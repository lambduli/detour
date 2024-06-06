module Check.Proof where


import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import Data.List qualified as List
import Data.Maybe ( mapMaybe, catMaybes )

-- import Control.Monad ( when, unless )
import Control.Monad.Reader ( ReaderT, asks, local )
import Control.Monad.State ( MonadState(get, put), gets )
import Control.Monad.Except ( Except, runExcept, throwError, catchError )
import Control.Monad.Extra

import Check.Error ( Error(..) )
import Check.Check
import Check.Assertion
import Check.Environment ( Environment(..) )
import Check.State ( State(..), Level(..) )
import Check.Substitute
import Check.Substitution hiding ( lookup )
import Check.Vars
import Check.Unify
import Check.Rule
import Check.Constraint
import Check.Solver ( Unifier(mgu), get'subst )
import Check.Substitution qualified as S
import Check.Types ( instantiate'scheme )

import Syntax.Formula ( Formula(Atom) )
import Syntax.Relation ( Relation(Meta'Rel), Prop'Var(..), Relation(..) )
import Syntax.Formula qualified as F
import Syntax.Term ( Term(..), Constant(..), Var(..), Free(..), Rigid(..), Bound(..) )
import Syntax.Theorem ( Theorem(..) )
import Syntax.Theorem qualified as T
import Syntax.Judgment ( Judgment(..) )
import Syntax.Judgment qualified as J
import Syntax.Jud qualified as Ju
import Syntax.Proof ( Proof(..) )
import Syntax.Proof qualified as P
import Syntax.Assumption ( Assumption(..) )
import Syntax.Justification ( Justification(..), Rule(..) )
import Syntax.Justification qualified as J
import Syntax.Claim ( Claim(..) )
import Syntax.Claim qualified as C
import Syntax.Type ( Type'Scheme(..), Type(..) )
import Syntax.Case ( Case(..) )
import Syntax.Syntax ( Syntax(..), Constructor(..) )


import Debug.Trace ( traceM )


check'proof :: Proof -> Check ()
check'proof Proof{ assumption = Universal binds , derivations } = do
  d <- asks depth

  rigid'depths <- gets rigid'depth'context
  free'depths <- gets free'depth'context

  let frees = concatMap collect'free'vars'in'judgment derivations

  let free'patch = Map.fromList $! map (\ f -> (f, d + 1)) frees
  let rigid'patch = Map.fromList $! map (\ (r, _) -> (r, d + 1)) binds

  let typing'patch = Map.fromList $! map (\ (R s, t) -> (s, t)) binds
  typing'patch' <- Map.fromList `fmap` mapM (\ (F s) -> do { t <- fresh'type ; return (s, Forall'T [] t) }) frees
  
  s <- get
  put s { rigid'depth'context = rigid'patch `Map.union` rigid'depths
        , free'depth'context = free'depths `Map.union` free'patch
        , typing'ctx = typing'ctx s `Map.union` typing'patch `Map.union` typing'patch' }

  local (\ e -> e { depth = d + 1 })
        (check'all derivations)

check'proof Proof{ assumption = Existential binding binds, derivations } = do
  d <- asks depth

  rigid'depths <- gets rigid'depth'context
  free'depths <- gets free'depth'context

  let frees = concatMap collect'free'vars'in'judgment derivations ++ collect'free'vars'in'binding binding

  let free'patch = Map.fromList $! map (\ f -> (f, d + 1)) frees
  let rigid'patch = Map.fromList $! map (\ (r, _) -> (r, d + 1)) binds
  
  let patch = case binding of
                (Just name, formula) ->
                  Map.singleton name (Assumed formula)
                (Nothing, _) ->
                  Map.empty
  let typing'patch = Map.fromList $! map (\ (R s, t) -> (s, t)) binds
  typing'patch' <- Map.fromList `fmap` mapM (\ (F s) -> do { t <- fresh'type ; return (s, Forall'T [] t) }) frees

  s <- get
  put s { rigid'depth'context = rigid'patch `Map.union` rigid'depths
        , free'depth'context = free'depths `Map.union` free'patch
        , typing'ctx = typing'ctx s `Map.union` typing'patch `Map.union` typing'patch' }

  local (\ e -> e { assert'scope = patch `Map.union` assert'scope e
                  , depth = d + 1 })
        (check'all derivations)

check'proof Proof{ assumption = Formula bindings, derivations } = do  
  d <- asks depth

  free'depths <- gets free'depth'context

  let frees = concatMap collect'free'vars'in'judgment derivations ++ concatMap collect'free'vars'in'binding bindings

  let free'patch = Map.fromList $! map (\ f -> (f, d + 1)) frees
  
  let assertions :: [(String, Assertion)]
      assertions  = mapMaybe to'assertion bindings

  let patch       = Map.fromList assertions

  typing'patch <- Map.fromList `fmap` mapM (\ (F s) -> do { t <- fresh'type ; return (s, Forall'T [] t) }) frees

  s <- get
  put s { free'depth'context = free'depths `Map.union` free'patch
        , typing'ctx = typing'ctx s `Map.union` typing'patch }

  local (\ e -> e { assert'scope = patch `Map.union` assert'scope e
                  , depth = d + 1 })
        (check'all derivations)

    where to'assertion :: (Maybe n, Formula) -> Maybe (n, Assertion)
          to'assertion (Nothing, _) = Nothing
          to'assertion (Just n, a) = Just (n, Assumed a)


last'derivation :: [Judgment] -> Check Judgment
last'derivation derivations = do
  case List.unsnoc derivations of
    Nothing -> do
      throwError $! Err ("Unexpected empty sub-proof.")
    Just (_, last) -> do
      return last


check'all :: [Judgment] -> Check ()
check'all [] = do
  throwError $! Err "Empty proofs are not allowed." -- Empty'Proof Nothing

check'all [judgment] = do
  check'judgment judgment

check'all (judgment : judgments) = do
  check'judgment judgment

  (in'scope'of judgment (check'all judgments))


in'scope'of :: Judgment -> Check a -> Check a
in'scope'of judgment@(Sub'Proof Proof{ P.name = Just name, assumption, derivations }) m = do
  last <- last'derivation derivations

  formula <-  case last of
                J.Claim C.Claim{ formula } -> do
                  return formula
                Sub'Proof _ -> do
                  throwError $! Err ("The last derivation must be a claim not a sub-proof.")
                Alias _ _ -> do
                  throwError $! Err ("The last derivation must be a claim not an alias.")
                Prove fm -> do
                  return fm

  scope <- asks assert'scope

  when (name `Map.member` scope) (throwError $! Err ("The name `" ++ name ++ "' is already used."))

  let der = Derived assumption formula
  local (\ e -> e{ assert'scope = Map.insert name der (assert'scope e) }) m

in'scope'of (Sub'Proof Proof{ P.name = Nothing }) m = do
  m

in'scope'of judgment@(J.Claim C.Claim{ C.name = Just name, formula }) m = do
  scope <- asks assert'scope

  when (name `Map.member` scope) (throwError $! Err ("The name `" ++ name ++ "' is already used."))

  let cl = Claimed formula
  local (\ e -> e{ assert'scope = Map.insert name cl (assert'scope e) }) m

in'scope'of (J.Claim C.Claim{ C.name = Nothing }) m = do
  m

in'scope'of (J.Alias _ _) m = do
  m

in'scope'of j@(J.Prove _) m = do
  check'judgment j
  m


check'judgment :: Judgment -> Check ()
check'judgment (Sub'Proof p@Proof{ P.name, assumption, derivations }) = do
  check'proof p

check'judgment (J.Claim c@C.Claim{ C.name, formula, justification }) = do
  let n = case name of
            Nothing -> "_"
            Just n -> n
  because ("I was checking a claim `" ++ n ++ "'") (justification `justifies` formula)

check'judgment (J.Alias name fm) = do
  collect (Atom (Meta'Rel (Prop'Var name)) :≡: fm)

check'judgment (J.Prove fm) = do
  proof'search fm




proves :: Formula -> Formula -> Check ()
proves fm'@F.True fm = fm' `unify` fm

proves fm'@F.False fm = fm' `unify` fm

proves fm'@(Atom _) fm = fm' `unify` fm

proves fm'@(F.Not _) fm = fm' `unify` fm

proves fm'@(F.And _ _) fm = fm' `unify` fm

proves fm'@(F.Or _ _) fm = fm' `unify` fm

proves fm'@(F.Impl _ _) fm = fm' `unify` fm

proves fm'@(F.Eq _ _) fm = fm' `unify` fm

proves fm'@(F.Forall _ _) fm@(F.Forall _ _) = fm' `unify` fm

proves fm'@(F.Forall (name, ts) body) fm = do
  -- instantiate the fm' and then call proves on it
  n <- fresh'name

  let t'patch = Map.singleton n ts
  d <- asks depth
  let d'patch = Map.singleton (F n) (d + 1)
  s <- get
  put s { typing'ctx = typing'ctx s `Map.union` t'patch
        , free'depth'context = free'depth'context s `Map.union` d'patch }

  let body' = apply (B name ==> Var (Free (F n))) body

  proves body' fm

proves fm'@(F.Exists _ _) fm@(F.Exists _ _)  = fm' `unify` fm

proves (F.Exists (name, ts) body) fm = do
  -- instantiate the fm' and then call proves on it
  n <- fresh'name

  let t'patch = Map.singleton n ts
  d <- asks depth
  let d'patch = Map.singleton (R n) (d + 1)
  s <- get
  put s { typing'ctx = typing'ctx s `Map.union` t'patch
        , rigid'depth'context = rigid'depth'context s `Map.union` d'patch }

  let body' = apply (B name ==> Var (Rigid (R n))) body

  proves body' fm


proof'search :: Formula -> Check ()
proof'search F.True = do
  return ()

proof'search F.False = do
  throwError $! Err "proof search for ⊥ not implemented yet"

proof'search (F.Atom (Meta'Rel _)) = do
  throwError $! Err "proof search for meta-relation variable is not a thing. This is probably an internal error."

proof'search fm@(F.Atom (Rel name terms)) = do
  --  I can search for a judgment that defines this name
  --    then I would try all of its constructors that would match this goal and see if at least one of them would justify this goal
  --  I can try theorems, see if I can instantiate any to justify this.
  --  I can search for an assertion that has been proved already to see if it justifies this goal.
  --    It might directly justify this one or it could be some universal that might be instantiable to justify it.

  --  I should probably priritize local assertions/judgments because one of them might be an induction hypothesis.
  --  Then I should look for theorems.
  --  Only then for constructors, I think.

  --  Actually, it might not matter. When doing induction, the local terms will be rigids, so they won't unify with any specific structure.
  --  So probably whatever.

  --  So let's start with the judgment.

  --  juds :: [ Jud String (String, [Type]) [Rule] ]
  juds <- gets judgments
  results <-  case List.find (\ (Ju.Jud _ _ (n, _) _) -> n == name) juds of
                Nothing -> do
                  --  no judgment for this goal
                  --  is that even ok?
                  throwError $! Err ("the goal `" ++ show fm ++ "' is formed by an unknown judgment.")

                Just (Ju.Jud _ _ _ rules) -> do
                  mapM concl'matches rules

  if not (any id results)
  then do
    --  get all the local asserts (for now only assertions)
    --  try to unify those formulae with the current goal

    assertions <- asks assert'scope
    let asserts = Map.assocs assertions

    result <- findM (\case  (_, Assumed fm') -> catchError (do { fm' `proves` fm ; return True }) (\ _ -> return False)
                            (_, Claimed fm') -> catchError (do { fm' `proves` fm ; return True }) (\ _ -> return False)
                            (_, Axiom fm') -> catchError (do { fm' `proves` fm ; return True }) (\ _ -> return False)
                            (_, Derived _ _) -> return False) asserts -- TODO: Actually, this could be useful. I might look up the scope and see if I can have what the derived needs if it proves what I need.

    case result of
      Nothing -> do
        --  keep searching maybe try some theorems now

        theors <- asks theorems
        -- traceM ("theorems available are " ++ List.intercalate "\n" (map show (Map.elems theors)))
        result <- findM (\ (_, T.Theorem{ T.name, prop'vars, assumptions, conclusion })
                          -> catchError (do
                                            old'new <- mapM (\ s -> do { n <- fresh'name ; return (s, n) } ) prop'vars
                                            let sub = concatMap (\ (o, n) -> Prop'Var o ==> Atom (Meta'Rel (Prop'Var n))) old'new

                                            let assumptions' = apply sub assumptions
                                            let conclusion' = apply sub conclusion
                                            List.foldr F.Impl conclusion' assumptions' `proves` fm
                                            return True) (\ _ -> return False)) (Map.assocs theors)

        case result of
          Nothing -> do
            throwError $! Err ("I didn't find any local assertion or theorems that would prove the goal `" ++ show fm ++ "'.")

          Just (n, t) -> do
            traceM ("\nI found a theorem `" ++ n ++ "' that justifies my goal `" ++ show fm ++ "'.")
            return ()

      Just (n, a) -> do
        traceM ("\nI found a local assertion `" ++ n ++ "' that justifies my goal `" ++ show fm ++ "'\nthe assertion was = `" ++ show a ++ "'.")
        return ()

  else do
    traceM ("I solved a goal `" ++ show fm ++ "' using some judgment rule.")
    return ()
          



  --  some of those matching rules might not have premises
  --  since they already matched, that would be success

  --  rules are      Rule String [(String, Type)] [Formula] Formula
  --  I don't care about the name : String
  --  the second argument, list of pairs is a list of parameters
  --  we I use that to instantiate those to fresh variables (register the types and such)
  --  I apply that instantiation to all the formulae
  --  I try to unify the conclusion with the goal
  --  if it doesn't fail, I get a substitution and apply it to all the formulae in the premise
  --  those are my new goals

  --  the above might succeed or fail
  --  I am not sure whether I need to try a different way if it succeeds
  --  if I were able to do interactions it would make sense
  
  --  it no rules match then I have a strange situation
  --  it should mean that the original goal I am trying is unprovable since there's no way to construct it

  --  if I find some rules but don't find a proof I might also try local assertions and theorems

  where concl'matches :: Ju.Rule -> Check Bool
        concl'matches (Ju.Rule _ prop'vars params premises conclusion) = do
          fresh'typed <- mapM (\ (n, t) -> do { fn <- fresh'name ; return (n, fn, t) }) params
          subst'1 <- concatMapM (\ (old, new, typ) -> do  { let ts = Forall'T [] typ
                                                          ; let t'patch = Map.singleton new ts
                                                          ; d <- asks depth
                                                          ; let d'patch = Map.singleton (F new) (d + 1)
                                                          ; s <- get
                                                          ; put s { typing'ctx = typing'ctx s `Map.union` t'patch
                                                                  , free'depth'context = free'depth'context s `Map.union` d'patch }
                                                          ; return (F old ==> Var (Free (F new))) }) fresh'typed
          subst'2 <- concatMapM (\ s -> do { p <- fresh'name ; return (Prop'Var s ==> Atom (Meta'Rel (Prop'Var p))) }) prop'vars
          let subst = subst'1 ++ subst'2
          let concl' = apply subst conclusion
          catchError  (do fm `unify` concl'
                          let premises' = apply subst premises
                          sub <- get'subst
                          let new'goals = apply sub premises'
                          mapM_ proof'search new'goals
                          return True)
                      (\ _ -> return False)


proof'search (F.Not fm) = do
  throwError $! Err "proof search for ¬ not implemented yet"

proof'search (F.And fm'a fm'b) = do
  proof'search fm'a
  proof'search fm'b

proof'search (F.Or fm'a fm'b) = do
  throwError $! Err "proof search for ∨ not implemented yet"

proof'search (F.Impl fm'a fm'b) = do
  throwError $! Err "proof search for ==> not implemented yet"

proof'search (F.Eq fm'a fm'b) = do
  throwError $! Err "proof search for <==> not implemented yet"

proof'search fm@(F.Exists (name, ts) body) = do
  traceM ("\n... My goal is `" ++ show fm ++ "'.")
  --  TODO: I should first see whether there's a local assertion or a theorem that would prove this goal.
  --        If not, I can attempt to search for a prove by instantiating and searching.
  assertions <- asks assert'scope
  traceM ("\n... my assertions are " ++ show assertions)
  let asserts = Map.assocs assertions

  result <- findM (\case  (_, Assumed fm') -> catchError (do { fm' `proves` fm ; return True }) (\ _ -> return False)
                          (_, Claimed fm') -> catchError (do { fm' `proves` fm ; return True }) (\ _ -> return False)
                          (_, Axiom fm') -> catchError (do { fm' `proves` fm ; return True }) (\ _ -> return False)
                          (_, Derived _ _) -> return False) asserts -- TODO: Actually, this could be useful. I might look up the scope and see if I can have what the derived needs if it proves what I need.

  case result of
    Nothing -> do
      --  keep searching maybe try some theorems now

      theors <- asks theorems
      -- traceM ("theorems available are " ++ List.intercalate "\n" (map show (Map.elems theors)))
      result <- findM (\ (_, T.Theorem{ T.name, assumptions, conclusion }) -> catchError (do { List.foldr F.Impl conclusion assumptions `proves` fm ; return True }) (\ _ -> return False)) (Map.assocs theors)

      case result of
        Nothing -> do
          f <- fresh'name
          let body' = apply (B name ==> Var (Free (F f))) body
          let t'patch = Map.singleton f ts
          d <- asks depth
          let d'patch = Map.singleton (F f) (d + 1)
          s <- get
          put s { typing'ctx = typing'ctx s `Map.union` t'patch
                , free'depth'context = free'depth'context s `Map.union` d'patch }

          traceM ("\n\n... I couldn't find a theorem or assertion so I am instantiating `" ++ show fm ++ "'\nmy current goal is `" ++ show body' ++ "'")
          proof'search body'
          -- throwError $! Err ("I didn't find any local assertion or theorems that would prove the goal `" ++ show fm ++ "'.")

        Just (n, t) -> do
          traceM ("\nI found a theorem `" ++ n ++ "' that justifies my goal `" ++ show fm ++ "'.")
          return ()

    Just (n, a) -> do
      traceM ("\nI found a local assertion `" ++ n ++ "' that justifies my goal `" ++ show fm ++ "'\nthe assertion was = `" ++ show a ++ "'.")
      return ()

proof'search fm@(F.Forall _ _) = do
  --  I need to take care of the generic
  --  I do that, for now, by case splitting
  --  I gather all the constructors for that type and make them into pattern
  --  that involves instantiating their parameters with fresh (typed) variables
  --  I then instantiate the formula per each constructor/pattern
  --  replacing the occurence of var for the corresponding term/pattern
  --  then I need to prove each one of those goals
  --  since I am using induction by default (explicitly)
  --  every case that might require it needs to be given an induction hypothesis
  --  so when we search for how to prove the current goal, we have three places to look at
  --    we look at judgments and their constructors, to see whether they can match the goal
  --    we look at theorems and see if we can ∀-eliminate them so that they can justify the goal
  --      TODO: what about existentials in theorems? how to deal with those?
  --    we look at proven assertions in the scope, those are things the user proved and induction hypotheses
  --
  --  when we find one or more ways to prove (or attempt to), we try those
  --  when we don't find any, we would initiate interaction with the user
  --  for now, we just print the goal and a little bit of context and fail the proof search

  (t, f, fm') <- case fm of
                  F.Forall (b, ts) fm -> do
                    t <- instantiate'scheme ts
                    f <- fresh'free
                    let fm' = apply [Bound'2'Term (B b) (Var (Free f))] fm

                    return (t, f, fm')

  n <-  case t of
          Type'Const n -> return n

          _ -> do
            throwError $! Err ("I can't prove the formula `" ++ show fm ++ "' by induction, its first binder has a confusing type `" ++ show t ++ "'.")


  syns <- gets syntax
  syn <- case lookup n syns of
          Nothing -> do
            throwError $! Err ("I can't prove the formula `" ++ show fm ++ "' by induction, I don't know the type of its first binder type `" ++ show t ++ "'.\nPerhaps you forgot to write a corresponding syntax section?")

          Just syn -> return syn

  let (Syntax constructors) = syn

  --  Now I need to take every constructor and instantiate it
  pats'cons <- mapM (\ c -> do  (rs, t) <- con'to'goal c
                                return (t, c, rs)) constructors

  let subs'cs = map (\ (t, c, rs) -> (f ==> t, c, rs)) pats'cons
  let goals'cs = map (\ (s, c, rs) -> (apply s fm', c, rs)) subs'cs

  mapM_ (search'case f t fm') goals'cs

  -- throwError $! Err ("Constructors = " ++ show constructors ++ "\nformula = " ++ show fm' ++ "\nterms = " ++ show pat'terms ++ "\ngoals = " ++ show goals)

  --  take it from here

  where search'case :: Free -> Type -> Formula -> (Formula, Constructor, [Rigid]) -> Check ()
        search'case f t fm' (goal, Constructor _ types, rs) = do
          let typed'rigids = filter (\ (_, typ) -> t == typ) (zip rs types)
          let hypotheses = map (\ (r, _) -> apply (f ==> (Var (Rigid r))) fm') typed'rigids

          let asserts = map Assumed hypotheses
          assert'patch <- mapM (\ as -> do { n <- fresh'name ; return (n, as) } ) asserts
          
          traceM ("\nthe goal is = " ++ show goal ++ "\ntype = " ++ show t ++ "\nrigids = " ++ show rs ++ "\nhypotheses = " ++ show hypotheses)

          local (\ e -> e { assert'scope = assert'scope e `Map.union` Map.fromList assert'patch })
                (proof'search goal)


con'to'goal :: Constructor -> Check ([Rigid], Term)
con'to'goal (Constructor c'name types) = do
  fresh'and'typed <- mapM (\ t -> fresh'name >>= \ n -> return (n, Forall'T [] t)) types

  let t'patch = Map.fromList fresh'and'typed
  

  d <- asks depth
  let d'patch = Map.fromList $! map (\ (n, _) -> (R n, d + 1)) fresh'and'typed

  s <- get
  put s { typing'ctx = typing'ctx s `Map.union` t'patch
        , rigid'depth'context = rigid'depth'context s `Map.union` d'patch }

  let rigids = map (\ (n, _) -> R n) fresh'and'typed
  let terms = map (\ r -> Var (Rigid r)) rigids

  return $! (rigids, App (C c'name) terms)


justifies :: Justification -> Formula -> Check ()
justifies Rule{ kind = rule, on = identifiers } fm = do
  assertions <- mapM id'to'assert identifiers --  TODO: id'to'assertions
  
  check'rule rule assertions fm

justifies (J.Theorem { J.name, on = identifiers }) fm = do
  T.Theorem { prop'vars, assumptions, conclusion, proof } <- look'up'theorem name

  --  I need to instantiate the prop'vars in all the assumptions and also the conclusion
  old'new <- mapM (\ s -> do { n <- fresh'name ; return (s, n) } ) prop'vars
  let sub = concatMap (\ (o, n) -> Prop'Var o ==> Atom (Meta'Rel (Prop'Var n))) old'new

  let assumptions' = apply sub assumptions
  let conclusion' = apply sub conclusion

  assertions <- mapM id'to'assert identifiers
  assertions `unify` assumptions'

  fm `unify` conclusion'

justifies Unproved _ = do
  return ()

justifies (Induction { proofs }) fm = do
  --  TODO:
  --  Proof by induction is like a proof by case analysis.
  --  But every case that has a part of it with the same type as the thing being matched on
  --  gets an induction hypothesis for that one part.
  --  The goal of each case is to prove the original statement instantiated with the specific case-term.

  (t, f, fm') <- case fm of
        F.Forall (b, ts) fm -> do
          t <- instantiate'scheme ts
          f <- fresh'free
          let fm' = apply [Bound'2'Term (B b) (Var (Free f))] fm

          return (t, f, fm')
        _ -> do
          throwError $! Err ("I can't prove the formula `" ++ show fm ++ "' by induction because it's not in the correct shape.")

  n <-  case t of
          Type'Const n -> return n

          _ -> do
            throwError $! Err ("I can't prove the formula `" ++ show fm ++ "' by induction, its first binder has a confusing type `" ++ show t ++ "'.")


  syns <- gets syntax
  syn <- case lookup n syns of
            Nothing -> do
              throwError $! Err ("I can't prove the formula `" ++ show fm ++ "' by induction, I don't know the type of its first binder type `" ++ show t ++ "'.\nPerhaps you forgot to write a corresponding syntax section?")

            Just syn -> return syn

  let (Syntax constructors) = syn


  --  For induction, we have to handle all the cases so that we "deserve" all the induction hypotheses.
  check'induction'cases proofs t constructors (f, fm')

  --  TODO: I need to figure out what (inductively defined) property
  --        is this reasoning about.
  --        Maybe like this:

  --        We have the formula, a bunch of base cases and a bunch of inductive cases.

  --        The formula the induction justifies looks something like this:
  --        ∀ x P[x]
  --        where P[x] is any formula where `x` is occuring.
  --
  --        The base cases look something like this:
  --        P[x -> α]
  --        where [x -> α] means that where above would be `x`, here it will be one of the
  --        non-inductive, base-case constants.
  --
  --        All the base cases should sort-of unify with the P[x] part if we consider `x`
  --        to be a unification variable.
  --        Example P[x] ≈ P[x -> Zero]
  --
  --        The inductive cases look something like this:
  --        ∀ y P[x -> y] ==> P[x -> ƒ(y)]
  --        where `ƒ` means some inductive-case function.
  --
  --
  --        From all this, it should be obvious which inductively-defined relation
  --        are we talking about.
  --        We should handle all the cases.
  --        They should preferably be in the correct order, but maybe I can deal
  --        with them being in any order.

justifies (Case'Analysis{ on'1, proofs }) fm = do
  --  TODO: I need to check that all the constructors of that type are covered by the case analysis.
  --        I need to check that each case is done correctly:
  --        We have three components.
  --            There's the local value we are doing case analysis on.
  --            There's the pattern.
  --            There's the corresponding constructor.
  --
  --        The pattern needs to be as general as possible.
  --        This means that each variable in the constructor needs to be paired up with a variable in the pattern.
  --        If the pattern has a non-variable at the place of an argument in the constructor the tool should complain about the pattern being "too specific".
  --
  --        The pattern also must not bind anything in the actual value being case-split.
  --        Like if we have `Suc(_n)` and a pattern `Suc(Zero)`.
  --        But that should not happen if the pattern must be as general as possible.

  --        Each case has a proof.
  --        Within that proof the variable being case-split on is unified with the pattern.
  --        I will do this by directly applying a corresponding substitution to it.
  --        This way I don't need to deal with un-unifying or anything like that.
  --
  --        The goal of the case analysis is known.
  --        I will take that goal, and for each case, I will apply that substitution to it too and then check that the last assertion in the proof is unifiable with it.

  t <- type'of on'1
  n <-  case t of
          Type'Const n -> return n

          _ -> do
            throwError $! Err ("I can't do case analysis on `" ++ show on'1 ++ "' it has a confusing type `" ++ show t ++ "'.")

  syns <- gets syntax
  syn <- case lookup n syns of
            Nothing -> do
              throwError $! Err ("I can't do case analysis on `" ++ show on'1 ++ "' I don't know its type `" ++ show t ++ "'.\nPerhaps you forgot to write a corresponding syntax section?")

            Just syn -> return syn

  let (Syntax constructors) = syn

  --  Now I need to iterate all the constructors and select those that should be handled.
  --  That should be done by checking whether a corresponding constructor (or a pattern created from it), would unify with the subject of the case analysis.
  --  If it would, we need to find a case that corresponds to it.
  --  That should be easy.
  --  Each pattern should be a constructor with a sequence of terms.
  --  There should be one case per each constructor.
  --  I can filter all the patterns that match the corresponding constructor and see that I have exactly one.
  --  The matching needs to take into account that the pattern must be the most general.
  --  

  --  The constradiction handling will then emerge naturally. No possible cases to handle -> goal accepted.

  check'cases proofs constructors fm on'1

justifies (Substitution{ on', using }) fm = do
  throwError $! Err "Proof by substitution is not implemented yet."
  --  using is a claim of equivalence (identifier that represents it, rather)
  --  on'    is a claim that proves something
  --  fm    and `on` can unify under the equivalence


check'induction'cases :: [Case] -> Type -> [Constructor] -> (Free, Formula) -> Check ()
check'induction'cases cases typ to'handle (f, goal) = do

  --  For each one of those, find all those cases that match them.
  --  If there are multiple -> fail
  --  If there is none -> fail

  -- traceM ("..........     I need to handle these constructors for the induction: " ++ show to'handle)

  handle'cases cases to'handle

  where handle'cases :: [Case] -> [Constructor] -> Check ()
        handle'cases [] [] = return ()
        handle'cases (Case p _ : _) [] = do
          throwError $! Err ("I found a redundant case in the case analysis.\nDrop the case for `" ++ show p ++ "'.")

        handle'cases cases (constr : constrs) = do
          --  find all the cases that match that constructor
          --  if there're more or less than one -> fail
          --  if there's exactly one -> continue
          (matching, not'matching) <- partitionM (`matches` constr) cases

          case matching of
            [] -> do
              throwError $! Err ("there's a case missing in the case analysis.\nI can't find a case for `" ++ show constr ++ "'.")

            (_ : _ : _) -> do
              throwError $! Err ("there are too many cases matching the constructor `" ++ show constr ++ "'.")

            [cas] -> do
              check'induction'case (f, goal) typ constr cas
              handle'cases not'matching constrs


check'induction'case :: (Free, Formula) -> Type -> Constructor -> Case -> Check ()
check'induction'case (f, goal) typ (Constructor _ types) (Case (c, rs) proof) = do
  --  I need to see if this case is for a base-case
  --  or for the inductive case.
  --  If the constructor contains another term of the same type, it is an inductive case.
  --  And we will make available a corresponding induction hypothesis.
  --  

  let pat'term = App c (map (\ r -> Var (Rigid r)) rs)

  --  if I were to unify the subject with the pat'term
  --  I would get a substitution
  --  I'd apply that substitution to the body of the case
  --  I also need to apply that substitution to the goal

  check'proof proof

  let goal' = apply [Free'2'Term f pat'term] goal

  let Proof{ assumption, derivations } = proof

  case assumption of
    Formula [] -> return ()
    Formula ind'hypotheses -> do
      let typed'rigids = filter (\ (_, t) -> t == typ) (zip rs types)
      let hypotheses = map (\ (r, _) -> apply (f ==> (Var (Rigid r))) goal) typed'rigids
      let ind'hypotheses' = map snd ind'hypotheses

      ind'hypotheses' `unify` hypotheses

    _ -> do
      throwError $! Err "the induction cases are not supposed to have quantified assumptions."
    

  case List.unsnoc derivations of
    Just (_, J.Claim (C.Claim { formula })) -> do
      formula `unify` goal'

    Just (_, _) -> do
      throwError $! Err ("I found a wrong-shaped conclusion in the body of the case.")

    Nothing -> do
      throwError $! Err "Missing conclusion."


check'cases :: [Case] -> [Constructor] -> Formula -> Term -> Check ()
check'cases cases constructors formula subject = do

  --  First filter the constructors.
  --  Find all those that are "unifiable" with the subject
  to'handle <- filterM (\ constr -> con'to'pat constr >>= (`unifiable` subject)) constructors

  --  For each one of those, find all those cases that match them.
  --  If there are multiple -> fail
  --  If there is none -> fail

  -- traceM ("..........     I need to handle these constructors: " ++ show to'handle)

  handle'cases cases to'handle

  where handle'cases :: [Case] -> [Constructor] -> Check ()
        handle'cases [] [] = return ()
        handle'cases (Case p _ : _) [] = do
          throwError $! Err ("I found a redundant case in the case analysis.\nDrop the case for `" ++ show p ++ "'.")

        handle'cases cases (constr : constrs) = do
          --  find all the cases that match that constructor
          --  if there're more or less than one -> fail
          --  if there's exactly one -> continue
          (matching, not'matching) <- partitionM (`matches` constr) cases

          case matching of
            [] -> do
              throwError $! Err ("there's a case missing in the case analysis.\nI can't find a case for `" ++ show constr ++ "'.")

            (_ : _ : _) -> do
              throwError $! Err ("there are too many cases matching the constructor `" ++ show constr ++ "'.")

            [cas] -> do
              check'case formula subject constr cas
              handle'cases not'matching constrs


matches :: Case -> Constructor -> Check Bool
matches (Case (con, rigids) _) constr = do
  --  the case's pattern must be the most general possible
  --  the variables in the case are rigid variables
  --  because it must not be unified with anything
  --  this way, I don't need to _CHECK_ that it is the most general in a complicated way
  --  I just check that all the rigid variables are unique
  --  or I can assume that the renamer will handle this

  --  TODO: make sure that the renamer handles checking that all the rigid variables are unique.

  --  I need to make sure that those rigid variables are correctly typed in the typing context.
  --  For that, I assign each one of them a fresh type variable and let the unification with the constructor pattern/term do its job.

  d <- asks depth
  let d'maps = map (\ r -> (r, d + 1)) rigids

  let pat'term = App con (map (\ r -> Var (Rigid r)) rigids)

  term <- con'to'pat constr

  mappings <- mapM (\ (R s) -> do { t <- fresh'type ; return (s, Forall'T [] t)  }) rigids

  s <- get
  put s { typing'ctx = typing'ctx s `Map.union` Map.fromList mappings
        , rigid'depth'context = rigid'depth'context s `Map.union` Map.fromList d'maps }

  -- traceM ("`~~~~~~~~~~~~~ I need to unify " ++ show term ++ "\nwith " ++ show pat'term)

  ifM (term `unifiable` pat'term)
      do { pat'term `unify` term ; return True }
      (return False)


con'to'pat :: Constructor -> Check Term
con'to'pat (Constructor c'name types) = do
  fresh'and'typed <- mapM (\ t -> fresh'name >>= \ n -> return (n, Forall'T [] t)) types

  let t'patch = Map.fromList fresh'and'typed
  

  d <- asks depth
  let d'patch = Map.fromList $! map (\ (n, _) -> (F n, d + 1)) fresh'and'typed

  s <- get
  put s { typing'ctx = typing'ctx s `Map.union` t'patch
        , free'depth'context = free'depth'context s `Map.union` d'patch }

  -- traceM ("--------- I have recorded these mappings in the typing context: " ++ show t'patch)

  let terms = map (\ (n, _) -> Var (Free (F n))) fresh'and'typed

  return $! App (C c'name) terms


unifiable :: Term -> Term -> Check Bool
unifiable left right = do
  subst <- get'subst
  tc <- gets typing'ctx
  -- traceM ("unifiable and the typing context is = " ++ show tc)
  b <- do { _ <- apply subst left `match'mgu` apply subst right ; return True } `catchError` (const (return False))
  -- traceM ("_____________\nunifiable\nis " ++ show (apply subst left) ++ "\nunifiable with " ++ show (apply subst right) ++ "\nconclusion= " ++ show b)
  return b



check'case :: Formula -> Term -> Constructor -> Case -> Check ()
check'case goal subject constructor (Case (c, rs) proof) = do

  let pat'term = App c (map (\ r -> Var (Rigid r)) rs)

  --  if I were to unify the subject with the pat'term
  --  I would get a substitution
  --  I'd apply that substitution to the body of the case
  --  I also need to apply that substitution to the goal
  --  

  subst <- get'subst
  s' <- apply subst pat'term `match'mgu` apply subst subject
  let s = subst `compose` s'

  -- traceM ("............... the substitution = " ++ show s)
  -- traceM ("I need to check the proof = " ++ show (apply s proof))
  -- traceM ("the old proof was = " ++ show proof)
  -- traceM ("...___... the term under rigid b = " ++ show (S.lookup (R "b") s) )
  -- let what = C.Claim{ C.name = Just "claim-name"
  --                   , formula = (Atom (Rel "whatever" [(Var (Rigid (R "b")))]))
  --                   , justification = Unproved }
  -- let what2 = Proof{ P.name = Just "proof-name"
  --                 , assumption = Formula []
  --                 , derivations = [J.Claim what] }
  -- traceM ("--···--  what happens = " ++ show (apply s what2))
  check'proof (apply s proof)

  -- traceM "proof checked"

  let goal' = apply s goal

  let Proof{ assumption, derivations } = apply s proof

  case assumption of
    Formula [] -> return ()
    _ -> do
      throwError $! Err "the cases are not supposed to have assumptions."
    

  case List.unsnoc derivations of
    Just (_, J.Claim (C.Claim { formula })) -> do
      -- traceM ("so I am here, finally\nunifying a formula " ++ show formula ++ "\nwith goal " ++ show goal')
      formula `unify` goal'

    Just (_, _) -> do
      throwError $! Err ("I found a wrong-shaped conclusion in the body of the case.")

    Nothing -> do
      throwError $! Err "Missing conclusion."


match'mgu :: Term -> Term -> Check Substitution
match'mgu p (Var (Rigid (R s))) = return [Rigid'2'Term (R s) p]
match'mgu p t = p `mgu` t --  TODO: this is obviously terrible idea, but might work for now


id'to'assert :: String -> Check Assertion
id'to'assert identifier = do
  scope <- asks assert'scope
  case Map.lookup identifier scope of
    Nothing -> do
      throwError $! Err ("Unknown identifier `" ++ identifier ++ "'.")
    Just assert -> do
      return assert


-- are'compatible'with :: [String] -> [Formula] -> Check ()
-- are'compatible'with identifiers formulae = do
--   assertions <- mapM id'to'assert identifiers
--   assertions `unify` formulae


-- is'compatible'with :: Formula -> Formula -> Check ()
-- is'compatible'with fm fm' = do
--   fm `unify` fm'


collect'free'vars'in'judgment :: Judgment -> [Free]
collect'free'vars'in'judgment (Sub'Proof _) = []
collect'free'vars'in'judgment (J.Claim claim) = Set.toList $! free claim
collect'free'vars'in'judgment (Alias _ _) = []
collect'free'vars'in'judgment (Prove fm) = Set.toList $! free fm


collect'free'vars'in'binding :: (Maybe a, Formula) -> [Free]
collect'free'vars'in'binding (_, f) = collect'free'vars'in'formula f


collect'free'vars'in'formula :: Formula -> [Free]
collect'free'vars'in'formula fm = Set.toList $! free fm

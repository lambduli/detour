module Check.Proof where


import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import Data.List qualified as List
import Data.Maybe ( mapMaybe )

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

import Syntax.Formula ( Formula(Atom) )
import Syntax.Relation ( Relation(Meta'Rel), Prop'Var(..), Relation(..) )
import Syntax.Formula qualified as F
import Syntax.Term ( Term(..), Constant(..), Var(..), Free(..), Rigid(..) )
import Syntax.Theorem ( Theorem(..) )
import Syntax.Theorem qualified as T
import Syntax.Judgment ( Judgment(..) )
import Syntax.Judgment qualified as J
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


justifies :: Justification -> Formula -> Check ()
justifies Rule{ kind = rule, on = identifiers } fm = do
  assertions <- mapM id'to'assert identifiers --  TODO: id'to'assertions
  
  check'rule rule assertions fm

justifies (J.Theorem { J.name, on = identifiers }) fm = do
  T.Theorem { assumptions, conclusion, proof } <- look'up'theorem name

  assertions <- mapM id'to'assert identifiers
  assertions `unify` assumptions

  fm `unify` conclusion

justifies Unproved _ = do
  return ()

justifies (Induction { on'1 }) fm = do
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

  throwError $! Err "Proof by induction is not implemented yet."

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


check'cases :: [Case] -> [Constructor] -> Formula -> Term -> Check ()
check'cases cases constructors formula subject = do

  --  First filter the constructors.
  --  Find all those that are "unifiable" with the subject

  to'handle <- filterM (\ constr -> con'to'pat constr >>= (`unifiable` subject)) constructors

  --  For each one of those, find all those cases that match them.
  --  If there are multiple -> fail
  --  If there is none -> fail

  traceM ("..........     I need to handle these constructors: " ++ show to'handle)

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

  traceM ("`~~~~~~~~~~~~~ I need to unify " ++ show term ++ "\nwith " ++ show pat'term)

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

  traceM ("--------- I have recorded these mappings in the typing context: " ++ show t'patch)

  let terms = map (\ (n, _) -> Var (Free (F n))) fresh'and'typed

  return $! App (C c'name) terms


unifiable :: Term -> Term -> Check Bool
unifiable left right = do
  subst <- get'subst
  tc <- gets typing'ctx
  traceM ("unifiable and the typing context is = " ++ show tc)
  b <- do { _ <- apply subst left `match'mgu` apply subst right ; return True } `catchError` (\ err -> do { traceM ("+++++++ the reason why it fails is " ++ show err) ; (return False) })
  traceM ("_____________\nunifiable\nis " ++ show (apply subst left) ++ "\nunifiable with " ++ show (apply subst right) ++ "\nconclusion= " ++ show b)
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

  traceM ("............... the substitution = " ++ show s)
  traceM ("I need to check the proof = " ++ show (apply s proof))
  traceM ("the old proof was = " ++ show proof)
  traceM ("...___... the term under rigid b = " ++ show (S.lookup (R "b") s) )
  let what = C.Claim{ C.name = Just "claim-name"
                    , formula = (Atom (Rel "whatever" [(Var (Rigid (R "b")))]))
                    , justification = Unproved }
  let what2 = Proof{ P.name = Just "proof-name"
                  , assumption = Formula []
                  , derivations = [J.Claim what] }
  traceM ("--···--  what happens = " ++ show (apply s what2))
  check'proof (apply s proof)

  traceM "proof checked"

  let goal' = apply s goal

  let Proof{ assumption, derivations } = apply s proof

  case assumption of
    Formula [] -> return ()
    _ -> do
      throwError $! Err "the cases are not supposed to have assumptions."
    

  case List.unsnoc derivations of
    Just (_, J.Claim (C.Claim { formula })) -> do
      traceM ("so I am here, finally\nunifying a formula " ++ show formula ++ "\nwith goal " ++ show goal')
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


collect'free'vars'in'binding :: (Maybe a, Formula) -> [Free]
collect'free'vars'in'binding (_, f) = collect'free'vars'in'formula f


collect'free'vars'in'formula :: Formula -> [Free]
collect'free'vars'in'formula fm = Set.toList $! free fm

module Check.Proof where


import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import Data.List qualified as List
import Data.Maybe ( mapMaybe )

-- import Control.Monad ( when, unless )
import Control.Monad.Reader ( ReaderT, asks, local )
import Control.Monad.State ( MonadState(get, put), gets )
import Control.Monad.Except ( Except, runExcept, throwError )
import Control.Monad.Extra

import Check.Error ( Error(..) )
import Check.Check
import Check.Assertion
import Check.Environment ( Environment(..) )
import Check.State ( State(..), Level(..) )
import Check.Substitute
import Check.Vars
import Check.Unify
import Check.Rule

import Syntax.Formula ( Formula(..) )
import Syntax.Formula qualified as F
import Syntax.Term ( Term(..), Constant, Free )
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


check'proof :: Proof -> Check ()
check'proof Proof{ assumption = Universal binds , derivations } = do
  d <- asks depth

  let cs = map fst binds

  const'depths <- gets const'depth'context
  free'depths <- gets free'depth'context

  let frees = concatMap collect'free'vars'in'judgment derivations
  let consts = concatMap collect'consts'in'judgment derivations

  let free'patch = Map.fromList $! map (\ f -> (f, d + 1)) frees
  let const'patch = Map.fromList $! map (\ c -> (c, Unrestricted (d + 1))) consts
  let const'patch'r = Map.fromList $! map (\ c -> (c, Restricted (d + 1))) cs
  
  s <- get
  put s { const'depth'context = const'depths `Map.union` const'patch `Map.union` const'patch'r
        , free'depth'context = free'depths `Map.union` free'patch }

  local (\ e -> e { depth = d + 1 })
        (check'all derivations)

--  NOTE: I am considering not relying on the parser to parse all the constants within the body of the proof as constants.
--        I could easily do that here. I would create a substitution from free-vars with the names of the constants to those constants.
--        I would apply this substitution to all the derivations and ALSO the formula.
--        This would make the parsing a bit easier.
--        I don't know it something like this can be done everywhere. Maybe it can.
check'proof Proof{ assumption = Existential binding cs, derivations } = do
  d <- asks depth

  const'depths <- gets const'depth'context
  free'depths <- gets free'depth'context

  let frees = concatMap collect'free'vars'in'judgment derivations ++ collect'free'vars'in'binding binding
  let consts = concatMap collect'consts'in'judgment derivations ++ collect'consts'in'binding binding

  let free'patch = Map.fromList $! map (\ f -> (f, d + 1)) frees
  let const'patch = Map.fromList $! map (\ c -> (c, Unrestricted (d + 1))) consts
  let const'patch'r = Map.fromList $! map (\ (c, _) -> (c, Unrestricted (d + 1))) cs
  
  let patch = case binding of
                (Just name, formula) ->
                  Map.singleton name (Assumed formula)
                (Nothing, _) ->
                  Map.empty

  s <- get
  put s { const'depth'context = const'depths `Map.union` const'patch `Map.union` const'patch'r
        , free'depth'context = free'depths `Map.union` free'patch }

  local (\ e -> e { assert'scope = assert'scope e `Map.union` patch
                  , depth = d + 1 })
        (check'all derivations)

check'proof Proof{ assumption = Formula bindings, derivations } = do  
  d <- asks depth

  const'depths <- gets const'depth'context
  free'depths <- gets free'depth'context

  let frees = concatMap collect'free'vars'in'judgment derivations ++ concatMap collect'free'vars'in'binding bindings
  let consts = concatMap collect'consts'in'judgment derivations ++ concatMap collect'consts'in'binding bindings

  let free'patch = Map.fromList $! map (\ f -> (f, d + 1)) frees
  let const'patch = Map.fromList $! map (\ c -> (c, Unrestricted (d + 1))) consts
  
  let assertions :: [(String, Assertion)]
      assertions  = mapMaybe to'assertion bindings

  let patch       = Map.fromList assertions

  s <- get
  put s { const'depth'context = const'depths `Map.union` const'patch
        , free'depth'context = free'depths `Map.union` free'patch }

  local (\ e -> e { assert'scope = assert'scope e `Map.union` patch
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


check'judgment :: Judgment -> Check ()
check'judgment (Sub'Proof p@Proof{ P.name, assumption, derivations }) = do
  check'proof p

check'judgment (J.Claim c@C.Claim{ C.name, formula, justification }) = do
  let n = case name of
            Nothing -> "_"
            Just n -> n
  because ("I was checking a claim `" ++ n ++ "'") (justification `justifies` formula)


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

justifies (Induction { on = identifiers }) fm = do
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

justifies (Substitution{ on', using }) fm = do
  throwError $! Err "Proof by substitution is not implemented yet."
  --  using is a claim of equivalence (identifier that represents it, rather)
  --  on'    is a claim that proves something
  --  fm    and `on` can unify under the equivalence


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


collect'consts'in'judgment :: Judgment -> [Constant]
collect'consts'in'judgment (Sub'Proof _) = []
collect'consts'in'judgment (J.Claim claim) = Set.toList $! free claim


collect'free'vars'in'binding :: (Maybe a, Formula) -> [Free]
collect'free'vars'in'binding (_, f) = collect'free'vars'in'formula f


collect'consts'in'binding :: (Maybe a, Formula) -> [Constant]
collect'consts'in'binding (_, f) = collect'consts'in'formula f


collect'free'vars'in'formula :: Formula -> [Free]
collect'free'vars'in'formula fm = Set.toList $! free fm


collect'consts'in'formula :: Formula -> [Constant]
collect'consts'in'formula fm = Set.toList $! free fm

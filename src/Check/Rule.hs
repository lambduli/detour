module Check.Rule where

-- import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import Data.List qualified as List
import Data.Maybe ( isJust )

-- import Control.Monad ( when, unless )
import Control.Monad.Reader ( ask, asks, local )
import Control.Monad.State ( MonadState(get, put), gets )
import Control.Monad.Except ( throwError, catchError )
import Control.Monad.Extra ( unless )

import Check.Error ( Error(..) )
import Check.Check
import Check.Assertion ( Assertion(..), asserts'formula )
import Check.Environment ( Environment(..) )
import Check.State ( State(..), Level(..) )
import Check.Substitute ( Substitute(apply) )
-- import Check.Free
import Check.Unify ( Unify(unify) )
import Check.Substitution
import Check.Solver ( solve, get'subst )
import Check.Types ( instantiate'scheme, instantiate'scheme'at )

import Syntax.Formula ( Formula(..) )
import Syntax.Formula qualified as F
import Syntax.Relation ( Relation(..), Prop'Var(..) )
import Syntax.Term ( Term(..), Var(..), Constant(..), Free(..), Bound(..), Rigid(..) )
import Syntax.Type ( Type, Type'Scheme(..) )
-- import Syntax.Theorem ( Theorem(..) )
-- import Syntax.Theorem qualified as T
-- import Syntax.Judgment ( Judgment(..) )
-- import Syntax.Judgment qualified as J
-- import Syntax.Proof ( Proof(..) )
-- import Syntax.Proof qualified as P
import Syntax.Assumption ( Assumption(..) )
import Syntax.Justification ( Justification(..), Rule(..) )
import Syntax.Jud qualified as J
-- import Syntax.Justification qualified as J
-- import Syntax.Claim ( Claim(..) )
-- import Syntax.Claim qualified as C


check'rule :: Rule -> [Assertion] -> Formula -> Check ()
{-  d : | p1 : _A
        | p2 : _B
        |-------------------
        | last : _C  by ...

     impl : _A ==> _B ==> _C  by rule ==>-intro on d   -}
check'rule Impl'Intro [assertion] impl = check'impl'intro assertion impl

check'rule Impl'Intro _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ==>-intro."

{-  impl : _A ==> _B => _C  by ...

    prem1 : _A  by ...
    prem2 : _B  by ...

    concl : _B  by rule ==>-elim on impl, prem1, prem2         -}
check'rule Impl'Elim (assert'impl : assert'prems) conclusion = do
  impl <- asserts'formula assert'impl --  TODO: the withError' trick

  prems <- mapM asserts'formula assert'prems --  TODO: the withError' trick

  let meta'impl = foldr Impl conclusion prems

  because ("I was trying to check the rule ==>-elim to justify `" ++ show conclusion ++ "'\n  the implication to eliminate `" ++ show impl ++ "'\n  and the proved premises " ++ List.intercalate ", " (map (\ p -> "`" ++ show p ++ "'") prems)) (impl `unify` meta'impl)

check'rule Impl'Elim _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ==>-elim."

{-  a : _A  by ...

    b : _B  by ...

    a∧b : _A ∧ _B  by rule ∧-intro on a, b      -}
check'rule Conj'Intro [assert'a, assert'b] conj = do
  a <- asserts'formula assert'a
  b <- asserts'formula assert'b

  because ("I was trying to check the rule ∧-intro") (conj `unify` (a `And` b))

check'rule Conj'Intro _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ∧-intro."

{-  a∧b : _A ∧ _B  by ...

    formula : _A  by rule ∧-elim on a∧b

    --  or

    formula : _B  by rule ∧-elim on a∧b           -}
check'rule Conj'Elim [assertion] formula = do
  a'and'b <- asserts'formula assertion
  
  a <- fresh'proposition
  b <- fresh'proposition

  a'and'b `unify` (a `And` b)

  
  because ("I was trying to check the rule ∧-elim")
          (catchError  do { formula `unify` a ; solve }
                      (const (formula `unify` b)))

check'rule Conj'Elim _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ∧-elim."

{-  a : _A  by ...

    b : _B  by ...

    disj : _A ∨ _B  by rule ∨-intro on a
    
    --  or
    disj : _A ∨ _B  by rule ∨-intro on b  -}
check'rule Disj'Intro [assertion] disj = do
  f <- asserts'formula assertion

  a <- fresh'proposition
  b <- fresh'proposition

  because ("I was trying to check the rule ∨-intro and it seems that the formula is not even a disjunction.") (disj `unify` (a `Or` b))

  because ("I was trying to check the rule ∨-intro")
          (catchError  do { f `unify` a ; solve }
                      (const (f `unify` b)))

check'rule Disj'Intro _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ∨-intro."

{-  a∨b : _A ∨ _B  by ...
    
    if-a :  | p : _A
            |-------------
            | goal-a : φ

    if-b :  | p : _B
            |-------------
            | goal-a : φ'
    
    formula : φ  by rule ∨-elim on a∨b, if-a, if-b                    -}
check'rule Disj'Elim  [ assertion
                      , Derived (Formula [(_, a)]) goal'a
                      , Derived (Formula [(_, b)]) goal'b ] formula = do
  disj <- asserts'formula assertion

  because ("I was trying to check the rule ∨-elim and it seems that the formula is not even a disjunction.") (disj `unify` (a `Or` b))

  because ("I was trying to check the rule ∨-elim and it seems that those two sub-proofs don't have the same goal.") (goal'a `unify` goal'b)
  because ("I was trying to check the rule ∨-elim and it seems that the formula is not the same as the goals of those sub-proofs.") (formula `unify` goal'a)

check'rule Disj'Elim  _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ∨-elim."

{-  a : _A  by ...

    not-a : ¬_A  by ...

    false : ⊥  by rule ⊥-elim on a, not-a

    --  or

    false : ⊥  by rule ⊥-elim on a, not-a           -}
check'rule Neg'Elim [assert'a, assert'a'] F.False = do
  a <- asserts'formula assert'a
  a' <- asserts'formula assert'a'

  because ("I was trying to check the rule ¬-elim.")
          (catchError do { Not a `unify` a' ; solve }
                      (const (a `unify` (Not a'))))

check'rule Neg'Elim _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ¬-elim."

{-  a=>b : _A ==> _B  by ...
    b=>a : _B ==> _A  by ...

    formula : _A <==> _B  by rule <==>-intro on a=>b, b=>a
    --  or
    formula : _B <==> _A  by rule <==>-intro on a=>b, b=>a    -}
check'rule Equiv'Intro [assert'ab, assert'ba] formula = do
  ab <- asserts'formula assert'ab
  ba <- asserts'formula assert'ba

  a <- fresh'proposition
  b <- fresh'proposition

  because ("I was trying to check the rule <==>-intro and it seems that the first argument is not even a concjunction.")
          (ab `unify` (a `Impl` b))
  because ("I was trying to check the rule <==>-intro and it seems that the second argument is not even a concjunction.")
          (ba `unify` (b `Impl` a))

  --  The equivalence is in one of two possible directions.

  because ("I was trying to check the rule <==>-intro and it seems that the formula is not correct equivalence.")
          (catchError do { formula `unify` (a `Eq` b) ; solve }
                      (const (formula `unify` (b `Eq` a))))

check'rule Equiv'Intro _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule <==>-intro."

{-  formula : _A <==> _B  by rule <==>-intro on a=>b, b=>a
    --  or
    formula : _B <==> _A  by rule <==>-intro on a=>b, b=>a
    
    impl : _A ==> _B  by rule <==>-elim on formula
    
        -}
check'rule Equiv'Elim [assertion] impl = do
  eq <- asserts'formula assertion

  --  Either  a <==> b justifies a ==> b
  --  or      a <==> b justifies b ==> a

  a <- fresh'proposition
  b <- fresh'proposition

  because ("I was trying to check the rule <==>-elim.") (eq `unify` (a `Eq` b))

  because ("I was trying to check the rule <==>-elim.")
          (catchError do { impl `unify` (a `Impl` b) ; solve }
                      (const (impl `unify` (b `Impl` a))))

check'rule Equiv'Elim _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule <==>-elim."

{-  true : ⊤  by rule ⊤-intro     -}
check'rule True'Intro [] F.True = do
  return ()

check'rule True'Intro _ F.True = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ⊤-intro."

{-  false : | prem : ¬φ
            |-------------------
            | last : ⊥  by ...

    formula : φ  by rule contradiction on false   -}
check'rule Proof'By'Contradiction [Derived (Formula [(_, Not a)]) last] formula = do
  lem <- asks lem

  if lem
  then do
    throwError (Err "Proof by contradiction is disallowed.")

  else do
    because ("I was trying to check the proof by contradiction and it seems that the goal is not even a ⊥.")
            (F.False `unify` last)
    because ("I was trying to check the proof by contradiction and it seems that the formula is not a negation of the assumption.")
            (a `unify` formula)

check'rule Proof'By'Contradiction _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule `contradiction'."

{-  false : ⊥  by ...

    _ : _A  by rule ⊥-elim on false   -}
check'rule Contra'Elim [assertion] _ = do
  false <- asserts'formula assertion
  
  because ("I was trying to check the rule ⊥-elim.") (false `unify` F.False)

check'rule Contra'Elim _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ⊥-elim."

{-  α : | for all (α : ℕ) , β
        |----------------------
        |
        | formula : P(α, x, β)  by ...   -- where x is something from the outer scope

    universal : ∀ a ∀ b P(a, x, b)  by ∀-intro on α                    -}

{-  What if we don't know the actual formula or even the universal?

    α : | for all α, β
        |----------------------
        |
        | formula : _  by ...

    universal : _  by ∀-intro on α                    -}
--  TODO: I am not going to deal with this now, but when I have it working
--        I want to experiment a bit and see what can I do about it.
check'rule Forall'Intro [Derived (Universal bindings) formula] universal = do
  -- --  There's no guarantee that formula will be "complete".
  -- --  For that reason, I shouldn't apply any substitution to it or do anything with it.
  -- --  Neither universal has to be "complete".
  -- --  My solution is to produce another kind of Constraint stating that:
  -- --    formula is an instance of the universal in the context of all of the `vars` as constants/bound variables.

  -- -- collect (Instantiation'Under universal formula vars)


  -- let subst       = map (\ c@(C n) -> Const'2'Term c (Bound (B n))) vars
  --     --  TODO: What if the formula contains free variables that have been unified with some
  --     --        of those constants (universals)?
  --     --        The following substitution will ignore that.
  --     --        So when we unify the formula' (inside of universal') with universal
  --     --        the Bounds in the universal will try to unify with those free-vars
  --     --        that are actually constants. This will lead to an unification error.
  --     --        I suppose this mistake would not lead to constants escaping because of levels.
  --     --        So how to fix this?
  --     --        Can I apply the same substitution to all the constraints?
  --     --        All the universal constants would become Bounds.
  --     --        Maybe I could.

  --     --        Is there maybe a better, simpler way to check the ∀-intro?
  --     formula'    = apply subst formula  --  formula with all the universals as Bounds
  --     --  ^^^ The issue is that if the formula is `_` this substitution does nothing.
  --     --      
  --     prefix      = map (\ (C n) -> n) vars
  --     universal'  = foldr Forall formula' prefix

  -- --  To fix the bug mentioned above.
  -- -- constrs <- gets term'constraints
  -- -- s <- get
  -- -- put s{ term'constraints = apply subst constrs }

  -- because ("I was trying to check the rule ∀-intro\n\n  the claimed formula `" ++ show universal ++ "'\n\n  the justification produced `" ++ show universal' ++ "'\n\n  because it started from `" ++ show formula ++ "'\n\n  and applied this substitution `" ++ show subst ++ "'.") (universal `unify` universal')

  body <- instantiate universal bindings
  because ("I was trying to check the rule ∀-intro |\n  body " ++ show body ++ "\n\n  formula " ++ show formula ++ "\n\n  universal " ++ show universal)
          (body `unify` formula)

  {-
    THIS IS INCORRECT:
    and it should be rejected
  
    uni : | for all α, β
          |--------------------
          |
          | formula : P(α, β, β)  by ...

    universal : ∀ a ∀ b ∀ c P(a, b, c)  by ∀-intro on uni
  -}

check'rule Forall'Intro _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ∀-intro."

{-  universal : ∀ α ∀ β P(α, β, x)  by ...

    formula : ∀ β P(a, β, x)  by ∀-elim on universal    -}
--  This one can introduce implicit universal variables.
--  Those are represented as free-variables.

--  It could happen that we don't have universal or even formula.
{-  universal : _  by ...

    --  but we should be able to infer the universal from the rest of the proof

    formula : _ by ∀-elim on universal

    --  and from that, we could get the formula too, I think.

    --  So it might be enough to just apply the current substitution to make sure
    --  that we have as specific formulae as possible.
                                              -}
check'rule Forall'Elim [assertion] formula = do
  --  universal <- asserts'formula assertion

  --  collect (formula `Instance'of` universal)
  
  --  Because universal and even formula could be unspecified,
  --  we just produce another kind of constraint saying that
  --      formula is an instance of universal. There's no telling of how many
  --      ∀ variables have been instantiated 
  
  
  universal <- asserts'formula assertion

  universal `unify'with'instance` formula

check'rule Forall'Elim _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ∀-elim."

{-  formula : P(α, β, x)  by ...

    existential : _  by ∃-intro on p
    --  or
    existential : P  by ∃-intro on p                    -}

{-  formula : P(α, β, x, α)  by ...

    existential : ∃ a ∃ b P(a, b, x, α)  by ∃-intro on formula  -}
check'rule Exists'Introduction [assertion] existential = do
  formula <- asserts'formula assertion

  because ("I was trying to check rule ∃-intro justifying `" ++ show existential ++ "'")
          (existential `unify'with'instance` formula)

check'rule Exists'Introduction _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ∃-intro."

{-  existential : ∃ x P(x, dᶜ, x)  by ...

    el :  | premise : P(α, f, g)  for some α
          |-----------------------------------
          |
          | last : φ  by ...

    formula : φ  by ∃-elim existential, el
-}
check'rule Exists'Elimination [assertion, Derived (Existential (_, premise) bindings) last] formula = do
  existential <- asserts'formula assertion

  assum <- instantiate existential bindings
  because ("I was trying to check the rule ∃-elim.")
          (assum `unify` premise)

  because ("I was trying to check the rule ∃-elim.")
          (last `unify` formula)
  --  Unification has built-in support for escape-checking, so this is a good choice.

  {-
    uni : ∀ o ∀ p G(o, p)  by ...
    
    implicits : G(m, n)  by ∀-elim on uni   --  here, m and n are implicitly introduced free-variables
    
    existential : ∃ x ∃ y P(x, y, u, u')    --  where u and u' are implicitly introduced free-variables

    el  : | P(α, β, u, u')                  --  this is ok, because u and u' are already in the existential
    --    | P(u, m, u, u')                  --  this is NOT ok for two reasons—we have escaped u, it now became a constant
          |----------------------
          |
          | 
          |
          |
    
    formula : φ  by ∃-elim existential, el

  -}

check'rule Exists'Elimination _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule ∃-elim."

check'rule Repetition [assertion] formula = do
  fm <- asserts'formula assertion
  because ("I was trying to check the rule repetition.") (formula `unify` fm)

check'rule Repetition _ _ = do
  throwError $! Err "I saw wrong number or shapes of arguments to the rule `repetition'."

check'rule (Custom name) assertions formula = do
  J.Rule _ typings premises conclusion <- find'rule name

  triples <- mapM (\ (n, t) -> do { v <- fresh'free ; return (n, v, t) }) typings

  let sub = concatMap (\ (old, new, _) -> F old ==> Var (Free new)) triples

  let premises' = apply sub premises
  let conclusion' = apply sub conclusion

  let t'patch = Map.fromList $! map (\ (_, F n, t) -> (n, Forall'T [] t)) triples
  s <- get
  put s{ typing'ctx = t'patch `Map.union` typing'ctx s}

  assertions `unify` premises'
  formula `unify` conclusion'

check'rule rule assertions formula = do
  throwError $! Err "This is a wrong justification."


find'rule :: String -> Check J.Rule
find'rule name = do
  juds <- gets judgments
  case List.find (\ (J.Jud _ _ rules) -> isJust $! List.find (\ (J.Rule n _ _ _) -> name == n) rules) juds of
    Nothing -> do
      throwError $! Err ("I don't know the rule named `" ++ name ++ "'.")

    Just (J.Jud _ _ rules) -> do
      case List.find (\ (J.Rule n _ _ _) -> name == n) rules of
        Nothing -> error "internal error: this should never happen"

        Just rule -> do
          return rule


instantiate :: Formula -> [(Rigid, Type'Scheme)] -> Check Formula
instantiate e@(Exists _ _) bs = instantiate'exist'to e bs
instantiate u@(Forall _ _) bs = instantiate'universal'to u bs
instantiate f _ = throwError $! Err ("I was trying to instantiate the formula `" ++ show f ++ "' but it isn't a quantified formula.")


instantiate'exist'to :: Formula -> [(Rigid, Type'Scheme)] -> Check Formula
instantiate'exist'to fm [] = do
  return fm

instantiate'exist'to (F.Exists (n, ts) body) ((r, ts') : cs) = do
  tc <- fresh'type'const
  t <- ts `instantiate'scheme'at` [tc]
  t' <- ts' `instantiate'scheme'at` [tc]  --  this is not strictly necessary, the constant would unify with a fresh variable from the ts' too
  t `unify` t'
  instantiate'exist'to (apply (B n ==> Var (Rigid r)) body) cs

instantiate'exist'to fm _ = do
  throwError $! Err ("Instantiation error. The `" ++ show fm ++ "' is not an existentially quantified formula and there are some instantiation-arguments (terms) left.")


instantiate'universal'to :: Formula -> [(Rigid, Type'Scheme)] -> Check Formula
instantiate'universal'to fm [] = do
  return fm

instantiate'universal'to (F.Forall (v, ts) body) ((r, ts') : cs) = do
  tc <- fresh'type'const
  t <- ts `instantiate'scheme'at` [tc]
  t' <- ts' `instantiate'scheme'at` [tc]  --  this is not strictly necessary, the constant would unify with a fresh variable from the ts' too
  t `unify` t'
  instantiate'universal'to (apply (B v ==> Var (Rigid r)) body) cs

instantiate'universal'to fm _ = do
  throwError $! Err ("Instantiation error. The `" ++ show fm ++ "' is not an existentially quantified formula and there are some instantiation-arguments (terms) left.")


unify'with'instance :: Formula -> Formula -> Check ()
unify'with'instance existential@(Exists _ _) instantiation = do
  --  Any of the terms in the instantiation can be abstracted away.
  --  I just decompose and the prefix from the existential gets substituted
  --  with fresh free-vars.
  --  Then unification.

  --  Decomposes the left formula into a left-prefix and the (ideally) right formula.
  --  ∃ x ∃ y ∃ z ...  and ∃ a ...  results in ([x, y], ∃ z ...)
  --  I need to decompose both of them
  (binds'l, body'l) <- decompose existential
  (binds'r, _) <- decompose instantiation

  --  binds'l needs to be longer than binds'r
  unless  (length binds'l > length binds'r)
          (throwError $! Err ("The supposedly more general formula `" ++ show existential ++ "' does not have a longer prefix than its supposed instantiation `" ++ show instantiation ++ "'."))

  let pref'len = length binds'l - length binds'r
  let prefix = take pref'len binds'l
  --  TODO: I should think a bit more about what is happening with the levels of the fresh free-vars.
  --        Does it make sense to give them the current depth level? Is it correct?

  --  TODO: TYPE-CHECK!
  --        I am thinking this: All the bound variables that I have just instantiated to free-vars had types,
  --        I should record those in the typing environment somehow—maybe I can do `local` and run the unification within it,
  --        so that all the object-level free-vars are known when type-checking during the unification.
  --        The things that they unify with (from the RHS), must have fitting types.
  
  bs <- mapM (\ (s, t) -> do { b <- fresh'free ; return $! ((B s), b, t) }) prefix
  let sub = map (\ (b, f, _) -> Bound'2'Term b (Var (Free f))) bs
  let t'ctx'patch = Map.fromList $! map (\ (_, F s, t) -> (s, t)) bs

  let formula = apply sub $! foldr Exists body'l (drop pref'len binds'l)

  s <- get
  put s{ typing'ctx = t'ctx'patch `Map.union` typing'ctx s }

  because ("I was trying to unify \n  `" ++ show existential ++ "'\nwith its supposed instance \n  `" ++ show instantiation ++ "'\nI instantiated the existential to\n  `" ++ show formula ++ "'.")
          (formula `unify` instantiation)

  where decompose :: Formula -> Check ([(String, Type'Scheme)], Formula)
        decompose (Exists x fm) = do
          (binders, body) <- decompose fm
          return (x : binders, body)
        decompose body = do
          return ([], body)


unify'with'instance universal@(Forall _ _) instantiation = do
  --  I need to decompose both of them
  (binds'l, body'l) <- decompose universal
  (binds'r, _) <- decompose instantiation

  --  binds'l needs to be longer than binds'r
  unless  (length binds'l > length binds'r)
          (throwError $! Err ("The supposedly more general formula `" ++ show universal ++ "' does not have a longer prefix than its supposed instantiation `" ++ show instantiation ++ "'."))

  let pref'len = length binds'l - length binds'r
  let prefix = take pref'len binds'l
  --  TODO: I should think a bit more about what is happening with the levels of the fresh free-vars.
  --        Does it make sense to give them the current depth level? Is it correct?

  --  TODO: TYPE-CHECK!
  --        I am thinking this: All the bound variables that I have just instantiated to free-vars had types,
  --        I should record those in the typing environment somehow—maybe I can do `local` and run the unification within it,
  --        so that all the object-level free-vars are known when type-checking during the unification.
  --        The things that they unify with (from the RHS), must have fitting types.

  bs <- mapM (\ (s, ts) -> do { b <- fresh'free ; return $! ((B s), b, ts) }) prefix
  let sub = map (\ (b, f, _) -> Bound'2'Term b (Var (Free f))) bs
  let t'ctx'patch = Map.fromList $! map (\ (_, F s, t) -> (s, t)) bs
  -- sub <- mapM (\ s -> do { b <- fresh'free ; return $! Bound'2'Term (B s) (Free b) }) (map fst prefix)
  let formula = apply sub $! foldr Forall body'l (drop pref'len binds'l)

  --  REVISE THE QUESTIONS BELOW. DOES IT STILL WORK?
  --  What happens if someone does this:
  {-  universal : ∀ α ∀ β P(α, β, α)  by ...

    formula : P(x, y, y)  by ∀-elim on universal    -}
  --  unification would be ok with that
  --  it would bind a x = y
  --  basically exploiting ∀ x P(x, x, x)

  s <- get
  put s{ typing'ctx = t'ctx'patch `Map.union` typing'ctx s }

  because ("I was trying to unify \n  `" ++ show formula ++ "' () with its supposed instance \n  `" ++ show instantiation ++ "'.")
          (formula `unify` instantiation)

  where decompose :: Formula -> Check ([(String, Type'Scheme)], Formula)
        decompose (Forall x fm) = do
          (binders, body) <- decompose fm
          return (x : binders, body)
        decompose body = do
          return ([], body)


unify'with'instance general instantiation = do
  throwError $! Err ("The formula `" ++ show general ++ "' is not a quantified formula so that it can be instantiated to `" ++ show instantiation ++ "'.")


check'impl'intro :: Assertion -> Formula -> Check ()
check'impl'intro (Derived (Formula assumps) last) impl = do
  let formulae = map snd assumps

  meta'props <- mapM (const fresh'proposition) assumps
  meta'concl <- fresh'proposition

  let meta'impl = foldr Impl meta'concl meta'props

  because ("I was trying to check a rule ==>-intro, specifically the premises") (formulae `unify` meta'props)
  last `unify` meta'concl

  subst <- get'subst

  because ("I was trying to check a rule ==>-intro\n  the implication `" ++ show impl ++ "'\n  the meta-implication `" ++ show (apply subst meta'impl) ++ "'") (impl `unify` (apply subst meta'impl))

check'impl'intro (Derived (Universal _) _) _ = do
  throwError $! Err "A sub-proof justifying implication can not have universal as its assumption."

check'impl'intro (Derived (Existential _ _) _) _ = do
  throwError $! Err "A sub-proof justifying implication can not have existential as its assumption."

check'impl'intro _ _ = do
  throwError $! Err ("Wrong justification for ==>-intro. It needs to be a sub-proof.")

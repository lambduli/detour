module Check.Theorem where


import Control.Monad.Except ( throwError )

import Check.Error ( Error(..) )

import Check.Check ( Check )

import Syntax.Theorem ( Theorem )
import Syntax.Judgment ( Judgment(..) )

-- TODO:  This file implements checking for one theorem.
--        It is working over the Check monad stack.



-- TODO:  This function goes one derivation at a time and checks them using unification and such.
--        I can use local to record the current theorem I am checking so that if it fails
--        I have the information in the environment and can report it in the Error.
--        Or, I could just track the location of the error and report just that.
--        This would be the first time I would do that (·_.)
check'theorem :: Theorem -> Check ()
check'theorem Theorem { assumptions = formulae
                      , conclusion
                      , proof = derivations } = do
  --  I need to traverse the proof (List of Derivations).
  --  The traversing function might succeed and return the last derivation.
  --  That can be a sub-proof too.
  --  If it is a sub-proof, I need to basically treat it as if this sub-proof is the proof
  --  of the theorem.
  --  
  --  I need to check that the assumptions of that sub-proof match the assumptions
  --  of the theorem.
  --  I also need to check that the conclusion of the sub-proof matches the
  --  conclusion of the theorem.

  last <- check'all derivations

  case last of
    Sub'Proof (Proof{ assumption, derivations }) -> do
      check'assumptions assumption formulae

      case reverse derivations of
        last : _ -> do
          check'conclusion last conclusion

        [] -> do
          throwError $! Missing'Conclusion conclusion

    Claim claim -> do
      check'conclusion claim conclusion


--  Checks all the derivations and possibly succeeds with the last Judgment.
--  QUESTION: Should this thing also return environment?
--            Yes, When we go check a sub-proof, we can do some unification whose effect should propagate.
check'all :: [Judgment] -> Check Judgment
check'all [] = do
  throwError $! Empty'Proof Nothing
check'all [judgment] = do
  check'judgment judgment
check'all (judgment : judgments) = do
  last <- check'judgment judgment

  in'scope'of last (check'all judgments)


in'scope'of :: Judgment -> Check a -> Check a
in'scope'of judgment@(Sub'Proof Proof{ name = Just name }) m = do
  scope <- asks judg'scope

  when (scope `Map.member` name) (throwError $! Name'Clash name)

  local (\ env@Env{ judg'scope = scope } -> env{ judg'scope = Map.insert name judgment scope })

in'scope'of (Sub'Proof Proof{ name = Nothing }) m = do
  m

in'scope'of judgment@(Claim Claim{ name = Just name }) m = do
  scope <- asks judg'scope

  when (scope `Map.member` name) (throwError $! Name'Clash name)

  local (\ env@Env{ judg'scope = scope } -> env{ judg'scope = Map.insert name judgment scope })

in'scope'of (Claim Claim{ name = Nothing }) m = do
  m


--  For checking theorem assumptions.
--  The universal case is not possible.
check'assumptions :: Assumption -> [Formula] -> Check ()
check'assumptions (Formula named'formulae) formulae = do
  --  The assumptions need to be in the correct order.
  --  Not every required assumpion needs to be used.
  match'assumptions named'formulae formulae
    where match'assumptions :: [(Maybe String, Formula)] -> [Formula] -> Check ()
          match'assumptions n@((_, n'fm) : n'fms) (fm : fms)
            = if n'fm `equivalent` fm
              then match'assumptions n'fms fms
              else match'assumptions n (fm : fms)

          match'assumptions [] _ = return ()
          match'assumptions _ []
            = throwError $! Wrong'Assumptions "Theorem doesn't allow any more assumptions but the proof mentions some more." -- TODO: make it better

check'assumptions (Universal [String]) = do
  throwError $! Disallowed "Introducing universal variables is not allowed in the premise of a theorem proof."


check'conclusion :: Judgment -> Formula -> Check ()
check'conclusion c@(Claim (Claim { formula })) fm
  = unless  (formula `alpha'equivalent'to` fm)
            (throwError $! Wrong'Conclusion fm c)
check'conclusion der fm
  = throwError $! Wrong'Conclusion fm der


check'judgment :: Judgment -> Check Judgment
--  TODO: If the Judgment is a Sub'Proof return the last judgment of that sub-proof.
--        If that is a sub-proof also, do that recursively.
--        At the end, there needs to be some judgment that is a claim.
check'judgment Sub'Proof Proof{ name, assumption, derivations } = do
  undefined
check'judgment Claim c@Claim{ formula, justification } = do
  --  TODO: Check this judgment.
  justification `justifies` formula

  return c


justifies :: Justification -> Formula -> Check ()
--  QUESTION: Should this function return a unifying substitution
--            or should it just apply the substitution and return unit?
justifies Rule{ kind = rule, on = identifiers } fm = do
  judgments <- mapM id'to'jud identifiers
  
  check'rule rule judgments fm

justifies (Theorem { name, on = identifiers }) fm = do
  Theorem { assumptions, conclusion, proof } <- look'up'theorem name

  identifiers `are'compatible'with` assumptions

  fm `is'compatible'with` conclusion

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

  undefined


id'to'jud :: String -> Check (Either Formula Judgment)
id'to'jud identifier = do
  scope <- asks judg'scope
  case Map.lookup scope identifier of
    Nothing -> do
      throwError $! Unknown'Identifier identifier
    Just either -> do
      return either


are'compatible'with :: [String] -> [Formula] -> Check ()
are'compatible'with identifiers formulae = do
  --  TODO: Get all the identifiers.
  --        They need to bind claims and assumptions.
  --        Those formulae need to unify together.
  --        This might result in a substitution.
  undefined


is'compatible'with :: Formula -> Formula -> Check ()
is'compatible'with formula conclusion = do
  --  TODO: They should just unify together modulo α-equivalence.
  --        This might result in a substitution.
  undefined


check'rule :: Rule -> [Either Formula Judgment] -> Formula -> Check ()
check'rule Impl'Intro judgments formula = do
  undefined

check'rule Impl'Elim judgments formula = do
  undefined

check'rule Conj'Intro judgments formula = do
  undefined

check'rule Conj'Elim judgments formula = do
  undefined

check'rule Disj'Intro judgments formula = do
  undefined

check'rule Disj'Elim judgments formula = do
  undefined

check'rule Neg'Elim judgments formula = do
  undefined

check'rule Equiv'Intro judgments formula = do
  undefined

check'rule Equiv'Elim judgments formula = do
  undefined

check'rule True'Intro [] Term.True = do
  return ()

check'rule Proof'By'Contradiction judgments formula = do
  m <- asks mode
  case m of
    Intuitionistic -> do
      throwError Disallowed'By'Contradiction
    Classical -> do
      undefined

check'rule Contra'Elim judgments formula = do
  undefined

check'rule Forall'Intro judgments formula = do
  undefined

check'rule Forall'Elim judgments formula = do
  undefined

check'rule Exists'Introduction judgments formula = do
  undefined

check'rule Exists'Elimination judgments formula = do
  undefined

check'rule Repetition judgments formula = do
  undefined

check'rule (Custom name) judgments formula = do
  undefined

check'rule rule judgments formula = do
  throwError $! Wrong'Justification rule judgments formula


module Check.Theorem where


import Control.Monad.Except ( throwError )

import Check.Error ( Error(..) )

import Check.Check ( Check )

import Syntax.Theorem ( Theorem )
import Syntax.Derivation ( Derivation(..) )

-- TODO:  This file implements checking for one theorem.
--        It is working over the Check monad stack.



-- TODO:  This function goes one derivation at a time and checks them using unification and such.
--        I can use local to record the current theorem I am checking so that if it fails
--        I have the information in the environment and can report it in the Error.
--        Or, I could just track the location of the error and report just that.
--        This would be the first time I would do that ·_.
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


--  Checks all the derivations and possibly succeeds with the last derivation.
check'all :: [Derivation] -> Check Derivation
check'all (derivation : derivations) = do
  --  TODO: check the current derivation
  --          this might lead to some unification
  --          in that case I will need to apply a unifying substitution to the env (all parts)
  --        if it has a name, put it in the scope
  --        within the new environment, run the rest of the checking
  undefined


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


check'conclusion :: Derivation -> Formula -> Check ()
check'conclusion c@(Claim (Claim { formula })) fm
  = unless  (formula `alpha'equivalent'to` fm)
            (throwError $! Wrong'Conclusion fm c)
check'conclusion der fm
  = throwError $! Wrong'Conclusion fm der
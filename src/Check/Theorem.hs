module Check.Theorem where


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
import Check.Proof
import Check.Solver ( solve )

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


import Debug.Trace ( trace, traceM )
import Data.List.Extra ( intercalate )


-- TODO:  This function goes one derivation at a time and checks them using unification and such.
--        I can use local to record the current theorem I am checking so that if it fails
--        I have the information in the environment and can report it in the Error.
--        Or, I could just track the location of the error and report just that.
--        This would be the first time I would do that ̅·_.)

--  TODO: The caller of this function is supposed to collect the final substitution and just to be sure
--        apply it to the whole theorem again. It might not have an effect depending on how I implement this
--        part of the checker.
--        In any case, the caller should then store the finalized theorem for later pretty-printing.

{-  theorem foo : P(α), F(α, β) A ==> B, A ⊢ B
    | _ : P(α)      -- ignore the first premise
    | _ : _         -- this is also possible
    | imp : A ==> B
    | cond : A
    |------------------------------------
    | ...                                   -}
check'theorem :: Theorem -> Check ()
check'theorem T.Theorem { T.name
                        , assumptions = formulae
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

  --  TODO: collect all the free-vars and constants at this level
  --        that includes free-vars and constants in the assumptions
  --        register them and run the check'all

  d <- asks depth

  s <- get
  const'depths <- gets const'depth'context
  free'depths <- gets free'depth'context

  let frees = concatMap collect'free'vars'in'judgment derivations ++ concatMap collect'free'vars'in'formula formulae
  let consts = concatMap collect'consts'in'judgment derivations ++ concatMap collect'consts'in'formula formulae

  let free'patch = Map.fromList $! map (\ f -> (f, d)) frees
  let const'patch = Map.fromList $! map (\ c -> (c, Unrestricted d)) consts

  --  NOTE: I do this, so that all those free-vars in the theorem
  --        that look implicitly universal can not be unified with anything particular.
  let implicit'universals :: Set.Set Free
      implicit'universals = free (conclusion : formulae)

  mapM_ (\ f -> fresh'constant (Unrestricted d) >>= unify f) implicit'universals

  put s { const'depth'context = const'depths `Map.union` const'patch
        , free'depth'context = free'depths `Map.union` free'patch }

  check'all derivations

  --  TODO: maybe abstract away to some function with a nice name
  case List.unsnoc derivations of
    {-  The sub-proof at the final position counts as a proof of the theorem.
        Derivations above this proof are allowed. They are treated as an "auxiliary" context. -}
    Just (_, Sub'Proof (Proof{ assumption = Formula pairs, derivations })) -> do
      let fms = map snd pairs
      formulae `unify` fms

      case List.unsnoc derivations of
        Just (_, last) -> do
          check'conclusion last conclusion

        Nothing -> do
          throwError $! Err "Missing conclusion."

    Just (_, Sub'Proof (Proof{ assumption = Universal _, derivations })) -> do
      throwError $! Err "Introducing universal variables is not allowed in the premise of a theorem proof."

    Just (_, Sub'Proof (Proof{ assumption = Existential _ _, derivations })) -> do
      throwError $! Err "Introducing existential assumptions is not allowed in the premise of a theorem proof."


    Just (_, c@(J.Claim _)) -> do
      check'conclusion c conclusion

    Nothing -> do
      throwError $! Err "Missing conclusion."
  
  -- print'constraints
  solve


--  TODO: better name for the function
check'conclusion :: Judgment -> Formula -> Check ()
check'conclusion c@(J.Claim (C.Claim { formula })) fm = do
  formula `unify` fm
  --  TODO: Later, I can have something like this:
  -- unless'ok (formula `unify` fm)
  --           (throwError $! Wrong'Conclusion fm c)
  --  The function `unless'ok` solves all the previously collected constraints.
  --  If one of them causes a failure, it does nothing to the error.
  --  It they all succeed, it then runs the monadic action in its argument, (formula `unify` fm) here,
  --  and solves all the constraints collected from that while using
  --  the function `withError` or something like that to change the error if it failed.
  --  If it doesn't fail either, it does nothing.

  --  It does the "failure recovery" so that it can change the value of the error if it fails.
  --  If it doesn't fail, it does nothing.

check'conclusion der fm = do
  throwError $! Err "Wrong conclusion."


print'constraints :: Check ()
print'constraints = do
  constrs <- gets term'constraints

  traceM (intercalate "\n" (map show constrs))

  return ()
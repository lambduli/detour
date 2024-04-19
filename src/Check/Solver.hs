{-# LANGUAGE UndecidableInstances #-}

module Check.Solver where


import Control.Monad.Reader ( ReaderT, asks, local )
import Control.Monad.State ( MonadState(get, put), gets )
import Control.Monad.Except ( Except, runExcept, throwError, tryError, withError, catchError )
import Control.Monad.Extra ( whenM, anyM )


import Check.Check
import Check.Constraint ( Constraint(..) )
import Check.Substitute ( Substitute(apply), compose )
import Check.Substitution ( Substitution, (==>) )
import Check.Substitution qualified as Substitution
import Check.State ( State(..), Level(..) )
import Check.Error ( Error(..) )

import Syntax.Term ( Term(..), Free(..), Constant(..), Bound(..) )
import Syntax.Relation ( Relation(..), Prop'Var(..) )
import Syntax.Formula hiding ( True, False )
import Syntax.Formula qualified as F
import Syntax.Type ( Type(..) )


solve :: Check ()
solve = do
  _ <- get'subst
  return ()

--  TODO: solve all the constraints in the state
--  For now, I could solve them and throw away the resulting substitution, wasting compute time.
--  This would make it easier for me to doeal with "iterative" solving—I wouldn't actually be doing any interative.
--  Later, when I figure out what I need to do exactly to keep the substitution ...

--  Actually, I think it might be pretty clear what to do.
--  Keep the substitution in the state. When asked to `solve`, apply the current substitution to the newly accumulated
--  constraints and only then start solving.
--  Obtain the substitution and store it, empty the constraints.
--  This should be very much equivalent to as if it was solved during one big go.


solve'constraints :: (Unifier a, Substitute a) => [Constraint a] -> Substitution -> Check Substitution
solve'constraints [] sub = return sub
solve'constraints ((a :≡: a') : cs) sub = do
  sub' <- a `mgu` a'
  solve'constraints (apply sub' cs) (sub' `compose` sub)


get'subst :: Check Substitution
get'subst = do
  t'cons <- gets term'constraints
  f'cons <- gets formula'constraints
  subst <- solve'constraints t'cons Substitution.empty
  subst' <- solve'constraints (apply subst f'cons) subst

  t'cons <- gets type'constraints
  subst't <- solve'constraints t'cons Substitution.empty
  return $! subst' `compose` subst't


class Unifier b where
  mgu :: b -> b -> Check Substitution


instance Unifier Term where
  mgu :: Term -> Term -> Check Substitution
  Bound l@(B n) `mgu` Bound r@(B n')
    | n == n' = return Substitution.empty
    | otherwise = throwError $! Err ("I could not unify two non-identical bound variables, the `" ++ show l ++ "' with `" ++ show r ++ "'.")

  Bound l `mgu` r = do
    throwError $! Err ("I could not unify a bound variable `" ++ show l ++ "' with a term `" ++ show r ++ "'.")

  l `mgu` Bound r = do
    throwError $! Err ("I could not unify a bound variable `" ++ show r ++ "' with a term `" ++ show l ++ "'.")

  l@(App (C n) args) `mgu` r@(App (C n') args')
    | n == n' = do
      --  NOTE: I am not checking levels. If the names are the same, they ought to be the same constant.
      args `mgu` args'
    | otherwise = throwError (Err ("I could not unify `" ++ show l ++ "' with `" ++ show r ++ "'." ))

  var@(Free free@(F _)) `mgu` var'@(Free free'@(F _)) = do
    if var == var'
    then return Substitution.empty 
    else do
      l <- free'level free
      l' <- free'level free'
      --  we always keep the one that has a "lower level" meaning that one is "more global" one
      if l' <= l
      then return (free ==> var')
      else return (free' ==> var) -- l' > l

  var@(Free free@(F n)) `mgu` term
    --  TODO: I could call this function in the monadic context as well.
    | free `occurs'in` term = do
      throwError $! Err ("occurs check failed. A free variable `" ++ show free ++ "' occurs in the term `" ++ show term ++ "'.")
    | otherwise = do
      i <- free'level free
      whenM (term `escapes'to` i) (throwError $! Err ("escape check failed. Some constant from `" ++ show term ++ "' attempted an escape to the lower depth."))

      return (free ==> term)

  term `mgu` var@(Free _)
    = var `mgu` term

  l `mgu` r = do
    throwError $! Err ("I could not unify `" ++ show l ++ "' with `" ++ show r ++ "'.")


instance Unifier Formula where
  mgu :: Formula -> Formula -> Check Substitution
  F.True `mgu` F.True = do
    return Substitution.empty

  F.False `mgu` F.False = do
    return Substitution.empty

  {-

      ℕ = Zero
        | Suc ℕ

      ...

      ∀ m n ℕ(m) => ℕ(n) => ℕ(m + n)
      + : ℕ => ℕ => ℕ
      + = λ (m : ℕ) (n : ℕ) ->  case m of
                                  Zero -> n
                                  Suc m' -> Suc (m' + n)


      a->b : _A  by rule ...

      rule schema AND-intro for proposition A, B: | A
                                                  | B
                                                  |----------------------- AND-intro
                                                  | A AND B

      _ : K AND B  by rule AND-intro on .., ..


      theorem schema foo for proposition A, B, C: A ==> B, B ==> C, A ⊢ C
      ...
  
  -}
  f@(Atom (Meta'Rel var@(Prop'Var _))) `mgu` right@(Forall var' body') = do
    throwError $! Err ("I could not unify a propositional meta-variable `" ++ show var ++ "' with a quantified formula `" ++ show right ++ "'.")

  f@(Atom (Meta'Rel var@(Prop'Var _))) `mgu` right@(Exists var' body') = do
    throwError $! Err ("I could not unify a propositional meta-variable `" ++ show var ++ "' with a quantified formula `" ++ show right ++ "'.")

  -- f@(Atom (Meta'Rel var@(Prop'Var _))) `mgu` right
  --   | f == right = return Substitution.empty
  --   | otherwise = do
  --       return (var ==> right)

  f@(Atom (Meta'Rel var@(Prop'Var _))) `mgu` fm
    | f == fm = return Substitution.empty
    | var `occurs'in` fm = throwError $! Err ("occurs check failed. A propositional meta-variable `" ++ show var ++ "' occurs in the formula `" ++ show fm ++ "'.")
    | otherwise = return (var ==> fm)

  left `mgu` f@(Atom (Meta'Rel (Prop'Var _))) = do
    f `mgu` left

  l@(Atom (Rel n args)) `mgu` r@(Atom (Rel n' args'))
    | n == n' = args `mgu` args'
    | otherwise = throwError $! Err ("I could not unify `" ++ show l ++ "' with `" ++ show r ++ "'.")  --  TODO: unification error, they are not the same formula

  (Not fm) `mgu` (Not fm') = do
    fm `mgu` fm'

  (left `And` right) `mgu` (left' `And` right') = do
    [left, right] `mgu` [left', right']

  (left `Or` right) `mgu` (left' `Or` right') = do
    [left, right] `mgu` [left', right']

  (left `Impl` right) `mgu` (left' `Impl` right') = do
    [left, right] `mgu` [left', right']

  (left `Eq` right) `mgu` (left' `Eq` right') = do
    [left, right] `mgu` [left', right']

  --  TODO: When unifying two ∀s ∃s
  --        I can do this:  pick a new name,
  --                        substitute on both sides respective bound variable for a bound var with the new name,
  --                        unify both sides.
  (Forall (var, _) body) `mgu` (Forall (var', _) body') = do
    --  TODO: Should I do anything with the types?
    --        I think I should try to unify them together.
    --        If those foralls are supposed to be the same, their types need to be the same.
    n <- fresh'name
    let b = B n
        body'a = apply (B var ==> Bound b) body
        body'b = apply (B var' ==> Bound b) body'

    body'a `mgu` body'b

  (Exists (var, _) body) `mgu` (Exists (var', _) body') = do
    --  TODO: Should I do anything with the types?
    --        I think I should try to unify them together.
    --        If those exists are supposed to be the same, their types need to be the same.
    n <- fresh'name
    let b = B n
        body'a = apply (B var ==> Bound b) body
        body'b = apply (B var' ==> Bound b) body'

    body'a `mgu` body'b

  l `mgu` r = do
    throwError (Err ("I could not unify `" ++ show l ++ "' with `" ++ show r ++ "'." ))


instance Unifier Type where
  _ `mgu` _ = throwError $! Err "Unification on types is not implemented yet!!!"


instance (Unifier b, Substitute b) => Unifier [b] where
  mgu :: [b] -> [b] -> Check Substitution
  [] `mgu` [] = return Substitution.empty

  (b : bs) `mgu` (b' : bs') = do
    su1 <- b `mgu` b'
    su2 <- apply su1 bs `mgu` apply su1 bs'
    return (su2 `compose` su1)

  _ `mgu` _ = do
    throwError $! Err ("I could not unify differently sized lists.")



class Occurs a b | a -> b, b -> a where
  occurs'in :: a -> b -> Bool


instance Occurs Free Term where
  occurs'in :: Free -> Term -> Bool
  _ `occurs'in` (Bound _) = False  --  TODO: this should also never happen, it would be another internal error
  free `occurs'in` (App _ args) = any (occurs'in free) args
  free `occurs'in` (Free f) = free == f


instance Occurs Prop'Var Formula where
  occurs'in :: Prop'Var -> Formula -> Bool
  _ `occurs'in` F.True = False
  _ `occurs'in` F.False = False
  _ `occurs'in` (Atom (Rel _ _)) = False
  prop `occurs'in` (Atom (Meta'Rel prop'var)) = prop == prop'var
  prop `occurs'in` (Not fm) = prop `occurs'in` fm
  prop `occurs'in` (left `And` right) = any (occurs'in prop) [left, right]
  prop `occurs'in` (left `Or` right) = any (occurs'in prop) [left, right]
  prop `occurs'in` (left `Impl` right) = any (occurs'in prop) [left, right]
  prop `occurs'in` (left `Eq` right) = any (occurs'in prop) [left, right]
  prop `occurs'in` (Forall _ body) = prop `occurs'in` body
  prop `occurs'in` (Exists _ body) = prop `occurs'in` body


escapes'to :: Term -> Int -> Check Bool
(Bound _) `escapes'to` depth -- = return False
  = error "internal error: Bound variable participating in unification."
  --  TODO: I could also just return False and save this dramatic piece of code.
  --  TODO: I think that throwing an error here is a mistake.
  --        Unifying a free variable with a term _CONTAINING_ bound vars is ok.
  --        And I made sure that I will never unify Bound with anything beside Bound.
  --        Well, now I am not sure!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  --        I think that this error is correct. Bounds are supposed to disappear.

(App c@(C n) args) `escapes'to` depth = do
  level <- const'level c
  case level of
    Restricted l | l < depth -> do
      return True

    _ -> anyM (\ t -> escapes'to t depth) args

(Free _) `escapes'to` depth = return False

module Check.Unify where


-- import Control.Monad.Reader ( ReaderT, asks, local )
-- import Control.Monad.State ( MonadState(get, put), gets )
import Control.Monad.Except ( throwError )


import Syntax.Formula ( Formula )
import Syntax.Term ( Term(..), Free(..), Constant(..) )
import Syntax.Type ( Type )


import Check.Check ( Check, collect )
import Check.Error ( Error(..) )
import Check.Constraint ( Constraint(..) )
-- import Check.Substitution ( Substitution )
import Check.Assertion
import Check.Solver ( solve )


class Unify a b where
  unify :: a -> b -> Check ()


instance Unify Term Term where
  t1 `unify` t2 = do
    collect (t1 :≡: t2)
    --  TODO: deal with the types later
    -- ty1 <- type'of t1
    -- ty2 <- type'of t2
    -- collect (ty1 :≡: ty2)
    solve


instance Unify Formula Formula where
  f1 `unify` f2 = do
    collect (f1 :≡: f2)
    solve


instance Unify Free Constant where
  free `unify` constant = do
    Free free `unify` App constant []


instance Unify Assertion Formula where
  (Assumed fm) `unify` fm' = fm `unify` fm'
  (Claimed fm) `unify` fm' = fm `unify` fm'
  (Axiom fm) `unify` fm' = fm `unify` fm'
  (Derived _ _) `unify` _ = do
    throwError undefined  --  TODO: error


instance Unify Type Type where
  t1 `unify` t2 = do
    collect (t1 :≡: t2)
    solve


instance Unify a b => Unify [a] [b] where
  [] `unify` [] = do
    return ()
 
  (a : as) `unify` (b : bs) = do
    a `unify` b
    as `unify` bs

  _ `unify` _ = do
    throwError $! Err "Unification Error. Can not unify two lists with differing lengths."

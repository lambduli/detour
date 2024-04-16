module Check.Check where


import Control.Monad.Reader ( ReaderT, asks )
import Control.Monad.State ( MonadState(get, put), gets, StateT )
import Control.Monad.Except ( Except, throwError )

import Data.Map.Strict qualified as Map

import Syntax.Term ( Term, Constant(..), Bound(..), Free(..) )
import Syntax.Theorem ( Theorem )
import Syntax.Formula ( Formula(..) )
import Syntax.Relation ( Relation(..), Prop'Var(..) )

import Check.Error ( Error(..) )
import Check.Environment ( Environment(..) )
import Check.State ( State(..), Level(..) )
import Check.Constraint ( Constraint )


type Check a
  = ReaderT
      Environment
      (StateT
        State
        (Except Error))
      a


{-  Allocates a new empty slot for all the given Free variables.  -}
-- allocate'metas :: [Free] -> Check [Int]
-- allocate'metas vars = do
--   mapM allocate'meta vars


{-  Allocates a new empty slot for the given Free variable. -}
-- allocate'meta :: Free -> Check Int
-- allocate'meta _ = do
--   State{ metas = old, counter = new'slot } <- get
--   let new = Map.insert new'slot Nothing old
--   put State{ metas = new, counter = new'slot + 1 }
--   return new'slot  


fresh'name :: Check String
fresh'name = do
  s@State{ counter } <- get
  put s{ counter = counter + 1 }
  return $! "_" ++ show counter


fresh'proposition :: Check Formula
fresh'proposition = do
  name <- fresh'name
  return $! Atom (Meta'Rel (Prop'Var name))


fresh'free :: Check Free
fresh'free = do
  n <- fresh'name

  d <- asks depth

  s <- get
  free'depths <- gets free'depth'context
  put s{ free'depth'context = Map.insert (F n) d free'depths }

  return (F n)


fresh'constant :: Level -> Check Constant
fresh'constant l = do
  name <- fresh'name

  s <- get
  const'depths <- gets const'depth'context
  put s{ const'depth'context = Map.insert (C name) l const'depths }

  return (C name)


const'level :: Constant -> Check Level
const'level c = do
  const'depths <- gets const'depth'context
  case Map.lookup c const'depths of
    Nothing -> do
      throwError (Err ("Internal Error. A constant `" ++ show c ++ "' is not recorded in the context."))

    Just l -> return l


free'level :: Free -> Check Int
free'level f = do
  free'depths <- gets free'depth'context
  case Map.lookup f free'depths of
    Nothing -> do
      throwError (Err ("Internal Error. A free variable `" ++ show f ++ "' is not recorded in the context."))

    Just l -> return l


-- assign'constant :: Level -> a -> Check (a, Constant)
-- assign'constant l a = do
--   name <- fresh'name
--   return (a, C l name)


fresh'bound :: Check Bound
fresh'bound = do
  n <- fresh'name

  return (B n)


class Collect a where
  collect :: Constraint a -> Check ()


instance Collect Term where
  collect :: Constraint Term -> Check ()
  collect constraint = do
    s@State{ term'constraints } <- get
    put s{ term'constraints = constraint : term'constraints}


instance Collect Formula where
  collect :: Constraint Formula -> Check ()
  collect constraint = do
    s@State{ formula'constraints } <- get
    put s{ formula'constraints = constraint : formula'constraints}


look'up'theorem :: String -> Check Theorem
look'up'theorem name = do
  thms <- asks theorems

  case Map.lookup name thms of
    Nothing -> do
      throwError $! Err ("Unknown theorem `" ++ name ++ "'.")
    
    Just thm -> do
      return thm

-- {-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE GADTs #-}
-- {-# LANGUAGE ScopedTypeVariables #-}
-- -- {-# LANGUAGE RecordPuns #-}

module Control.Monad.InteractT where


import Prelude hiding ( interact )

-- 
-- 
-- 
-- 
-- 
-- 
class Monad m => Interact q m where
  request :: q r -> m r
-- 
-- 
-- 
-- 
-- 
-- 
newtype InteractT env st err m a = InteractT { interact :: env -> st -> m (Either err (st, a)) }


--  Identity:       fmap id == id
--  Composition:    fmap (f . g) == fmap f . fmap g
instance Functor m => Functor (InteractT env st err m) where
  fmap :: (a -> b) -> InteractT env st err m a -> InteractT env st err m b
  fmap f InteractT{ interact = f' } = InteractT { interact = \ e s -> (\case  Left err -> Left err
                                                                              Right (s', a) -> Right (s', f a)) `fmap` f' e s }


--  Identity:       pure id <*> v = v
--  Composition:    pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
--  Homomorphism    pure f <*> pure x = pure (f x)
--  Interchange     u <*> pure y = pure ($ y) <*> u

--                  fmap f x = pure f <*> x
instance (Functor m, Monad m) => Applicative (InteractT env st err m) where
  pure :: a -> InteractT env st err m a
  pure a = InteractT { interact = \ _ s -> pure (Right (s, a)) }

  liftA2 :: (Functor m, Monad m) => (a -> b -> c) -> InteractT env st err m a -> InteractT env st err m b -> InteractT env st err m c
  liftA2 f InteractT{ interact = f1 } InteractT{ interact = f2 }
    = InteractT { interact = \ e s -> f1 e s >>= (\case Left err -> pure (Left err)
                                                        Right (s', a) -> (\case Left err -> Left err
                                                                                Right (s'', b) -> Right (s'', f a b)) `fmap` f2 e s') }


--  Left Identity:  return a >>= k = k a
--  Right Identity: m >>= return = m
--  Associativity:  m >>= (\x -> k x >>= h) = (m >>= k) >>= h

--                  pure = return
--                  m1 <*> m2 = m1 >>= (\x1 -> m2 >>= (\x2 -> return (x1 x2)))
--                  (*>) = (>>)
instance Monad m => Monad (InteractT env st err m) where
  InteractT{ interact = f1 } >>= f = InteractT { interact = \ e s -> f1 e s >>= (\case  Left err -> return (Left err)
                                                                                        Right (s', a) -> let InteractT{ interact } = f a in interact e s') }






ask :: Monad m => InteractT env st err m env
ask = InteractT { interact = \ env st -> return (Right (st, env)) }


asks :: Monad m => (env -> a) -> InteractT env st err m a
asks f = InteractT { interact = \ env st -> return (Right (st, f env)) }


local :: (env -> env) -> InteractT env st err m a -> InteractT env st err m a
local fn InteractT{ interact = f } = InteractT { interact = \ env st -> f (fn env) st }


get :: Monad m => InteractT env st err m st
get = InteractT { interact = \ _ st -> return (Right (st, st)) }


gets :: Monad m => (st -> b) -> InteractT env st err m b
gets f = InteractT { interact = \ _ st -> return (Right (st, f st)) }


put :: Monad m => st -> InteractT env st err m ()
put st = InteractT { interact = \ _ _ -> return (Right (st, ())) }


throwError :: Monad m => err -> InteractT env st err m a
throwError err = InteractT { interact = \ _ _ -> return (Left err) }


--  m a -> (e -> m a) -> m a
catchError :: Monad m => InteractT env st err m a -> (err -> InteractT env st err m a) -> InteractT env st err m a
catchError action f = tryError action >>= \case Left err -> f err
                                                Right a -> InteractT { interact = \ _ st -> return (Right (st, a)) }


-- MonadError e m => (e -> e) -> m a -> m a
withError :: Monad m => (err -> err) -> InteractT env st err m a -> InteractT env st err m a
withError f InteractT{ interact = f' } = InteractT { interact = \ env st -> f' env st >>= \case Left e -> return (Left (f e))
                                                                                                Right r -> return (Right r) }


--   MonadError e m => m a -> m (Either e a)
tryError :: Monad m => InteractT env st err m a -> InteractT env st err m (Either err a)
tryError InteractT{ interact = f } = InteractT { interact = \ env st -> f env st >>= \case  Left err -> return (Right (st, Left err))
                                                                                            Right (s, a) -> return (Right (s, Right a)) }


inter :: (Monad m, Interact qu m) => qu re -> InteractT env st err m re
inter q = InteractT { interact = \ _ s -> request q >>= (\ re -> return (Right (s, re))) }






run'interact :: Monad m => st -> env -> InteractT env st err m a -> m (Either err (st, a))
run'interact st env InteractT{ interact } = interact env st

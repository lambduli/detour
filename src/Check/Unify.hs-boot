module Check.Unify where


import Check.Check ( Check )
import Check.Assertion ( Assertion )

import Syntax.Term ( Term, Free, Constant )
import Syntax.Formula ( Formula )
import Syntax.Type ( Type )


class Unify a b where
  unify :: Monad m => a -> b -> Check m ()


instance Unify Term Term


instance Unify Formula Formula where


instance Unify Free Constant where


instance Unify Assertion Formula where


instance Unify Type Type where


instance Unify a b => Unify [a] [b] where

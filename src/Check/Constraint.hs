module Check.Constraint where


-- import Syntax.Term ( Term )
-- import Syntax.Formula ( Formula )


infix 5 :≡:

data Constraint a = a :≡: a
  deriving (Show, Eq)


-- data Constraint'  = Term `Unify'T` Term
--                   | Formula `Unify'F` Formula
--                   | Formula `Instance'of` Formula
--   deriving (Show, Eq)

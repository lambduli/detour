module Check.Constraint where


infix 5 :≡:

data Constraint a = a :≡: a
  deriving (Show, Eq)

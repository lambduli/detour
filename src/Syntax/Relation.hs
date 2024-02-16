module Syntax.Relation where


import Syntax.Term ( Term )


data Relation = Rel String [Term]     -- P(x, ƒ(x, y))
  deriving (Show, Eq, Ord)

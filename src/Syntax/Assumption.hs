module Syntax.Assumption where


import Syntax.Formula ( Formula )


data Assumption = Formula [(Maybe String, Formula)]
                | Universal [String]
  deriving (Show, Eq)

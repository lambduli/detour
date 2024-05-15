module Syntax.Jud where


import Syntax.Type ( Type )
import Syntax.Formula ( Formula )


data Jud = Jud String (String, [Type]) [Rule]
  deriving (Show, Eq)


data Rule = Rule String [(String, Type)] [Formula] Formula
  deriving (Show, Eq)

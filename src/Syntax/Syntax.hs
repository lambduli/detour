module Syntax.Syntax where


import Syntax.Type ( Type )


newtype Syntax = Syntax [Constructor]
  deriving (Show, Eq)


data Constructor = Constructor String [Type]
  deriving (Show, Eq)

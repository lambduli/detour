module Syntax.Module where


import Syntax.Definition ( Definition )


data Module = Module  { name :: Maybe String
                      , constants :: [String]
                      , definitions :: [Definition] }
  deriving (Show, Eq)

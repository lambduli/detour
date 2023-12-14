module Syntax.Assumption where

import Syntax.Formula ( Formula )


data Assumption = Formula Formula
                | Universal [String]
                | Formula'For'Some Formula [String]
  deriving (Show, Eq)

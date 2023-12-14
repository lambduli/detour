module Syntax.Theorem where

import Syntax.Assumption ( Assumption )


data Theorem = Theorem  { name :: String
                        , assumptions :: [Assumption]
                        , conclusion :: Formula
                        , justification :: [Derivation] }
  deriving (Show, Eq)

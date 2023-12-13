module Syntax.Theorem where


data Theorem = Theorem  { name :: String
                        , assumptions :: [Formula]
                        , conclusion :: Formula
                        , justification :: [Derivation] }
  deriving (Show, Eq)

module Syntax.Theorem where


import Syntax.Formula ( Formula )
import Syntax.Derivation ( Derivation )
import Syntax.Assumption ( Assumption )


data Theorem = Theorem  { name :: String
                        , assumptions :: [Formula]
                        , conclusion :: Formula
                        , proof :: [Derivation] }
                        --  TODO: Do I want to allow the more flexible way?
                        --        Or do I want to just make it Proof?
  deriving (Eq)


instance Show Theorem where
  --  TODO: replace the `show assumptions` with some nice way to print the assumptions
  --  TODO: if the assumptions are empty, don't print them and the ⊢, only print the conclusion
  --  TODO: ?
  show :: Theorem -> String
  show Theorem{ name, assumptions, conclusion, proof }
    = "theorem " ++ name ++ " : " ++ show assumptions ++ " ⊢ " ++ show conclusion ++ "\n" ++ show proof
    
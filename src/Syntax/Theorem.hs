module Syntax.Theorem where


import Data.List.Extra ( intercalate )

import Syntax.Formula ( Formula )
import Syntax.Judgment ( Judgment )


data Theorem = Theorem  { name :: String
                        , prop'vars :: [String]
                        , assumptions :: [Formula]
                        , conclusion :: Formula
                        , proof :: [Judgment] }
  deriving (Eq)


instance Show Theorem where
  --  TODO: replace the `show assumptions` with some nice way to print the assumptions
  --  TODO: if the assumptions are empty, don't print them and the ⊢, only print the conclusion
  --  TODO: ?
  show :: Theorem -> String
  show Theorem{ name, prop'vars, assumptions, conclusion, proof }
    = "theorem schema " ++ name ++ "for propositions"
        ++ intercalate ", " prop'vars
        ++ " : "
        ++ intercalate ", " (map show assumptions)
        ++ " ⊢ " ++ show conclusion
        ++ "\n" ++ intercalate "\n" (map show proof)
    
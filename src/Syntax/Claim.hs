module Syntax.Claim where


import Syntax.Formula ( Formula )
import Syntax.Justification ( Justification )


data Claim = Claim{ name :: Maybe String
                  , formula :: Formula
                  , justification :: Justification }
  deriving (Eq)


instance Show Claim where
  show Claim{ name = Nothing, formula, justification }
    = "_" ++ " : " ++ show formula ++ "  by " ++ show justification
  show Claim{ name = Just n, formula, justification }
    = n ++ " : " ++ show formula ++ "  by " ++ show justification

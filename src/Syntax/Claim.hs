module Syntax.Claim where


import Syntax.Formula ( Formula )
import Syntax.Justification ( Justification )


data Claim = Claim{ name :: Maybe String
                  , formula :: Formula
                  , justification :: Justification }
  deriving (Show, Eq)

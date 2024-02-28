module Syntax.Proof where

import Syntax.Assumption ( Assumption )
import Syntax.Judgment ( Judgment )


data Proof = Proof{ name :: Maybe String
                  , assumption :: Assumption
                  , derivations :: [Judgment] }
  deriving (Show, Eq)

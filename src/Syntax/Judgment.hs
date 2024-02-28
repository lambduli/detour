module Syntax.Judgment where


import Syntax.Formula ( Formula(..) )
import Syntax.Assumption ( Assumption )
import Syntax.Justification ( Justification )


--  TODO: this should, perhaps, be called Judgment
data Judgment = Sub'Proof Proof
              | Claim Claim
  deriving (Show, Eq)


data Proof = Proof{ name :: Maybe String
                  , assumption :: Assumption
                  , derivations :: [Judgment] }
  deriving (Show, Eq)


data Claim = Claim{ name :: Maybe String
                  , formula :: Formula
                  , justification :: Justification }
  deriving (Show, Eq)

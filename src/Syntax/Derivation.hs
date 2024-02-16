module Syntax.Derivation where


import Syntax.Formula ( Formula(..) )
import Syntax.Assumption ( Assumption )
import Syntax.Justification ( Justification )


data Derivation = Sub'Proof Proof
                | Claim Claim
  deriving (Show, Eq)


data Proof = Proof{ name :: Maybe String
                  , assumption :: Assumption
                  , derivations :: [Derivation] }
  deriving (Show, Eq)


data Claim = Claim{ name :: Maybe String
                  , formula :: Maybe Formula
                  , justification :: Justification }
  deriving (Show, Eq)

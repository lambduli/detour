module Syntax.Derivation where

import Syntax.Formula ( Formula(..) )
import Syntax.Assumption ( Assumption )


data Derivation = Sub'Proof { name :: Maybe String
                            , assumptions :: [Assumption]  -- assumptions can introduce new constants and variables, that needs to be taken care of
                            , derivations :: [Derivation] }
                | Rule      { name :: Maybe String
                            , formula :: Maybe Formula
                            , justification :: Justification }
  deriving (Show, Eq)

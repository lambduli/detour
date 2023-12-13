module Syntax.Derivation where

import Syntax.Formula ( Formula(..) )


data Derivation = Sub'Proof { name :: Maybe String
                            , assumptions :: [Formula]
                            , derivations :: [Derivation] }
                | Rule      { name :: Maybe String
                            , formula :: Maybe Formula
                            , justification :: Justification }
  deriving (Show, Eq)

module Syntax.Case where


import Syntax.Term ( Constant, Rigid )
import {-# SOURCE #-} Syntax.Proof ( Proof )


data Case = Case (Constant, [Rigid]) Proof
          -- | Case'Rule String ...
  deriving (Show, Eq)

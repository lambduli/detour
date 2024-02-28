module Syntax.Judgment where


import Syntax.Assumption ( Assumption )
import Syntax.Claim ( Claim )
import Syntax.Formula ( Formula(..) )
import {-# SOURCE #-} Syntax.Justification ( Justification )
import {-# SOURCE #-} Syntax.Proof ( Proof )



data Judgment = Sub'Proof Proof
              | Claim Claim
  deriving (Show, Eq)

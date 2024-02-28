module Syntax.Judgment where


import Syntax.Formula ( Formula(..) )
import Syntax.Assumption ( Assumption )
import Syntax.Justification ( Justification )
import Syntax.Proof ( Proof )
import Syntax.Claim ( Claim )


data Judgment = Sub'Proof Proof
              | Claim Claim
  deriving (Show, Eq)

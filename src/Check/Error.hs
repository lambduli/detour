module Check.Error where


import Syntax.Term ( Term )
import Syntax.Formula ( Formula )
import Syntax.Theorem ( Theorem )
import Syntax.Judgment ( Judgment )
import Syntax.Justification ( Rule )

import {-# SOURCE #-} Check.Assertion ( Assertion )


-- TODO:  Track the location of a corresponding token in the source-file.
data Error
  -- = Unif'Mismatch Term Term       --  Can't unify these two term.
  -- | Unknown'Rule String           --  Rule doesn't exist.
  -- | Unknown'Theorem String        --  Theorem doesn't exist.
  -- | Universal'Bound String Term   --  The universal pseudo-variable is bound to some term.
  -- | Unknown'Identifier String

  -- | Disallowed'By'Contradiction

  -- --  What's the difference between these two?
  -- | Rule'Mismatch String          --  The claim is not matching the rule or the "arguments" are not matching.
  -- | Wrong'Justification Rule [Assertion] Formula

  -- | Disallowed String             --  When some syntax is used at a wrong place.
  -- | Wrong'Assumptions String      --  
  -- | Wrong'Conclusion Formula Formula
  -- | Missing'Conclusion Formula
  -- | Empty'Proof (Maybe Theorem)   --  When a proof is an empty list
  --               --  TODO: Change from Maybe Theorem to Theorem!
  -- | Name'Clash String

  -- | WIP String                    --  This is just while I'm developing.


  = Err String
  deriving (Eq)


instance Show Error where
  show (Err msg) = msg


--  What about the informative error reporting where every failure is presented as a sequence of "why and what was I trying to check"
--  data Error
--    = First Unification'Error
--    | Nth ... Error
--
--  Where ... is the information about the current "level".
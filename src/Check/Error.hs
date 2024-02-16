module Check.Error where


import Syntax.Term ( Term )
import Syntax.Formula ( Formula )


-- TODO:  Track the location of a corresponding token in the source-file.
data Error
  = Unif'Mismatch Term Term       --  Can't unify these two term.
  | Rule'Mismatch Formula         --  The claim is not matching the rule or the "arguments" are not matching.
  | Unknown'Rule String           --  Rule doesn't exist.
  | Unknown'Theorem String        --  Theorem doesn't exist.
  | Universal'Bound String Term   --  The universal pseudo-variable is bound to some term.

  | Disallowed String             --  When some syntax is used at a wrong place.
  | Wrong'Assumptions String      --  
  | Wrong'Conclusion Formula Derivation
  | Missing'Conclusion Formula

  | WIP String                    --  This is just while I'm developing.
  deriving (Show, Eq)

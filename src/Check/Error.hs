module Check.Error where


import Syntax.Term ( Term )
import Syntax.Formula ( Formula )


-- TODO:  Track the location of a corresponding token in the source-file.
data Error
  = Unif'Mismatch Term Term       --  Can't unify these two term.
  | Unknown'Rule String           --  Rule doesn't exist.
  | Unknown'Theorem String        --  Theorem doesn't exist.
  | Universal'Bound String Term   --  The universal pseudo-variable is bound to some term.
  | Unknown'Identifier String

  | Disallowed'By'Contradiction
  
  --  What's the difference between these two?
  | Rule'Mismatch String          --  The claim is not matching the rule or the "arguments" are not matching.
  | Wrong'Justification Rule [Either Formula Judgment] Formula

  | Disallowed String             --  When some syntax is used at a wrong place.
  | Wrong'Assumptions String      --  
  | Wrong'Conclusion Formula Judgment
  | Missing'Conclusion Formula
  | Empty'Proof (Maybe Theorem)   --  When a proof is an empty list
                --  TODO: Change from Maybe Theorem to Theorem!
  | Name'Clash String

  | WIP String                    --  This is just while I'm developing.
  deriving (Show, Eq)

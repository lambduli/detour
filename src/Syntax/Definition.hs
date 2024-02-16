module Syntax.Definition where


import Syntax.Formula ( Formula )
import Syntax.Theorem ( Theorem )


--  TODO: I will need to change this to support:
--        - Inductive definitions
--        - Custom rules
--        - Axiom and Rules schemas

--  I don't yet know what that will entail.

data Definition = Axiom Formula
                | Theorem Theorem
  deriving (Show, Eq)
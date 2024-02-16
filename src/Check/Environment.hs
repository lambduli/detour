module Check.Environment where


import Data.Map.Strict qualified as Map

import Syntax.Term( Term )
import Syntax.Theorem ( Theorem )

import Unification.Meta ( Meta)


--  TODO: When I implement the simple version of type-checking
--    [ for the stuff like ∀ ℕ P(ℕ) to be instantiatable only to variables and
--      terms of "type" ℕ ]
--        This is not something I am dealing with right now.
data Environment = Env{ theorems :: Map.Map String Theorem
                      , var'scope :: Map.Map String (Either Meta Term)
                        --  NOTE: When it's a Term it should always be the function application, really.
                        --        It doesn't make sense for it to be a variable.
                        --        The meaning of a Var constructor in Term is for bound variables.
                        --        That will never happen.
                        --        There is sort of a divide between bound variables in formulae
                        --        and variables that we have in scope when doing proves.
                        --        We never have in scope a bound variable.
                        --        We can have in scope universal variables intended for ∀-intro
                        --          (and those are not really variables)
                        --        or variables in assumptions of sub-proofs intended for ∃-elim
                        --          (and those aren't really variables either)
                        --        or implicitly introduced universal variables from ∀-elim
                        --          (those are treated as variables and they are sort of free)
                        --        but none of these are close to what bound variables are.
                      , der'scope :: Map.Map String Either Formula Derivation }
                        --  It's either formula or derivation.
                        --  The formula is for assumptions.
                        --  The Derivation is for sub-proofs and claims.
  deriving (Show, Eq)

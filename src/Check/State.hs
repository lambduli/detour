module Check.State where


import Data.Map.Strict qualified as Map

import Syntax.Term ( Term )

import Check.Meta ( Meta )


{-  The vars tracks what each variable in the scope is known to be.
    This way, the Environment tracks what is in scope and State tracks what it is.

    This should reflect the way things work:
    When something is introduced into the scope, every sub-scope of the current one
    gets access to it.
    However, what the "it" is can change (by unification) somewhere deep down.
    We would have to thread the unifying substitution all the way throught the program,
    basically simulating state.

    This way, we use the read-only environment just to track _WHAT_ is in the scope
    and the mutable state to track _WHAT_ it is.
    Things can change as they need to and we don't need to make sure to "untrack"
    stuff when it goes out of scope.  -}
data State = State{ vars :: Map.Map Int (Either Meta Term) }
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
  deriving (Show, Eq)

module Syntax.Justification where


data Justification  = Rule  { rule :: Rule, on :: [Term] }
                    | Theorem { name :: String, on :: [Term] }
  deriving (Show, Eq)


data Rule = Impl'Intro
          | Impl'Elim
          | Conj'Intro
          | Conj'Elim
          | Disj'Intro
          | Disj'Elim
          | Neg'Elim  -- contradiction introduction
          | Equiv'Intro
          | Equiv'Elim
          | Proof'By'Contradiction
          | Contra'Elim
          | Forall'Intro
          | Forall'Elim
          | Exists'Introduction
          | Exists'Elimination
          | Repetition
          | Custom String -- user-defined rules
          | Tautology -- if I would want to eliminate implication that is in the shape ⊤ ==> A, I don't really need to justify ⊤, its justification is always in scope
  deriving (Show, Eq)

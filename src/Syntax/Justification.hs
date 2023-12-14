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
  deriving (Show, Eq)

module Syntax.Justification where


import Syntax.Term ( Term )
import {-# SOURCE #-} Syntax.Proof ( Proof )


data Justification  = Rule  { kind :: Rule, on :: [String] }
                    | Theorem { name :: String, on :: [String] }
                    | Unproved
                    | Induction { on :: [String] }
                    | Substitution { on' :: Term, using :: String } --  TODO: figure out a better name than on'
                    -- | Case { on :: String, proofs :: [(Proof, String)] }  --  The String is the name of the rule used.
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
          | True'Intro  -- I can trivially justify ⊤
          | Proof'By'Contradiction
          | Contra'Elim
          | Forall'Intro
          | Forall'Elim
          | Exists'Introduction
          | Exists'Elimination
          | Repetition
          | Custom String -- user-defined rules
  deriving (Show, Eq)

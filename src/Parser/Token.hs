module Parser.Token where


--  TODO: DO IT!
data Token  = Upper'Var String
            | Lower'Var String
            | Number String

            | Constant'Before

            --  keywords
            | Comma           --  ,
            | Period          --  .
            | Theorem         --  theorem
            | Axiom           --  axiom
            | Axioms          --  axioms
            | Constants       --  constants
            | Aliases         --  aliases
            | Colon           --  :
            | Turnstile       --  ⊢
            | By              --  by
            | Rule            --  rule
            | Induction       --  induction
            | On              --  on
            | All             --  all any
            | Unproved

            | Tautology       --  ⊤
            | Contradiction   --  ⊥
            | Forall          --  ∀
            | Exists          --  ∃
            | Negate          --  ¬ NOT
            | And             --  ∧ && AND
            | Or              --  ∨ || OR
            | Implication     --  ==>
            | Equivalence     --  <=>

            | Paren'Open      --  (
            | Paren'Close     --  )
            | Box'Open        --  [
            | Box'Close       --  ]
            | Bracket'Open    --  {
            | Bracket'Close   --  }

            | Underscore      --  _
            | Equal           --  =

            --  layout
            | Pipe            --  |
            | Dash            --  -----
            | Begin'Layout
            | End'Layout

            | EOF
  deriving (Show, Eq)
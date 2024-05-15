module Parser.Token where


--  TODO: DO IT!
data Token  = Ident String
            | Constant'Before

            --  keywords
            | Module
            | Comma           --  ,
            | Period          --  .
            | Schema          --  schema
            | Syntax          --  syntax
            | Judgment        --  judgment
            | Theorem         --  theorem
            | Axiom           --  axiom
            -- | Axioms          --  axioms
            | Constants       --  constants
            | Aliases         --  aliases
            | Colon           --  :
            | Turnstile       --  ⊢
            | By              --  by
            | Rule            --  rule
            | Induction       --  induction
            | On              --  on
            | All             --  all any
            | For             --  for
            | Some            --  some
            | Object          --  object / objects
            | Proposition     --  proposition / propositions
            | Unproved        --  unproved
            | Case            --  case
            | Analysis        --  analysis

            | Tautology       --  ⊤
            | Contradiction   --  ⊥
            | Forall          --  ∀
            | Exists          --  ∃
            | Negate          --  ¬ NOT
            | And             --  ∧ && AND
            | Or              --  ∨ || OR
            | Implication     --  ==>
            | Equivalence     --  <=>

            | Type'Arrow      --  ->

            | Paren'Open      --  (
            | Paren'Close     --  )
            | Box'Open        --  [
            | Box'Close       --  ]
            | Bracket'Open    --  {
            | Bracket'Close   --  }

            | Underscore      --  _
            | Equal           --  =
            | Defines         --  :=

            --  layout
            | Pipe            --  |
            | Dash            --  -----
            | Begin'Layout
            | End'Layout

            | EOF
  deriving (Show, Eq)
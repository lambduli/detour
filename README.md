# Detour

A toy proof-checker for a mix of first-order predicate and second-order propositional logic natural deduction proofs in a Fitch-style notation.


------

## TODO:
- [x] remove the substitution `Const2Term`
- [ ] maybe have a special kind of term like `Rigid` variable? I don't remember for what, though.


## TODO:
- [x] a switch `--lem=true/false` that disallows (or allows) the *proof by contradiction* rule
- [x] Lexer
- [x] Parser
- [x] the Data Type Representation
- [x] named axioms in the global scope
- [ ] ~~named sub-proofs in the global scope~~

- [ ] Proof-checking
  - [x] Unification
  - [x] `check'rule`

- [ ] Custom syntax
  - [x] parsing syntax definitions
  - [x] case analysis on objects
    - [x] exhaustivity/specificity checking
  - [ ] induction on objects

- [ ] Custom Rules
  - [x] parsing judgment definitions
  - [x] user-defined judgments
    - [x] rules
    - [ ] type-check the rule definitions (formulae in the premises and the result parts are well-formed)
    - [x] implement `check-rule` for custom rules
      - [x] the ∀-elim part
      - [x] the ==>-elim part
  - [ ] case analysis on propositions
  - [ ] induction on propositions
    - [ ] ~~check the strict positivity property~~

- [ ] Typed Stuff
  - [x] typing for terms
  - [x] type unification

- [ ] second-order features
  - [ ] theorem schemata
  - [ ] rule and judgment schemata over propositions

- [ ] ~~REPL~~
  - [ ] ~~the Console Command Mode~~

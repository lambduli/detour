# Detour

A toy proof-checker for a mix of first-order predicate and second-order propositional logic natural deduction proofs in a Fitch-style notation.


------

## TODO:
- [ ] remove the substitution `Const2Term`
- [ ] maybe have a special kind of term like `Rigid` variable? I don't remember for what, though.


## TODO:
- [ ] a switch `--lem=true/false` that disallows (or allows) the *proof by contradiction* rule
- [x] Lexer
- [x] Parser
- [x] the Data Type Representation
- [ ] named axioms in the global scope
- [ ] named sub-proofs in the global scope
- [ ] user-defined syntax
  - [ ] check the strict positivity property
- [ ] Proof-checking
  - [x] Unification
  - [ ] `check'rule`
    - [ ] induction
    - [ ] custom rules
  - [ ] second-order features
    - [ ] theorem schemas
    - [ ] rule schemas
- [ ] REPL
  - [ ] the Console Command Mode

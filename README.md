# Detour

A toy proof-checker for first-order logic natural deduction with Fitch-style notation.


------


## TODO:
- [ ] a switch `--intuitionistic` or `--classical` that disallows (or allows) the *proof by contradiction* rule
- [ ] REPL
- [ ] Lexer
- [ ] Parser
- [ ] the Data Type Representation
- [ ] the Console Command Mode


## THOUGHTS:
- [ ] if I allow the user-definition of axioms and rules, what if the user introduces an axiom that leads to inconsistency? it might be an obvious one like `false: ⊥` or it could be something more non-obvious like `false: A ∧ ¬A` or even more non-obvious like: `a: A` and also `¬a: ¬A` or even more non-obvious ...
I want to know whether that's sort of "on the user" or if I should do something to check that it's not done or even—maybe **I** should prevent that. But then, how would I prevent that and also allow to define custom rules and axioms?
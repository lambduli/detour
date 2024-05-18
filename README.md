# Detour

A toy proof-checker for first-order predicate logic natural deduction with Fitch-style notation.

It is still in the stage of prototyping.

It supports exactly first-order predicate logic with no custom rules.

## Syntax

### Axioms
You define axioms like so:
```
axiom nat-zero : ℕ(Zero)
axiom nat-suc  : ∀ n : ℕ(n) ==> ℕ(Suc(n))

axiom sum-zero : ∀ n : ℕ(n) ==> Sum(Zero , n , n)
axiom sum-suc  : ∀ n₁ n₂ n₃ : ℕ(n₁) ==>
                              ℕ(n₂) ==>
                              ℕ(n₃) ==>
                              Sum( n₁ , n₂ , n₃ ) ==> Sum( Suc(n₁) , n₂ , Suc(n₃) )
```

#### Induction
The tool does not understand induction. You have to define your own induction axioms:
```
axiom ind-sum : --  The base case.
                { ∀ n₂ : ℕ(n₂) ==> ∃ n₃ : ℕ(n₃) ∧ Sum( Zero , n₂ , n₃ ) } ==>
                --  The inductive case.
                [ ∀ n : ℕ(n) ==> { ∀ n₂ : ℕ(n₂) ==> ∃ n₃ : ℕ(n₃) ∧ Sum( n , n₂ , n₃ ) } ==> { ∀ n₂ : ℕ(n₂) ==> ∃ n₃ : ℕ(n₃) ∧ Sum( Suc(n) , n₂ , n₃ ) } ] ==>
                { ∀ n₁ : ℕ(n₁) ==> ∀ n₂ : ℕ(n₂) ==> ∃ n₃ : ℕ(n₃) ∧ Sum( n₁ , n₂ , n₃ ) }
```

### Theorems
A theorem is a statement followed by its proof.
```
theorem totality : ∀ n₁ : ℕ(n₁) ==> ∀ n₂ : ℕ(n₂) ==> ∃ n₃ : ℕ(n₃) ∧ Sum( n₁ , n₂ , n₃ )
```


### Proofs
Proofs are the most visually involved part. You start by writing the vertical and horizontal lines:
```
|
|---------------------------
|
|
|
|
```

The lines above the long horizontal line are for premises while the space below the horizontal line is for deriving new information.

Here is a simple theorem in propositional logic:
```
theorem foo : A ==> B ==> C ⊢ B ==> A ==> C
| p : A ==> B ==> C
|----------------------------------------------------------
|
| 0 : | p0 : B
|     |----------------------------------------------------
|     |
|     | 1 : | p1 : A
|     |     |----------------------------------------------
|     |     |
|     |     | b=>c : B ==> C  by rule ==>-elim on p, p1
|     |     |
|     |     | C  by rule ==>-elim on b=>c, p0
|     |
|     | A ==> C  by rule ==>-intro on 1
|
| B ==> A ==> C  by rule ==>-intro on 0
```

You have to name all your premises.
You don't have to name all the asserted statements below the line. Only those you intend to refer to.
The last one in a (sub-)proof is supposed to be proving the goal.

You can use whatever names you want. Almost all characters are allowed except some special symbols that have concrete meanings in *detour*.

See the [`./examples`](./examples) directory for a few examples.



------
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

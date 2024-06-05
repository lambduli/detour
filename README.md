# Detour

A toy proof-checker for first-order predicate logic natural deduction with Fitch-style notation.

It is still in the stage of prototyping.

It supports exactly first-order predicate logic with custom definitions for terms and propositions.

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


### Inductive Definitions
You can also define your relations more concisely using the `syntax` and `judgment` declarations.
Here's an example of the above in the new syntax:
```
syntax ℕ  = Zero
          | Suc(ℕ)

judgment sum = Sum(ℕ, ℕ, ℕ)

rule schema sum-zero for all objects (n : ℕ) :
|
|-------------------------------------- sum-zero
| Sum(Zero, n, n)


rule schema sum-suc for all objects (m : ℕ), (n : ℕ), (o : ℕ) :
| Sum(m, n, o)
|-------------------------------------- sum-suc
| Sum(Suc(m), n, Suc(o))
```


### Induction and Case Analysis
If you declare your relations (using `syntax` and `judgment`) as shown above, the tool supports proofs by induction and case analysis.
Here's an example of a theorem *total* for addition:
```
theorem total : ∀ (n₁ : ℕ) (n₂ : ℕ) : ∃ (n₃ : ℕ) : Sum( n₁ , n₂ , n₃ )
∀ (n₁ : ℕ) (n₂ : ℕ) : ∃ (n₃ : ℕ) : Sum( n₁ , n₂ , n₃ )  by induction :

  case Zero -> 
    |
    |--------------------------------------------------------------------------------------------
    | uni-n2 :  | for all (n2 : ℕ)
    |           |--------------------------------------------------------------------------------
    |           | sz : Sum( Zero , n2 , n3 )  by rule sum-zero
    |           | ∃ (n₃ : ℕ) : Sum( Zero , n2 , n₃ )  by rule ∃-intro on sz
    |
    | ∀ (n₂ : ℕ) : ∃ (n₃ : ℕ) : Sum( Zero , n₂ , n₃ )  by rule ∀-intro on uni-n2


  case Suc(m) ->  

    | induction-hypothesis : ∀ (n₂ : ℕ) : ∃ (n₃ : ℕ) : Sum( m , n₂ , n₃ )
    |--------------------------------------------------------------------------------------------
    | uni-n2b : | for all (N2 : ℕ)
    |           |--------------------------------------------------------------------------------
    |           | d1 : ∃ (n₃ : ℕ) : Sum( m , N2 , n₃ )  by rule ∀-elim on induction-hypothesis
    |           | exn3 :  | p5 : Sum( m , N2 , n3 ) for some (n3 : ℕ)
    |           |         |----------------------------------------------------------------------
    |           |         | sum-m+1 : Sum( Suc(m) , N2 , Suc(n3) )  by rule sum-suc on p5
    |           |         | ∃ (n₃ : ℕ) : Sum( Suc(m) , N2 , n₃ )  by rule ∃-intro on sum-m+1
    |           |
    |           | ∃ (n₃ : ℕ) : Sum( Suc(m) , N2 , n₃ )  by rule ∃-elim on d1, exn3
    |
    | ∀ (n₂ : ℕ) : ∃ (n₃ : ℕ) : Sum( Suc(m) , n₂ , n₃ )  by rule ∀-intro on uni-n2b
```


### Theorems
A theorem is a statement followed by its proof.
```
theorem total : ∀ (n₁ : ℕ) (n₂ : ℕ) : ∃ (n₃ : ℕ) : Sum( n₁ , n₂ , n₃ )
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


## Automated Proving
The tool now supports a somewhat automated proof search.
The goal is to focus on very interactive proving. It is not a goal to build a powerful automated theorem prover.
However, with the correct use of tactics (in the future) it maybe could be.

The theorem `total` from above now can be proved trivially:

```
theorem total : ∀ (N : ℕ) (M : ℕ) : ∃ (O : ℕ) : Sum(N, M, O)
prove ∀ (N : ℕ) (M : ℕ) : ∃ (O : ℕ) : Sum(N, M, O)
```

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
  - [x] induction on objects

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

- [ ] automated proving
  - [ ] all connectives
  - [ ] quantified formulae
  - [x] induction
  - [x] using theorems
  - [x] using local assertions

- [ ] second-order features
  - [ ] theorem schemata
  - [ ] rule and judgment schemata over propositions

- [ ] ~~REPL~~
  - [ ] ~~the Console Command Mode~~

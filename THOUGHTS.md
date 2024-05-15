# THOUGHTS


###### Inconsistent Theories
If I allow the user to define axioms and rules, what if the user introduces an axiom that leads to inconsistency?
It might be an obvious one like `false: ⊥` or it could be something more non-obvious like `false: A ∧ ¬A` or even more non-obvious like `a:` A` and also `¬a: ¬A` or even more non-obvious ...

I wonder whether that's sort of "on the user" or if I should do something to check that it's not done or even—maybe try to prevent that. But then, how would I prevent that and also allow to define custom rules and axioms with not much burden on the user?


______


###### Reflection, Case-analysis and Restriction on Rule's Conclusions

It seems that when we define some inductive syntax/type/relation there can be no axiom/rule (schema) with that relation as a result or a part of the result (conclusion).

I think the reason is roughly this: To do case analysis (or proof by reflection), we want the assurance that the object/proof derivation was constructed using only one of the ways it was defined. (That only includes those specific ways in the inductive definition of a syntax ("constructors") or a judgment ("rules").)

For example, let's assume the following:

```
inductive Nat = Zero | Suc Nat
```

This is somewhat equivalent to:

```
Nat(Zero)
∀ x Nat(x) => Nat(Suc(x))
```

except that the original one implicitly communicates that there are no other ways to construct an object that is in `Nat` relation. In that sense, the original definition also introduces an additional axiom

but the original one is more restrictive in what can then follow.

The following additional axiom(s) would not be legal in the context of the inductive definition:

```
axioms:

  Nat(α)  -- only Zero and Suc of Nat are natural numbers

  ∀ x P(x) => Nat(x)  -- P can be whatever and this can lead to proving that Nat(β) for some strange constant β
                      -- If P(x) can be proved true for terms outside the inductive framework you can infer Nat(x) without following the intended progression.

  P(β) ∨ Nat(β) -- I am not sure that `∨` is a problem on its own. But thinking of it right now, I am not sure what would happen if I proved ¬P(β). Wouldn't this lead to elimination that would just assert Nat(β)? I don't remember a rule like that, but who knows.

  ⊤ ∧ Nat(β)  -- This just directly asserts that Nat(β).

  ∃ x Nat(x)  -- Non-constructive nature: The existential quantifier implies the existence of a natural number, but it doesn't provide any information about which specific number it is. This means you cannot construct that specific number using the axioms and induction alone. You can only reason about its existence.

  ...
```
This should demonstrate why we don't want to allow those.
I think we can allow `Nat(_)` when it is on the left-hand side of the `=>`. I think that if it's on the LHS of a `=>` it is even ok if the `Nat(_)` is wrapped in `¬` or `∧` or `∨` and so on. The reason being, if its on the LHS of `=>` it's still a condition/premise of the implication/function. It is not a result. And what is more, I think it should also be ok for the `Nat(_)` to be on the RHS of an implication if it is nested on the LHS of some implication. An example:

The reasoning is, that to use this implication to prove `P` (even if it's effectively a ⊥) we would need to do modus ponens of => elimination. That means giving a proof of `X => Nat(β)`. If that is possible, well then ok (but it seems to be that something like that would not be possible). There are some formulae that would look more reasonable as axioms of this shape:

```
  ∀ x ( [ X(x) => Nat(x) ] => P(x) )

```

One can imagine that `X` is something that makes the whole thing make sense. It might be a predicate that only holds if the `x` is `Nat` or if it's `Nat` and is an even number, or something like this. Even with this somewhat incomplete example, I think it should be clear that having `Nat(_)` on the RHS of some => is ok if that whole implication is on the LHS of a top-level =>. For more intuition, see the following Agda snippet:

```agda
data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data Foo : Set where
  foo : (Nat -> Nat) -> Foo
```


So to go back to my thought—I think this shows what needs to be restricted and why.


One more addition to implications.
According the AI this might still be problematic: `∀ x Nat(x) => Foo(x)`.

> Compatibility with induction:

> This axiom is technically compatible with induction because it doesn't introduce any information about which specific values are "Nat". You can still use the base case (Nat(Zero)) and the step case (∀ n Nat(n) => Nat(Suc(n))) to prove properties about natural numbers without directly relying on this additional axiom.
> Impact on reasoning:

> However, this axiom does impact how you can reason about "Foo". It essentially states that everything that is "Nat" is also "Foo". This can have the following consequences:

> Non-constructiveness: Similar to the existential quantifier case, you can't necessarily construct a specific "Foo" element just by knowing it's also "Nat". The axiom only establishes a one-way implication.

> Proof burden: When proving a statement about "Foo", you might need to consider both cases:

> If the element is already proven to be "Nat", then you can directly use the axiom to infer it's also "Foo".
> If the element hasn't been proven to be "Nat", you can't rely on this axiom and might need independent reasoning to show it's "Foo".
> Comparison to existential quantification:

> While this axiom doesn't explicitly assert Nat(x) for any specific x, it's essentially saying that for all possible x, if it's "Nat", then it's also "Foo". This introduces a similar level of non-constructivity as the existential quantifier case, albeit in a different form.

I think the last part is talking about the impact on `Foo`.

In any case, I need to read more on this.

(More of the brainstorm with the AI at https://gemini.google.com/app/f0ea08f6daf73324)

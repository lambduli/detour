# Rules

In this file, I want to think about what is the best way to implement `syntax`, `judgment`s and *rules*.


With the `syntax` definitions, we have different-looking quantifiers:

`∀ ℕ₁ : Sum( ℕ₁ , Zero, ℕ₁ )`

and

`∃ ℕ : Sum( Zero , Zero , ℕ )`.


I was thinking of having a special representation for these. Like "typed forall" and "typed exists" in my code.





I don't think I would ever be able to express something like this:

```
judgment A ≡ B for all propositions A, B

rule schema typed-forall for all propositions P, G :  | ∀ x : P(x) ==> G[x]
                                                      |------------------------ typed-forall
                                                      | ∀ P₁ : G[x -> P₁]

```

For that reason, I think it would be useful if there's some facility to do the above as a language feature.


#### Solution
I have a solution for this!!!
When I define `ℕ` using the `syntax` form I can not use `ℕ` as a relation, like `ℕ(x)`.
Then there's no reason to go between the two. Only one of them is possible.






## Type-checking

So, how do I do type-checking?

So I was thinking this. When I introduce a typed explicit universal variable, I keep its type in an environment.
When I need to unify that object-variable with some term I produce a type-constraint unifying their types.

This way, when I am doing the implicit ∀-elimination on rules and introducing implicit universal variables or unifying those with terms, I will always keep the types.






## Representation

Maybe I could have only one representation for *forall* and *exists*. When I don't know what the "type" of that variable is, I just invent a new type meta-variable.


I am also thinking about changing the syntax a bit.

`∀ (n₁ : ℕ) : Sum( n₁ , Zero, n₁ )` for the typed variant and `∀ x : Id( x , x )` for the untyped one.

This makes sense to me, intuitively. I will have to investigate a bit more.

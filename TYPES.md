# Implementing Types


Here's the thing.
When I do the usual proof-checking, I invent new object-level free-vars for unification purposes.
Now, those will be typed. Some of them might have an unknown type. That should be equal to saying that a certain ∀ or ∃ quantify over the whole domain.


It is kinda interesting how here, unknown type means *all the objects* and not, *objects of one certain type*.
I hope this doesn't cause issues.


Because I invent new free-vars during the process of checking, I don't really have a way to get them into an environment.
I could get them into a state, but I don't think that's the best idea.

I am worried that, in some cases, those free-vars can get unified with something in such a way that they end up being a part of the substitution and get put somewhere, where I won't be able to resolve them within the local environment.

I need to investigate all those cases.
I need to start with, what are all the places where I introduce a new free-var and whether it could happen that they could get "captured" or "spread" somewhere else.
I can run the unification in a local environment where those new free-vars have meaning, but that means that they can't end up being present in the resulting substitution, which they could.


Example:

- rule ∃-intro

When checking a justification by rule ∃-intro I have some formula like `P(α)` and I have a quantified formula like
`∃ a : P(a)`. I check that those match by inventing a new unification variable for `a`, instantiating the existential formula with it and trying to unify it with its supposed instantiation.
This, however, can lead to `α` ending up in the substitution. Here's an example.


| p : P(α, α)  by ...
|
| ∃ a : P(a, α)  by rule ∃-intro on p


The `a` becomes some `_0`. The `_0` is then unified with `α` and we get a substitution `α -> _0`. That's bad.
We would have to register `_0` in the typing environment so that its type is known.



## Typed vs Untyped Logic

Could there be a conflict because of the untyped part of the language?

Is it possible that some untyped part would allow two variables of two different types but the untyped part would require them to be of the same type?

It almost seems like that might not be possible.
When we have untyped universals like `∀ x y : P(x, y)` then it will be typed like this:

`∀ (τ₁ : Type) (τ₂ : Type) . ∀ (x:τ₁) (y:τ₂) : P(x, y)`

This means that each "untyped" variable will have its own type after instantiation.
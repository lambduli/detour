# Correspondence between the Detour Proof System and a Programming Language/Type System

I have syntax declarations:

```
syntax:

ℕ = Zero
  | Suc ℕ
```

This means the following logical relation:

```
ℕ(Zero)

∀ n ℕ(n) => Ν(Suc(n))
```


It also means the following definition in the "inference-rule" style (Fitch-style notation):

```
proposition ℕ(_):

|
|--------------------- nat-zero
| ℕ(Zero)

| ℕ(n)
|--------------------- nat-suc
| ℕ(Suc(n))
```

As a note, the second one is a rule schema, to be precise.


It also corresponds to the following Agda-style data type:

```agda
data ℕ : Set where
  Zero : ℕ
  Suc : ℕ -> ℕ
```

The first, third, and fourth definitions have something that the second one does not necessarily have.
They explicitly state that the constants `Zero` and `Suc` are the only way to construct an object of type ℕ.

At least that's what it seems like to me.
It also seems to me that because I can write `∀ m n ℕ(m) => ℕ(n) => ℕ(m + n)` I would have to somehow
make it explicit, that `+` is not a third option to create an object of type ℕ.
I think this is explicitly introduced in the axiom of induction. That one only mentions cases for `Zero` and for `Suc(n)`.
This should mean that `+` is defined in terms of these two.





## Interpreted Functions using λ-calculus Notation
I was thinking what if we allow the definition of interpreted functions
(the ones that would usually be normal functions in languages like Agda) and keep the uninterpreted notion of a function
only for constructors?

I would have something like this:

```
syntax:

ℕ = zero
  | suc ℕ


∀ m n ℕ(m) => ℕ(n) => ℕ(m + n)

+ = λ m n ->  case m of
                zero -> n
                suc m -> suc (m + n)
```

First, I would have to be able to type check that this definition is correct
and also do a termination check. The termination check might be tricky.

But this function uses pretty standard recursion.
I might be able to constrict the case analysis in such functions
so that it won't allow patterns like `suc zero` or `suc (suc `m)` to make things simple.
It would then amount to a pretty standard inductive reasoning.

I would understand the definition above like this:
I am claiming that for every `m` such that `ℕ(m)` the proposition `∀ n ℕ(m) => ℕ(n) => ℕ(m + n)` holds.
This can be proven by induction. I have to prove that for `m` equal `zero` it holds and I have to prove
it for `m` equal to `suc n` for any `n` it holds.

This can be **proven** only if we have a definition of `+`. If we don't interpret the `+` function
then we can only **assume** that it's valid, we consider it an "axiom".

If we have the definition of the function we can use the function itself to show that the proposition holds.
The function is defined in such a way, that it is actually an inductive proof of the formula.

This gives a sort of "proof by definition" vibes.

It is fair to note that the lambda expression is a proof of that proposition in the sense that the function
uses a proof by induction to show that for all natural numbers it returns a natural number.

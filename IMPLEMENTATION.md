# IMPLEMENTATION

I have theorems/lemmas. Those consist of a statement and its proof.

```
theorem modus-ponens: A, A ==> B ⊢ B .
_ : | a: A
    | a->b: A ==> B
    |-----------------------------
    |
    | b: B  by ==>-elim on a->b, a
    |
    _: B by b
```

We assume here that `A` and `B` are specific propositions and not meta-variables.

To check that the derivation is a valid proof for the statement I traverse the derivation sequentially, from top to the bottom. The top-most sub-proof must have corresponding assumptions, of course, and its consequence must correspond to the original statement's consequence.

The body of the proof must be a sequence of "declarations" called *assumptions*.
Each assumption states that a certain object with a specified name (or an anonymous object in case of `_`) is a proof of a certain proposition. The justification of that is given after the `by` keyword.

```
b: B by ...
```


## Checking the Justifications

I am thinking the following, the unification might not be necessary until I have meta-variables.

But let's think with meta-variables right from the beginning. This way I can later do therem-schemas and proof-schemas and I can soon do axiom and rule schemas and have a sort of pseudo-higher-order level.

The question is—do I treat the proofs almost as a "functional language" and do I type-check it in the similar way or do I treat it more like logic-language and use unification way more? I need to figure that out.

So here's a messed up derivation, I think.

```
theorem messed-up : Foo(α, β, λ)
                  , ...
_ : | p1 : Foo(α, β, λ)
    |--------------------
    |
    | _ : | all a
    |     |-------------------
    |     |
    |     | foo : Foo(a, a, λ)  by p1
    |     | -- this should fail, `a` is a universal variable
    |     | -- it cannot unify with two constants at once
    |     |
    |
```

Another case of a messed up derivation:

```
theorem messed-up : ∀ a ∀ b Foo(a, a, b)
                            Bar(σ, φ)
                            Baz(η, η)
                  , ...
                  ⊢ ...
_ : | p1 : ∀ a ∀ b Foo(a, a, b)
    | p2 : Bar(σ, φ)
    | p3 : Baz(η, η)
    |--------------------
    |
    | foo : Foo(α, β, λ)  by ∀-elim on p1
    | -- the deal is, α and β are the same thing now; they should have been unified
    |
    | -- I am allowed to do this:
    | foo-∃ : ∃ α ∃ β ∃ λ Foo(α, β, λ)  by ∃-intro on foo
    | -- I think I could have also introduced the lambda as a universal variable
    | -- and then derive ∃ α ∃ β ∀ λ Foo(α, β, λ) ; but that doesn't matter
    |
    |
    |
    | -- what I want to demonstrate is this:
    | bar1 : Bar(α, β)  by p2   -- this should fail
    | -- α and β are two "constants", they have been introduced by ∀-elim, so they are fairly flexible
    | -- for example, it should be ok to do this:
    | baz : Baz(α, β)  by p3
    | -- simply, because they can be pretty much anything, so there's no reason for them to not be specifically η
    |
    | -- but, they are still unified together, so we can not unify α with σ and β with φ
    | -- that won't work
    |
```


But this raises a question—should I allow things like `Baz(α, β)` from above being justified by `Baz(η, η)`?
I don't necessarily see a problem with it. Both `α` and `β` came as instantiations of a universal proposition.
We are allowed to think of them as a specific object (or rather names for a specific object/objects). In this sense, it should be fine to unify them with a constant. In a Hindley-Milner Inference sort-of terms, I think of these two as fresh meta-variables when they are introduced. They are allowed to unify with constants and other meta-variables. That's fine.

Just for the sake of the argument. If I wouldn't want to allow things like these, would I still be able to do something similar using only the strict notions?

What is it even the thing that I am attempting above? I don't know. The thing above is fairly artificial.
I am thinking whether maybe some more "real-world" example would demonstrate? Maybe the proof of totality?

______


So, now again, if I am very explicit and I don't have implicitly quantified rules, can I do what is above?

```
theorem messed-up : Foo(α, β, λ)
                  , ...
_ : | p1 : Foo(α, β, λ)
    |--------------------
    |
    | _ : | all a
    |     |-------------------
    |     |
    |     | foo : Foo(a, a, λ)  by p1
    |     | -- this should fail, `a` is a universal variable
    |     | -- it cannot unify with two constants at once
    |     |
    |
```

This is now illegal. And below is an explanation of why.

______


So I am thinking this—here's what's OK:

- unifying explicitly introduced universal variable with some other universal variable when using ∀-elim
- unifying implicit universal with an explicit universal (I do this when the justification features the same universal variable twice and I ∀-elim it using two variables, one implicit and the other explicit)
- ?

What is not OK:

- unifying explit universal variable with "explicit" existential variable (in the sub-proof used for ∃-elim) [because this one is actually a constant]
- unifying explicit and implicit universal variable with a constant

The above would lead to something like claiming that some proposition P holds for every object justified by showing that it holds for some specific object. Here's an example:

```
| all a
|----------------
| f : Foo(α, β)  by rule repetition on ...  -- just to show that somewhere there's a derivation
|                                           -- claiming Foo(α, β) for those two constants
| _ : Foo(a, β)  by f                       -- this justification wouldn't make sense
|                                           -- I can use the claim that Foo(α, β) for some two constants
|                                           -- to justify that it holds for a universal variable.
|                                           -- Even if I didn't disallow it at this point, this sub-proof
|                                           -- can never be used for ∀-intro. It could claim things like:
|                                           -- ∀ a Foo(a, β) and that's wrong.

```

So this rules out of the problematic derivations from way above.

Here's the second one:

```
theorem messed-up : ∀ a ∀ b Foo(a, a, b)
                            Bar(σ, φ)
                            Baz(η, η)
                  , ...
                  ⊢ ...
_ : | p1 : ∀ a ∀ b Foo(a, a, b)
    | p2 : Bar(σ, φ)
    | p3 : Baz(η, η)
    |--------------------
    |
    | foo : Foo(α, β, λ)  by ∀-elim on p1
    | -- the deal is, α and β are the same thing now; they should have been unified
    |
    | -- I am allowed to do this:
    | foo-∃ : ∃ α ∃ β ∃ λ Foo(α, β, λ)  by ∃-intro on foo
    | -- I think I could have also introduced the lambda as a universal variable
    | -- and then derive ∃ α ∃ β ∀ λ Foo(α, β, λ) ; but that doesn't matter
    |
    |
    | -- what I want to demonstrate is this:
    | bar1 : Bar(α, β)  by p2   -- this will fail
    |                           -- α is implicit universal
    |                           -- as such, it can not unify (when justifying) with a constant σ
    |
    | -- α and β are two "constants", they have been introduced by ∀-elim, so they are fairly flexible
    | -- for example, it should be ok to do this:
    | baz : Baz(α, β)  by p3
    | -- simply, because they can be pretty much anything, so there's no reason for them to not be specifically η
    |
    | -- but, they are still unified together, so we can not unify α with σ and β with φ
    | -- that won't work
    |
```

The example above shows that I could, in theory, forbid unifying an implicit universal with constants.
This would prevent the "bar1" situation even before we would realize that α and β are the same thing and as such they can not each unify with a different constant.

However, the `baz` shows that it could perhaps be useful to think of the implicit universals as "flexible aliases" to constants. In a way, it seems to me that we can think of those implicit universals as constants. This is exemplified by the fact that when we do ∀-elim, we can instantiate it with any other term aside from just variables. And terms are, in fact, constants. But again, however, we could observe that treating the implicit universal variables as sort-of flexible constant aliases would allow us to treat α and β as an alias to η. They would all become the same constant referred to by different names.


So I am still thinking whether I need unification or rather some simple form of putting things equal to each other.
I think I need to consider that sometimes instead of variables, I will be dealing with "complicated" terms featuring not only variables.

This will make the "simple form of putting things equal" somewhat equivalent to unification, I think.




Here's what I am not sure whether it's OK:

- unifying explicit universal with another explicit universal
- unifying implicit universal with a constant

I just covered the second point above. I suppose it could be useful. The implicit universal would be treated as a sort of flexible variable until it becomes bound to a constant. Then it would become sort of an alias to that constant, so it would become sort of a constant itself.


As for the first one, here's an example:

```
_ : | p1 : ∀ a Id(a, a)
    |----------------------
    |
    | a : | all α
    |     |-----------------
    |     |
    |     | b : | all β
    |     |     |-------------
    |     |     |
    |     |     | _ : Id(α, β)  by rule ∀-elim on p1
    |     |     | -- but if I do this, I can misuse it like this:
    |     |
    |     | _ : ∀ b Id(α, b)  by rule ∀-intro on b
    |
    | _ : ∀ a ∀ b Id(a, b)  by rule ∀-intro on a
    |
```

This is no good.






There are certain distinctions between what cen be done with those explicit variables and what can be done with those implicit variables. Perhaps, implicits should not be treated as variables but rather as terms/constants.
When we have implicit universal after ∀-elim that term (variable) can, in fact, also be any term we like. So it's not really the same as a variable.

When we do explicit universal, because we want to do ∀-intro in the future, that variable should really not become unified with any other term/constant. Now it seems that it should also not be unified with other universal variables because that could lead to incorrect claims as shown above.

The question is—is it ok for explicit universal variable to be used as a (implicit) term when doing ∀-elim? I think that my proof of totality very much depends on it. Regardless, I need to re-think it and make sure that it sounds valid.

I am thinking that maybe those explicitly declared universal variables should be considered sort-of constants. This will prevent me from unifying them with anything specific—that would be bad for the future ∀-introduction. It will allow me to use those "sort-of constants" when eliminating some universally quantified proposition. But it will prevent me from doing the thing above. To be more specific, the thing above would be rejected because α and β are two different "sort-of constants" and as such they can't unify together, which they would, because of the way ∀ a Id(a, a) is instantiated.

When it comes to implicitly introduced variables during ∀-elimination, I think it is ok to instantiate those universally bound variables with any term. That means, constants/general terms are ok as well as those explicitly introduced universal variables—as those are considered constants themselves. If we write a fresh variable at the place of the bound variable (in the formula before the ∀-elimination) I think we can consider that to be an implicitly introduced variable. This one can not be used for ∀-introduction, because it has not been introduced explicitly. It can, however, stand for something that we do not care about and eventually go out of scope. It can also be unified with some constant—I think that this is also ok.

Here's a short relevant part of that proof:

```
| N2 :  | all ℕ₂
|       |----------------
|       |
|       | -- [[ Now, I need to prove the base case. ]]
|       |
|       | sz : ∀ ℕ Sum( Z , ℕ , ℕ )  by rule sum-z
|       | sum23 : Sum( Z , ℕ₂ , ℕ₃ )  by rule ∀-elim on sz
|       | base : ∃ ℕ₃ Sum( Z , ℕ₂ , ℕ₃ )  by rule ∃-intro sum23
|       |
```
Clearly it's ok for the line with `sum23` to do ∀-elim in such a way that it introduces ℕ₃ implicitly. In the light of the discussion above, this ℕ₃ is now a term/constant. It should not be seen as a universal variable.

That being put aside, it also seems ok to instantiate the universal being eliminated with our explicitly declared universal variable ℕ₂. Otherwise we would not really be able to do one of the most simple things—taking a forall, eliminating it and re-introducing it.

```
| p1: ∀ a P(a)
|-------------------
|
| α : | all α
|     |---------------
|     |
|     | _ : P(α)  by rule ∀-elim on p1
|
| _ : ∀ a P(a)  by rule ∀-intro on α
|
```

The above should be doable and can only be doable if it's ok to instantiate a forall-being-eliminated with the explicit universal variable in the scope.

As I have explained above—I think that it is ok.



I am now thinking about reordering. Can I reorder two universals?

```
| p1 : ∀ x ∀ y P(x, y)
|-------------------------------
|
| α : | all α
|     |-------------------------
|     |
|     | β : | all β
|     |     |-------------------
|     |     |
|     |     | _ : P(β, α)  by rule ∀-elim on p1
|     |
|     | _ : ∀ x P(x, α)  by rule ∀-intro on β
|
| _ : ∀ y ∀ x P(x, y)  by rule ∀-intro on α
```

Of course I can do reorder. This makes sense and I should have seen it right away not only after I have started writing it down.






There's one thing that I haven't dealt with yet.
When I have `∀ ℕ P(ℕ)` I actually have `∀ x ℕ(x) => P(x)`. At least I think that's what we mean.

The engine can see that from the use of the specific identifiers for the bounds variables.
It can often also see it from the way the judgements are defined.

One of the reasons why I am thinking about it is induction. The induction does not really provide proofs of things like `∀ x P(x)` but rather `∀ x ℕ(x) => P(x)`. That is, the object must be a natural number for the proposition to be correct.

If I have more types of objects in the system (defined by the user) I need to consider this.

What I mean is, when I have something like `∀ ℕ P(ℕ)` I can only instantiate it so that ℕ becomes a term `τ` for which it holds that `ℕ(τ)`. So there's a little bit of type-checking going on. I think we might be able to just deal with it using unification. If you give me some term, I see if I can check one of those two patterns against it. If the term is a variable, or it contains a variable like `α` or `s(s(s(β)))`, I need to record somewhere that this variable is of specific type. I need to do this so that I can't later come and try to generalize it as a variable of a completely different type or so that I don't try to unify it with a term or a variable of a different type.

This is going to be interesting.






How do I deal with unification and keeping track of what variable is unified with what?

So any time I introduce a variable (implicitly through ∀-elim) I track it in the environment.
When I introduce a new universal I also track it in the environment.

The way I track those is simple—each identifier is assigned a term.
Those explicit universal variables are assigned a unique constant and all the implicit universals are assigned a fresh unification-variable.

When I unify two terms I get a unifying substitution. I apply it to the environment.
This can lead to some of those variables to "become" a specific (ground) term.
In some cases, it might lead to only parts of the terms assigned to them to be narrowed down.
That's how it should work.


One nice thing about this is that I can parse many things as variables even though they will not be treated as variables semantically.
One example is ∃-elim. When I do ∃-elim, like `_ : P(α, β)  by ∃-elim on ...` I can parse both α and β as variables even though, semantically, they will be treated as new constants.
The correct semantics is assured by the checker. It "interprets" the ∃-elim so that those two variables α and β are assigned up to two unique constants (maybe the justification relies on ∃ a P(a, a), then it would be just one and the same constant). This way they can't unify with anything beside fresh unification-variables (implicit universals).

This way it is ok if the α or β are already in the scope, introduced implicitly by some ∀-elim. That implicit universal gets unified with that unique constant.



I think the unification will work similarly as in my HM inference type-checker.
The function that unifies two terms produces a unifying substitution and I apply that substitution to the environment.

Here's how it works for the variables that are already unified with something.
Whenever I need to unify anything with a variable from the language I need to do a lookup in the environment. There will always be some term associated with the "actual" variable.

So maybe I should clarify. I have Terms and meta-variables participating in the unification.
The key in the scope is the actual variable. The actual variable can be assigned a term, in the environment or it can be assigned a meta variable, if the actual variable plays a role of a universal variable (implicit) and hasn't been unified with anything.

So when I am unifying terms the variables in the terms always refer to the ones registered in the environment. The meta-variables don't have names, they can't be directly refered to. They are just slots. They are a way for me to express that some actual variable can be anything and it is ok to unify it with one concrete term.

I like this. It makes sense to me.

So when I am unifying a variable and something (two terms), the variable is an actual-variable. This means that I first need to lookup what it is associated with and unify with accordance to that.
If it is associated with a meta-variable, basically meaning it's not associated with anything, I just unify the two.
If it is associated with a term I unify those two terms instead and if it succeeds the unifying substitution will take care of the smaller parts and so on.

The situations where two or more actual-variables are unified together but it's still unknown to what they are, and then something is unified with one of them this situation is actually simple. The situation at the beginning is represented by all of those keys in the environment being associated to the same meta-variable. When one of them is unified with anything concrete, the unifying substitution for the meta-variable being replaced with that concrete thing is generated and is applied to the environment. This leads to that concrete thing being associated with all the original actual-variables.


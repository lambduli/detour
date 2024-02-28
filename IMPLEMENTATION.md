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


## SYNTAX

```
judgment ≡(A, B) for any proposition A, B:

rule schema eq-not-and for any proposition A, B : |
                                                  |-------------------------
                                                  | ≡( ¬(A ∧ B) , ¬A ∨ ¬B )
```

However, the judgment definition can serve as a sort of a binder.
So I could make it so that A and B are propositional meta-variables
in the scope of any rule of this judgment.
The (explicit) above would still be possible. It would be another local binder.


-------------------------------------------------------------------------------

```
judgment ℕ(o) for any object o:

rule nat-z: |
            |------
            | ℕ( Z )
```

I can also write the rule name behind the line, they must be the same name.

```
rule nat-z: |
            |--------- nat-z
            | ℕ( Z )
```

```
rule schema nat-s for any object x: | ℕ( x )
                                    |--------- nat-s
                                    | ℕ( S(x) )
```

I guess, repeating the part "for any object x"
is a bit redundant. It is obvious from the judgment definition
that it must be an object. So maybe I can leave it out.

```
rule schema nat-s:  | ℕ( x )
                    |--------- nat-s
                    | ℕ( S(x) )
```

-------------------------------------------------------------------------------

```
judgment Sum( ℕ , ℕ , ℕ ):
```

This can be read as a shorthand for the following:
judgment Sum(x, y, z) for any object x, y, z such that ℕ(x), ℕ(y), ℕ(z):

I could make it so that this explicit form is also legal.

```
rule schema sum-z:  |
                    |------------------- sum-z
                    | Sum( Z , ℕ , ℕ )
```

Technically, I can write the above explicitly like this:

```
rule schema sum-z for any object n such that ℕ(n):  |
                                                    |------------------- sum-z
                                                    | Sum( Z , n , n )
```

```
rule schema sum-s:  | Sum( ℕ₁ , ℕ₂ , ℕ₃ )
                    |--------------------------- sum-s
                    | Sum( S(ℕ₁) , ℕ₂ , S(ℕ₃) )
```

I can write this explicitly too, but I won't.


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

The (first-order) theorem schemas over objects are fine.
Can we have this second-order for theorems too?
Something like:

```
theorem schema nnf-¬∧ for any proposition A, B: ¬(A ∧ B)
                                              ⊢ ¬A ∨ ¬B
_ : | p: ¬(A ∧ B)
    |--------------------------------------------
    | --  How do we prove something like this?
    | --  I am thinking by case analysis on the truthiness of the A and B.
    |
    | --  I need to prove that for both cases (A holds) (¬A holds)
    | --  the `¬A ∨ ¬B` will have the same logical valuation as the ¬(A ∧ B).
    | --
    | __  : | "A holds"
    |       |------------------------------------
    |       |
    |       | b :   | "B holds"
    |       |       |------------------------------
    |       |       |
    |       |       | _ : ¬(A ∧ B) doesn't hold  by valuation/interpretation
    |       |       | _ : ¬A ∨ ¬B doesn't hold  by valuation/interpretation
    |       |
    |       |   : | "¬B holds"
    |       |       |----------------------------
    |       |       |
    |       |       | _ : ¬(A ∧ B) holds  by valuation/interpretation
    |       |       | _ : ¬A ∨ ¬B holds  by valuation/interpretation
    |       |
    |       | _ : ¬A ∨ ¬B  by case analysis on truth valuation of B on 
    |
    |
    | __  : | "¬A holds"
    |       |------------------------------------
    |       |
    |       |
    |
    | _ : ¬A ∨ ¬B  by case analysis on truth valuation of A, B on ...
```

Or maybe a proof "by truth table"?



-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

```
judgment AND(A, B) for any proposition A, B:

rule schema and-intro for any proposition A, B: | A
                                                | B
                                                |------------ and-intro
                                                | AND(A, B)
```

Do I need to define the elimination rule for AND too?
I think I might not need to, I would just do a case analysis on the
proof of AND(A, B), used the rule and-intro as a single option
(or I would do `by inversion`)
and I would obtain A and B.
This seems to work nicely because of the implicit understanding
that the premises are all in "conjunction".



```
judgment OR(A, B) for any proposition A, B:

rule schema or-intro-l for any proposition A, B:  | A
                                                  |----------- or-intro-l
                                                  | OR(A, B)

rule schema or-intro-r for any proposition A, B:  | B
                                                  |----------- or-intro-r
                                                  | OR(A, B)
```

And again, to eliminate this, we use case analysis.


This brings me to the point of the example above.
It seems that at some point (when I implement custom rules and rule schemas and case analysis)
I will be able to stop using the built-in rules for first-order predicate logic
and define my own connectives and their rules.


The questions that remains—what should the case analysis look like?

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

```
theorem __  : ∀ n ℕ(S(n)) ==> ℕ(n)
α : | any α
    |----------------------------------
    |
    | sub-proof : | p1 : ℕ(S(α))
    |             |--------------------
    |             |
    |             | ℕ(α)  by inversion of rule sum-s on p1
    |             |
    |             | -- alternatively, we would need to do full case analysis
    |             |
    |             | ℕ(α)  by case analysis on p1 :  | ℕ( S(α) )
    |             |                                 |------------------------ sum-s
    |             |                                 |
    |             |                                 | ℕ( α )
    |
    | ℕ(S(α)) ==> ℕ(α)  by ==>-intro on sub-proof

∀ n ℕ(S(n)) ==> ℕ(n)  by rule ∀-intro on α
```

I like the proof above quite a bit.

There is one aspect that I want to discuss.
The theorem is an implication and not the usual logical consequence statement.
This allows me to quantify over the n explicitly.

If I have written it as a statement about logical consequence:

```
theorem __  : ∀ n ℕ(S(n)) ⊢ ℕ(n)
```

it wouldn't really make sense to use the ∀ n.
So I would have to do something like:

```
theorem __  : ℕ(S(n)) ⊢ ℕ(n)
```

and leave the n to be quantified implicitly.
It would make sense to mean universal quantification for the implicit variables.


It might make sense to also allow more explicit form:

```
theorem __ for any object n : ℕ(S(n)) ⊢ ℕ(n)
```



There's one more thing.
What about theorem like this:

```
theorem __  : S(n) ⊢ ℕ(n)
```

The deal is—the premise is not a proposition/formula.
It is an object.
I suppose this could be useful for some sort of auxiliary theorems/lemmas
where in the main proof I have a variable unified with S(n) or maybe even S(n) directly
and I need to sort of "hide" the details of proving the conclusion.

I don't really know how to make it a "proper" theorem in the logic.
I don't know whether that is a problem or not.

SASyLF does not allow that. I don't know why I thought it does.



So how would I write totality as a statemtn of a logical consequence
with the implicit quantification?
Can I even do that?
Do I even want to do that? Is it useful for anything?

```
theorem totality : ∃ ℕ₃ Sum( ℕ₁ , ℕ₂ , ℕ₃ )
```

Or rather explicitly:

```
theorem totality for any object ℕ₁, ℕ₂ such that ℕ(ℕ₁), ℕ(ℕ₂) : ∃ ℕ₃ Sum( ℕ₁ , ℕ₂ , ℕ₃ )
```

Well, if nothing else, I can use it a little bit more straightforwardly
if it's a logical consequence.
`Sum(m , n, o)  by theorem totality on m, n`

The issue is, it seems that there would need to be some sort of implicit
instantiation of the ∃ ℕ₃.

I don't know if I like this.



_____

So now, I can do the following:

```
theorem schema modus-ponens for any proposition A, B : A, A ==> B ⊢ B .
```


--------------------

I think I am starting to understand why there's `syntax` section separate from judgments.

Using syntax we define the theory. The judgments serve to reason about that theory in a meta-theoretical way/level.

That's probably why in SASyLF we don't have judgments over judgments. Judgments are supposed to reason about propositions from the theory.


So this raises a question. Can my framework handle judgments over judgments?

```
syntax:

ℕ = Z
  | S ℕ

--  Is implicitly understood as:

inductive proposition ℕ:
  axiom nat-z : ℕ(Z)
  axiom nat-s : ∀ n ℕ(n) => ℕ(S(n))

--  So we get induction just fine.


--  To the point.
judgment Sum(ℕ₁, ℕ₂, ℕ₃):

rule schema sum-z:  |
                    |------------------- sum-z
                    | Sum( Z , ℕ , ℕ )

rule schema sum-s:  | Sum( ℕ₁ , ℕ₂ , ℕ₃ )
                    |--------------------------- sum-s
                    | Sum( S(ℕ₁) , ℕ₂ , S(ℕ₃) )


--  Can I now do something like this:

judgment Same(Sum, Sum):

rule schema same: | Sum(ℕ₁, ℕ₂, ℕ₃)
                  | Sum(ℕ₄, ℕ₅, ℕ₃)
                  |----------------------------------------- same
                  | Same(Sum(ℕ₁, ℕ₂, ℕ₃), Sum(ℕ₄, ℕ₅, ℕ₃))
```

I think I can see how this would not make much sense.

It is an interesting thought, however. But it doesn't seem to be making sense.


------

There's another.

Suppose that I want to have a theory where there are numbers and also objects/terms that represent addition.

So I put the `Sum(ℕ, ℕ, ℕ)` at the syntax level.

I can then have a judgment outside the language/theory about the addition.
I would have the usual `Sum(ℕ, ℕ, ℕ)` and would use it as a basis for the evaluation semantics.

That's what I did in SASyLF.



However, this raises another interesting question.
What if I express, in the language/syntax, the notion of reductions?

What I mean is—the language doesn't have just numbers and two operations. It now has another operator "single-step-arrow" `-->` that relates two arithmetic expressions. We wan't to make sure that it always relates them in a correct way.

I need to make a judgment for that step and I would use that judgment as a basis for how the expression `AE --> AE'` is evaluated.


This is an interesting thought. We can keep adding constructs to the language that make it a different language. From a language of arithmetics to the language for reasoning about arithmetics. The interesting part is that it doesn't seem to require much more work. We use the judgments we originally defined for reasoning at the meta level as a basis for the evaluation of the in-language constructs/expressions.



-------

## Checking SCHEMATA

How do I deal with rule schemata and perhaps theorem schemata?

Let's take it one by one.


A rule schema for a proposition/syntax:

```
rule schema nat-s for any object x: | ℕ( x )
                                    |------------ nat-s
                                    | ℕ( S(x) )
```

How do I deal with this?
It seems to me that it should be pretty straightforward.
I know that the `x` is universally quantified.
So I can use this rule to justify `ℕ(S(x))` for `x` being a specific term,
also `x` being an implicit universal variable (now introduced or already present),
also `x` being an explicit universal variable (they are effectively constants),
when given `ℕ(x)`.

In a way, this works like a ∀-elim together with ==>-elim.



A second-order rule schema for a judgment:

```
judgment A ≡ B for any proposition A, B:

rule schema de-morgan-1 for any proposition A, B :  |
                                                    |--------------------- de-morgan-1
                                                    | ¬(A ∨ B) ≡ ¬A ∧ ¬B

rule schema de-morgan-2 for any proposition A, B :  |
                                                    |--------------------- de-morgan-2
                                                    | ¬(A ∧ B) ≡ ¬A ∨ ¬B

rule schema equivalence-1 for any proposition A, B :  | A ≡ B
                                                      | A
                                                      |----------- equivalence-1
                                                      | B

rule schema equivalence-2 for any proposition A, B :  | A ≡ B
                                                      | A
                                                      |----------- equivalence-2
                                                      | B


```

To use these as `by rule de-morgan-1 on _, _` we need to perform a little bit more complicate unification. Here is a little bit more complete example:

```
...

-- we must prove `¬X(a, b) ∧ ¬Y(g, h)`

p1 : ¬(X(a, b) ∨ Y(g, h))  by repetition on ... -- it was proven somehow

p2 : ¬(X(a, b) ∨ Y(g, h)) ≡ ¬X(a, b) ∧ ¬Y(g, h)  by rule de-morgan-1 for X(a, b), Y(g, h)
--  maybe I don't even need the `for ...` part?

--  and here is the unrelated, but interesting part

con : ¬X(a, b) ∧ ¬Y(g, h)  by rule equivalence-1 on p2, p1

--  here comes the coolest part
--  what if this theorem is supposed to prove some more complicated formula
--  that contains `¬X(a, b) ∧ ¬Y(g, h)` somewhere in it
--  we don't want to prove `¬X(a, b) ∧ ¬Y(g, h)` directly
--  or rather we don't want to prove the conclusion directly
--  we can use the substitution

con' : ¬X(a, b) ∧ ¬Y(g, h)  by substituting p1 for ¬X(a, b) ∧ ¬Y(g, h) using p2
-- this might not read the right way
-- so maybe
-- ¬X(a, b) ∧ ¬Y(g, h)  by substitution on p1 using p2


--  this works for more complicated formulae as well

proven : [¬(X(a, b) ∨ Y(g, h))] ==> [¬(X(a, b) ∨ Y(g, h))]  by ...

con'' : [¬X(a, b) ∧ ¬Y(g, h)] ==> [¬X(a, b) ∧ ¬Y(g, h)]  by substituting p1 for ¬X(a, b) ∧ ¬Y(g, h) using p2

-- so with the alternative syntax this would be
-- [¬X(a, b) ∧ ¬Y(g, h)] ==> [¬X(a, b) ∧ ¬Y(g, h)] substitution on proven using p2

```

**The unification part**
This is the main topic of this example.
As far as I can tell, if I only do syntactic unification, I can go even higher than just secon-order. It will still be decidable. I think this might be what the *Sireum Logika* documentation means when they say they consider propositions and function as uninterpreted. This makes dealing with the unification much easier.

So I think I will be able to allow theorem schemata abstracting over some propositions too.



**The substitution part**
The justification by substitution replaces all the proofs of the substituted sub-formula for the `p1` in the claim. That is, if the proof of equivalence `p2` is valid and in the shape of "<whatever p1 claims> ≡ <the formula>" or "<the formula> ≡ <whatever p1 claims>".

I could make it work for both cases. Alternatively, I could say that it only works on one direction and rely on the inference rule deriving the symmetry of equivalence. That is also ok.



A second-order theorem schema for a:

```
theorem schema something for proposition A, B : A ≡ B
                                              , A(α)
                                              ⊢ B(α)
| p1 : A ≡ B
| p2 : A(α)
|---------------------
|
| B(α)  by substitution on p2 using p1
| -- NOTE: This should work. A ≡ B says they are the same on all arguments.
```

This might be straightforward. I am not sure yet.
It seems that I just must make sure that it is consistent with the theory.

Then, I just substitute the name of the predicate/function in the proven part with the other side of the equivalence. I think that the engine should identify which part needs to be replaced with the other side of the equvalence on its on. That would make sense.

How do I implement it?
Maybe, I try to unify the proven and the claim and when I can't unify two things (only then) I see whether I can use the equivalence (in any direction) to make them unify.
In sucha a case, the two things (that wouldn't unify before) must be exactly equal to those two things in the equivalence (up to α-renaming, I think).

This means I can use the substitution to justify things like:

```
proven : A ∧ ¬B ==> ¬B ∨ A  by ...

eq : A ≡ B

conclusion : B ∧ ¬A ==> ¬A ∨ B  by substitution on proven using eq
```

I think this makes sense. The equivalence allows me to replace `A` with `B` and `B` with `A` wherever I need. That is my understanding.


------

```
proposition ℕ(o) for any object o:

rule nat-z: |
            |------
            | ℕ( Z )
```

Alternatively, I could embrace the "syntax" way and define it using a grammar:

```
syntax:

ℕ -> Z
  -> S ( ℕ )
```

Would I then be able to do this too?

```
AE  -> ( + AE AE )
    -> ( * AE AE )
    -> ℕ
```

I know there's an issue with ℕ ==> AE
if I have a ℕ, I also have AE.
I understand that there's a problem with "the missing constructor"
but what if I use the "production rule number" as a sort of hidden constructor?
This way if I am writing Z or S(Z) it depends on how do I want to parse it.
If I am parsing it as ℕ, it is clear.
If I am parsing it as AE, I know what it is as well.

There could be an issue if AE contains two rules like this, but that would be
a R/R conflict in the grammar, I am sure.

But logic-wise, it shouldn't be a problem. Or so I have heard.

------

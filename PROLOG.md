# Embedding FOL Natural Deduction proofs in Prolog

So we need the notion of derivations as a first-class object.

We can't just have the propositions as objects in Prolog, we have to be able to treat derivations as objects too. So that we can check that those derivations are legal.

On the other hand, could it perhaps be, that we would not really care about those derivations beside the fact that they are valid? So if something made sure they are valid—all the derivations preceding the one being checked/processed—would we be ok?

Let's have a look.


## Basic Representation

How do I represent constants, functions and function applications, propositional *constants* and propositions, quantified variables, and the rest?

### Constants
It seems that constants could be represented as atoms with the same name.

### Functions and Function Applications
It seems that those could be represented as structs.

### Propositional *Constants* and Propositions
So I am thinking—maybe I can do that using structs and atoms too. I only need to make sure that I will never confuse a representation of a constant with a representation of a propositions and so on.

### Quantified Variables
I will need to think about this one some more.



Let's try some simple example.

```
pr :  | p1: ∀ a ∀ b P(a, b)
      |------------------------
      |
      | d1 : P(α, β)  by rule ∀-elim on p1
      |
      | c : ∃ x ∃ y P(x, y)  by rule ∃-intro on d1
      |
```

What would this look like translated to Prolog?

```
pr(P1, C) :- forall_elim(P1, D1) , exists_intro(D1, C)
```

Maybe something like this?
So now the question is, how are `forall_elim` and `exists_intro` implemented?

How is `P1` represented? Maybe something like this: `forall(A, forall(B, p(A, B)))`?

This would allow me to easily instantiate it. I would just unify the variables with the term that is "instantiating" them.

So what would that mean for `forall_elim`?

```
forall_elim(forall(VAR, PROP), PROP).
```

Maybe? This would of course mean that each ∀-elimination would have to happen separately. So this would change the Prolog code above to:

```
pr(P1, C) :- forall_elim(P1, D1) , forall_elim(D1, D2) , exists_intro(D2, C)
```

The existential should be very similar. Except it is not that obvious, I will get to it soon.



## Scope Guards
It seems clear to me that Prolog won't take care of the scopes of variables and sub-proofs for us. That is something we would have to take care of during the encoding process.

## Universal Variables

One way to check that a universal variable was not unified with anything is to use some Prolog predicate testing whether a thing is a fresh-variable.

## Forall Introduction
This is something I am not sure of.

Here's what I am thinking:

```
| p1 : ∀ a P(a)
|---------------------
|
| α : | all α
|     |---------------
|     |
|     | d : P(α)  by rule ∀-elim on p1
|
| c : ∀ x P(x)  by rule ∀-intro on α
|
```

To introduce a ∀ I need to make sure that the assertion fo `c` is quantified version of the assertion that `d` makes. This could be done by inventing new unused atom, let's call it `x`, and unifying the un-quantified part of `c` with the whole `d`. This would check for me that `α` is not unified with anything at this point. Or at least only with some variable.
If this passes I can construct another version of `c` where instead of that unique atom `x` I have a fresh variable `X`.

The proposition might feature some other variables. Those might have been unified with something in the inner scope of the sub-proof. So I probably should unify the new `c` (the one with `X`) with `c`. I will need to look into it a bit more.
Then I just construct the forall with the `X` and I have the forall.
I suppose, this is what the implementation of ∀-intro or rather `forall_intro` would do.

The `exists_intro` should work in a similar way.

In the case of `forall_intro` we would want to introduce some inner scope to prevent the variable `α` be used in the current one. This could be somewhat challanging because we don't have "nested predicates" in Prolog. So this sort of check would probably have to be done by us (or some external mechanism).


## Exists Elimination
Here's an example:

```
| p1 : ∃ x P(x)
|-----------------
|
| α : | p2: P(α)
|     |------------------
|     |
|     | c : ∃ a P(a)  by rule ∃-intro on p2
|
| r : ∃ a P(a)  by rule ∃-elim on p1, α
|
```

This example combines ∃-elimination and ∃-introduction.

We need to check that `α` is not used outside its scope using some external mechanism.

Let's get the intro case out of the way first. We construct a term representing `P(a)` using an actual Prolog variable for `a`. This term has to unify with `p2`. We then have to construct the same term again (so that its variable `a` is not unified with anything) and use it to construct the existential. 


Now for the ∃-elimination, we construct a term corresponding to `P(a)` with a unique atom for `a`. We unify it with the unqualified part of `c`. This checks that the proposition in `c` does not "mangle" its variable in some bad way. In other words, this should prevent `c` being different to `r`, I think.

We also need to make sure that `p2` matches with `p1`. We do that using another temporary representation of the proposition in `r` and matching it against the proposition in `p1`.
As `p2` is instantiated with a constant/term (represented as an unique atom `α` in this temporary proposition) we only take the unqualified part of `p2`.

Actually, maybe we treat the instantiated term `p2` as if `α` is a constant.
In that case we would assign it a unique atom `α` and this would also change the way the ∃-intro is checked. We would not need to check that `α` is not unified with anything (as it is an atom), instead we would just check that `r` and `c` are "the same thing".

Finally, we would create the resulting representation of `r` with a fresh Prolog variable for `a` and use it to construct the full existential.



> TODO: What about the explicit universal variables in ∀-intro proofs.


## Theorems
How are theorems represented?
I am thinking predicates as well.



# Questions

Can I prevent things like this?

Start with ∀ a P(a, a).
Introduce universal x.
Introduce universal y.
Eliminate the ∀ to get P(x, y).
Introduce ∀ to get ∀ x P(x, y).
Introduce ∀ to get ∀ x ∀ y P(x, y).

This is clearly not OK.

I think I might have figured it out in the IMPLEMENTATION.md file.

# Encoding of Derivations
So I want to encode the derivations as objects too. It seems to me that it should be pretty straightforward.

Here's what I am thinking:

## Representing Rules as Objects in Prolog

### ∧-intro
```
conj_intro(Ader, Bder, deriv(conj_i, PREMISES, CONCLUSION)) :-  Ader = deriv(_rule, _premises, Aconclusion)
                                                              , Bder = deriv(_rule, _premises, Bconclusion)
                                                              , PREMISES = [Ader, Bder]
                                                              , CONCLUSION = conj(A, B) .
```

First two arguments are derivations of the premises A and B.
The last argument is a resulting derivation—a proof (object) for A => B.
We now don't need to trust that the code-generating part of our software won't ever introduce some assertion without having a proper justification for it. Every assertion is now a part of a derivation that can be checked at any point.

### ∧-elim
```
conj_elim(CON, deriv(conj_e, [CON], A)) :-  CON = deriv(conj_i, PREMISES, conj(A, B)) .

conj_elim(CON, deriv(conj_e, [CON], B)) :-  CON = deriv(conj_i, PREMISES, conj(A, B)) .
```

So this is what the simple rules look like. To obtain A or B from A ∧ B, we must first have the A ∧ B.


This sort of approach means that when we write the proofs, we don't really need to have those propositions "on their own". We have them as conclusions of derivations.


### Sub-proofs
This one is going to be a bit more interesting. It is something that we haven't dealt with, previously.

Example:
```
| p1 : A
|---------------------
|
| d : | p2 : B
|     |---------------
|     |
|     | conclusion : A ∧ B  by rule ∧-intro on p1, p2
|
```

A subproof is just another object. Because of the scope, we build it in-place, we don't use auxiliary predicates for that. So the following is a term in the general shape `sub-proof(PREMISES, CONCLUSION)`.
The conclusion is going to be a derivation, so all the relevant assertions in the body of the sub-proof are going to be recorded in the conclusion.

```
P1 = a(),
P2 = b(),

DERIV = deriv(conj_i, PREMISES, CONCLUSION),
conj_intro(P1, P2, DERIV),
D = sub-proof(P2, CONCLUSION) ,
...
```

This is a messed up example. Look below and see a better one.

### ==>-intro
The above relates to the introduction rule for the implication.

Here's an example how we would use such a rule:

```
| d1 :  | p1 : A
|       |---------------------
|       |
|       | d2 :  | p2 : B
|       |       |---------------
|       |       |
|       |       | conclusion : A ∧ B  by rule ∧-intro on p1, p2
|       |
|       | B=>A∧B : B ==> A ∧ B  by rule impl-intro on d2
|
| A=>B=>A∧B : A ==> B ==> A ∧ B  by rule impl-intro on d1
```

This is it encoded:

```
A = a(),
B = b(),

    P1 = a(),
% |----------------

      P2 = b(),
%   |--------------
%   |
      DERIV = deriv(conj_i, _premises, conj(A, B)), % I guess this is just for demonstration purposes?
      conj_intro(P1, P2, DERIV),
      D2 = sub_proof(P2, DERIV),

    impl_intro(impl(B, conj(A, B)), D2, B=>A∧Bderiv),
    D1 = sub_proof(P1, B=>A∧Bderiv),

  impl_intro(impl(A, impl(B, conj(A, B))), D1, A=>B=>A∧Bderiv) .
```

So, how is `impl_intro` implemented?

```
impl_intro(THEIMPL, SUBPROOF, DERout) :-  SUBPROOF = sub_proof(PREMISE, DERin)
                                        , DERin = deriv(_, _, CONCL)
                                        , THEIMPL = impl(PREMISE, CONCL)
                                        , DERout = deriv(impl_i, SUBPROOF, THEIMPL) .
```

### Quantifiers
I think quantifiers should be very similar to the simpler approach.
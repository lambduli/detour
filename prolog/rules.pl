% conj_intro/3
% conj_intro relates:
%                   - a proposition A we have
%                   - a proposition B we have
%                   - a proposition A ∧ B we are trying to prove
conj_intro(A, B, and(A, B)).


% conj_elim/2
% I am trying to take advantage of the backtracking.
% This might make the proofs simpler—avoiding some sort of ∧-elim-left ∧-elim-right.
conj_elim(and(A, B), A).
conj_elim(and(A, B), B).




disj_intro(A, or(A, B)).
disj_intro(B, or(A, B)).


% it takes the disjunction of A ∨ B
% it takes the assumption of the first derivation A
% it takes the conclusion of the first derivation P
% it takes the assumption of the second derivation B
% it takes the conclusion of the second derivation P
% it takes a proposition that it is supposed to justify—P

% We really want both sub-proofs to conclude with the same proposition.
% That's why we unify those two together.
% We also want the proposition that is being justified to be the same thing as well. 
disj_elim(or(A, B), A, P, B, P, P).




impl_intro(A, B, impl(A, B)).


impl_elim(impl(A, B), A, B).




neg_intro(A, false, not(A)).


neg_elim(A, not(A), false).
% maybe I can use backtracking and have
neg_elim(not(A), A, false).




contr_elim(false, C).




% proof by contradiction for classical logic mode
contr(not(A), false, A).




% this one is a bit different, more complicated
% the A is the conclusion of the sub-proof, it contains a variable U
% the second one is the proposition being justified
%   instead of variable U, it has a variable X inside
%   if those two terms unify together and I can check that X is still unusigned variable
%   then I know two things: - structurally, they are the same
%                           - the U is never bound anywhere within the sub-proof
% at the same time, because I unify the thing in the forall with the conclusion of the sub-proof
% if there is some outer variable being bound to a specific term, it will be bound in the concluded forall
% this will make it possible to catch this later (maybe in foral_intro, maybe in some other rule)
forall_intro(A, FORALL) :- FORALL = forall(X, P) , subsumes_term(P, A).
% this is most likely wrong
% my universal variables should be represented as atoms
% this means I need to fix this implementation
% I think it's fixed now.


forall_elim(FORALL, A) :- FORALL = forall(_, _)
                        , copy_term(FORALL, forall(_, A)) , ! .

% this is just a quick attempt to support the multi-step elimination
% I don't know how I would check that 
% forall_elim(forall(_, FORALL), A) :-  FORALL = forall(_, _)
%                                     , forall_elim(FORALL, A).


% this one even more complicated
% in this case, I would have a proposition containing a term/constant
% that I would need to unify with the generalized with (from the exists)
% to check that structurally, it is valid
% I might also check that the var X then would not be a variable
%
% but then I would need to manipulate the proposition so that the term/constant
% in it, the one we are generalizing over, gets replaced with a fresh variable that we call X
% this would be incredibly tedious and needlesly complicated
% instead, I am going to rely on the frontend
% when it sees an application of a rule ∃-intro
% it looks at its argument (the specific proposition), it creates a new copy of that Prolog term
% this copy is almost completely identical to the original, all the variables and such are the same
% the only difference is that the term that we are generalizing over is now replaced with
% a fresh variable
% this way, I can unify them together and the resulting existential does really contain a variable
% and not something else
%
% the aux-variable in the AwithVar will never be used again, so this is a no issue.
%
% and just to be more explicit about it, this predicate also takes the original version of the proposition
% exists_intro(_, AwithVar, exists(X, AwithVar)) :- var(X).

% this is a simpler version of the above
% we check that the unqualified part of the existential subsumes
% the proposition it is supposed to generalize
% the X stays a variable after this check
exists_intro(AwithTerm, exists(X, AwithVar)) :- subsumes_term(AwithVar, AwithTerm).


exists_elim(EXISTS, AwithU, P, P) :- EXISTS = exists(Xo, Ao)
                                  , copy_term(EXISTS, NEWEXISTS)
                                  , NEWEXISTS = exists(X, A)
                                  , A = AwithU % U is never used again so I don't mind
                                  , var(X) % U must be a variable, so X must be a variable
                                  % the above might have the same effect as the thing below

                                  , subsumes_term(AwithU, Ao)
                                  , subsumes_term(Ao, AwithU) % probably won't hurt
                                  , copy_term(A, B).



% induction should check that first two arguments are propositions
% in this general shape:
% first P(0)
% second ∀ x P(x) => P(x + 1)
% if this is the case, then we can give back this:
% ∀ x P(x)
induction(BASE, INDUCT, FORALL) :-  FORALL = forall(_, _)

                                    % first, the base case
                                  , copy_term(FORALL, forall(VARZ, FORMZ))
                                  , VARZ = zero
                                  , subsumes_term(FORMZ, BASE)

                                  % % now, the inductive case
                                  , copy_term(FORALL, forall(VARN, FORMN))

                                  , copy_term(FORALL, forall(VARN1, FORMN1))
                                  , VARN1 = s(VARN)

                                  , copy_term(INDUCT, forall(_, F))

                                  , INDIMPL = impl(FORMN, FORMN1)
                                  % , writeln(INDIMPL)
                                  % , writeln(F)
                                  , subsumes_term(INDIMPL, F)
                                  , subsumes_term(F, INDIMPL) .




% ∃ ℕ₃ Sum( Z , ℕ₂ , ℕ₃ )   the base case
% ∀ ℕ' [ ∃ ℕ₃ Sum( ℕ' , ℕ₂ , ℕ₃ ) ==> ∃ ℕ₃ Sum( S(ℕ') , ℕ₂ , ℕ₃ ) ]   the inductive case
%
% ∀ ℕ₁ ∃ ℕ₃ Sum( ℕ₁ , ℕ₂ , ℕ₃ )   the resulting proposition

% So I have to create a pattern that matches the base case
% then I can instantiate that one variable in the pattern with "zero" and again, match the base case

% then I take that general pattern and see that the inductive case is
% <the pattern> ==> <the pattern>

% Then I would instantiate that pattern with "N" on the LHS of the implication
% and with "N + 1" on the RHS of the implication
% it then has to unify as well

% I think I am just gonna make the induction predicate take that "pattern".
% I am gonna say that the frontend would build that pattern.

% here the pattern will be    ∃ ℕ₃ Sum( PLACEHOLDER , ℕ₂ , ℕ₃ )
% where the ℕ₂ is a fixed universal variable and the PLACEHOLDER is the thing that
% the induction predicate needs to instantiate to "zero" and then to "N" and then to "N + 1"
%
% I will deal with that using the copy_term predicate.
%
% For that reason, I think, I will need to take the pattern wrapped in something
% so that the PLACEAHOLDER is accessible to me.
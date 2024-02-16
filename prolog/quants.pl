
%%
%% THIS ONE IS SUPPOSED TO FAIL
%%
% This is the example of an illegal derivation.
% 
% _ : | p1 : ∀ a Id(a, a)
%     |----------------------
%     |
%     | a : | all α
%     |     |-----------------
%     |     |
%     |     | b : | all β
%     |     |     |-------------
%     |     |     |
%     |     |     | _ : Id(α, β)  by rule ∀-elim on p1
%     |     |     | -- but if I do this, I can misuse it like this:
%     |     |
%     |     | _ : ∀ b Id(α, b)  by rule ∀-intro on b
%     |
%     | _ : ∀ a ∀ b Id(a, b)  by rule ∀-intro on a
%     |

% Now, to represent it as Prolog program.

regeneralize(P1, RESULT) :- P1 =  forall(I, id(I, I)) % I don't like exposing them
                                                      % but I want to check.

                                , A = aaa
                                , B = bbb
                                , C1 = id(A, B)
                                , forall_elim(P1, C1)

                                , C2 = forall(G, id(A, G))
                                , forall_intro(C1, C2)
                                
                                , C3 = forall(X, (forall(Y, id(X, Y))))
                                , forall_intro(C2, C3)

                                , RESULT = C3.
%%
%%  THIS FAILS
%%



%%
%% THIS ONE IS SUPPOSED TO WORK
%%
% | p1 : ∀ x ∀ y P(x, y)
% |-------------------------------
% |
% | α : | all α
% |     |-------------------------
% |     |
% |     | β : | all β
% |     |     |-------------------
% |     |     |
% |     |     | _ : P(β, α)  by rule ∀-elim on p1
% |     |
% |     | _ : ∀ x P(x, α)  by rule ∀-intro on β
% |
% | _ : ∀ y ∀ x P(x, y)  by rule ∀-intro on α

reorder(P1, RESULT) :-  P1 =  forall(X, forall(Y, p(X, Y)))
                            , A = aaa
                            , B = bbb

                            , Cc = forall(F, p(B, F))
                            , forall_elim(P1, Cc)

                            , C1 = p(B, A)
                            , forall_elim(Cc, C1)

                            , C2 = forall(O, p(O, A))
                            , forall_intro(C1, C2)

                            , C3 = forall(K, (forall(L, p(L, K))))
                            , forall_intro(C2, C3)

                            , RESULT = C3.
%%
%%  THIS WORKS
%%
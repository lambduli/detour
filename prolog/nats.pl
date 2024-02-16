% rule
% sum-z : |
%         |-----------------------
%         | ∀ ℕ Sum( Z , ℕ , ℕ )

sum_z(forall(N, sum(zero, N, N))).

% rule
% sum-s : |
%         |-------------------------------------------------------------------
%         | ∀ ℕ₁ ∀ ℕ₂ ∀ ℕ₃ Sum( ℕ₁ , ℕ₂ , ℕ₃ ) ==> Sum( S(ℕ₁) , ℕ₂ , S(ℕ₃) )
%

sum_s(forall(N1, forall(N2, (forall(N3, impl(sum(N1, N2, N3), (sum(s(N1), N2, s(N3))))))))).


% theorem totality :  ∀ ℕ₂ ∀ ℕ₁ ∃ ℕ₃ Sum( ℕ₁ , ℕ₂ , ℕ₃ )
totality(CONCLUSION)  :-  
% |-------------------------------------------------------
% | N2 :  | all ℕ₂
            N2 = nN2 % this is just so that lines in the comments have something to correspond to
% |       |----------------
% |       | sz : ∀ ℕ Sum( Z , ℕ , ℕ )  by rule sum-z
          , sum_z(SZ) % I don't expand it because I don't want to touch those variables anywhere.

% |       | sum23 : Sum( Z , ℕ₂ , ℕ₃ )  by rule ∀-elim on sz
          , SUM23 = sum(zero, N2, N3) % I want to to expose those variables
          , forall_elim(SZ, SUM23)

% |       | base : ∃ ℕ'₃ Sum( Z , ℕ₂ , ℕ'₃ )  by rule ∃-intro sum23
          , BASE = exists(NP3, sum(zero, N2, NP3))
          , exists_intro(SUM23, BASE)


% |       | N∀ :  | all ℕ'
                  , Nn1 = nN1 % universal variables are actually atoms/constants ; they only unify with fresh-variables and themselves
% |       |       |---------------------

% |       |       | im :  | p1: ∃ ℕ₃ Sum( ℕ' , ℕ₂ , ℕ₃ )
                          , P1 = exists(N3p1, sum(Nn1, N2, N3p1))  % we are assuming this, the "frontend" takes care of checking that this really is legally assumed
% |       |       |       |--------------------------------

% |       |       |       | N3 :  | p2: Sum( ℕ' , ℕ₂ , ℕ₃ )
                                  , P2 = sum(Nn1, N2, N3p12) % again—assumption, again—frontend

% |       |       |       |       |-----------------------------
% |       |       |       |       | sums : ∀ ℕ₁ ∀ ℕ₂ ∀ ℕ₃ Sum( ℕ₁ , ℕ₂ , ℕ₃ ) ==> Sum( S(ℕ₁) , ℕ₂ , S(ℕ₃) )  by rule sum-s
                                  , sum_s(SUMS) % I don't want to expose those variables, just to be sure

% |       |       |       |       | impl : Sum( ℕ' , ℕ₂ , ℕ₃ ) ==> Sum( S(ℕ') , ℕ₂ , S(ℕ₃) )  by rule ∀-elim on sums
                                    % I need to do it a step-by-step
                                    % first this: ∀ ℕ₂ ∀ ℕ₃ Sum( ℕ' , ℕ₂ , ℕ₃ ) ==> Sum( S(ℕ') , ℕ₂ , S(ℕ₃) ) 
                                  , F2 = forall(Np2a, forall(Np3a, impl(sum(Nn1, Np2a, Np3a), sum(s(Nn1), Np2a, s(Np3a)))))
                                  , forall_elim(SUSM, F2)
                                    % now: ∀ ℕ₃ Sum( ℕ' , ℕ₂ , ℕ₃ ) ==> Sum( S(ℕ') , ℕ₂ , S(ℕ₃) )
                                  , F3 = forall(Np3a, impl(sum(Nn1, N2, Np3a), sum(s(Nn1), N2, s(Np3a))))
                                  , forall_elim(F2, F3)
                                    % now: Sum( ℕ' , ℕ₂ , ℕ₃ ) ==> Sum( S(ℕ') , ℕ₂ , S(ℕ₃) )
                                  , IMPLab3 = impl(sum(Nn1, N2, Np3ab), sum(s(Nn1), N2, s(Np3ab)))

% |       |       |       |       | d1 : Sum( S(ℕ') , ℕ₂ , S(ℕ₃) ) by rule ==>-elim on impl, p2
                                  , D1 = sum(s(Nn1), N2, s(Np3ab))
                                  , impl_elim(IMPLab3, P2, D1)

% |       |       |       |       | _ : ∃ ℕ₃ Sum( S(ℕ') , ℕ₂ , ℕ₃ ) by rule ∃-intro on d1, S(ℕ₃)  -- I am generalizing over S(ℕ₃), the engine may figure it out.
                                  , CON1 = exists(N3abc, sum(s(Nn1), N2, N3abc))
                                  , exists_intro(D1, CON1)

% |       |       |       | _ : ∃ ℕ₃ Sum( S(ℕ') , ℕ₂ , ℕ₃ )  by rule ∃-elim on p1, N3
                          , CON2 = exists(N3pabc, sum(s(Nn1), N2, N3pabc))
                          , exists_elim(P1, P2, CON1, CON2)

% |       |       | impl : ∃ ℕ₃ Sum( ℕ' , ℕ₂ , ℕ₃ ) ==> ∃ ℕ₃ Sum( S(ℕ') , ℕ₂ , ℕ₃ )  by rule ==>-intro on im
                  , IMPLabc = impl(exists(N3pbo, sum(Nn1, N2, N3pbo)), exists(N3pco, (sum(s(Nn1), N2, N3pco))))
                  , impl_intro(P1, CON2, IMPLabc)

% |       | ind : ∀ ℕ' [ ∃ ℕ₃ Sum( ℕ' , ℕ₂ , ℕ₃ ) ==> ∃ ℕ₃ Sum( S(ℕ') , ℕ₂ , ℕ₃ ) ]  by rule ∀-intro on N∀
          , IND = forall(Npr, impl(exists(N3pbo, sum(Npr, N2, N3pbo)), exists(N3pco, (sum(s(Npr), N2, N3pco)))))
          , forall_intro(IMPLabc, IND)

% |       | -- Now, I do proof by induction.
% |       | _: ∀ ℕ₁ ∃ ℕ₃ Sum( ℕ₁ , ℕ₂ , ℕ₃ )  by induction on base, ind
          , FALLN = forall(N11N, exists(N33N, sum(N11N, N2, N33N)))
          
          % , PATTERN = exists(NP3, sum(PLACEHOLDER, N2, NP3))
          , induction(BASE, IND, FALLN)

% | _ : ∀ ℕ₂ ∀ ℕ₁ ∃ ℕ₃ Sum( ℕ₁ , ℕ₂ , ℕ₃ )  by ∀-intro on N2
  , RESULT = forall(N22N, forall(N11N, exists(N33N, sum(N11N, N22N, N33N))))
  , forall_intro(FALLN, RESULT)

  , CONCLUSION = RESULT
.

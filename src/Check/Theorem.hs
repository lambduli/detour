module Check.Theorem where


import Control.Monad.Except ( throwError )

import Check.Error ( Error(..) )

import Check.Check ( Check )

import Syntax.Theorem ( Theorem )
import Syntax.Judgment ( Judgment(..) )

-- TODO:  This file implements checking for one theorem.
--        It is working over the Check monad stack.



-- TODO:  This function goes one derivation at a time and checks them using unification and such.
--        I can use local to record the current theorem I am checking so that if it fails
--        I have the information in the environment and can report it in the Error.
--        Or, I could just track the location of the error and report just that.
--        This would be the first time I would do that (·_.)
check'theorem :: Theorem -> Check ()
check'theorem Theorem { assumptions = formulae
                      , conclusion
                      , proof = derivations } = do
  --  I need to traverse the proof (List of Derivations).
  --  The traversing function might succeed and return the last derivation.
  --  That can be a sub-proof too.
  --  If it is a sub-proof, I need to basically treat it as if this sub-proof is the proof
  --  of the theorem.
  --  
  --  I need to check that the assumptions of that sub-proof match the assumptions
  --  of the theorem.
  --  I also need to check that the conclusion of the sub-proof matches the
  --  conclusion of the theorem.

  last <- check'all derivations

  case last of
    Sub'Proof (Proof{ assumption, derivations }) -> do
      check'assumptions assumption formulae

      case reverse derivations of
        last : _ -> do
          check'conclusion last conclusion

        [] -> do
          throwError $! Missing'Conclusion conclusion

    Claim claim -> do
      check'conclusion claim conclusion


check'proof :: Proof -> Check ()
check'proof Proof{ assumption = Universal variables, derivations } = do
  assignments <- mapM assign'fresh'const variables
  let patch = Map.fromList assignments

  local (\ env@Env{ var'scope = scope } -> env{ var'scope = scope `Map.union` patch }) (check'all derivations)
  where assign'fresh'const :: String -> Check (String, Int)
        assign'fresh'const var = do
          c <- fresh'constant
          addr <- store c
          return (var, addr)

check'proof Proof{ assumption = Formula bindings, derivations } = do
  let named = filter is'named bindings -- [(Maybe String, Formula)]
  let patch = Map.fromList named
  local (\ env@Env{ judg'scope = scope } -> env{ judg'scope = scope `Map.union` patch }) (check'all derivations)
  where is'named :: (Maybe String, a) -> Bool
        is'named (Nothing, _) = False
        is'named (Just _, _) = True


check'all :: [Judgment] -> Check ()
check'all [] = do
  throwError $! Empty'Proof Nothing

check'all [judgment] = do
  check'judgment judgment

check'all (judgment : judgments) = do
  check'judgment judgment

  in'scope'of judgment (check'all judgments)


in'scope'of :: Judgment -> Check a -> Check a
in'scope'of judgment@(Sub'Proof Proof{ name = Just name }) m = do
  scope <- asks judg'scope

  when (scope `Map.member` name) (throwError $! Name'Clash name)

  local (\ env@Env{ judg'scope = scope } -> env{ judg'scope = Map.insert name (Right judgment) scope }) m

in'scope'of (Sub'Proof Proof{ name = Nothing }) m = do
  m

in'scope'of judgment@(Claim Claim{ name = Just name }) m = do
  scope <- asks judg'scope

  when (scope `Map.member` name) (throwError $! Name'Clash name)

  local (\ env@Env{ judg'scope = scope } -> env{ judg'scope = Map.insert name (Right judgment) scope }) m

in'scope'of (Claim Claim{ name = Nothing }) m = do
  m


--  For checking theorem assumptions.
--  The universal case is not possible.
check'assumptions :: Assumption -> [Formula] -> Check ()
check'assumptions (Formula named'formulae) formulae = do
  --  The assumptions need to be in the correct order.
  --  Not every required assumpion needs to be used.
  match'assumptions named'formulae formulae
    where match'assumptions :: [(Maybe String, Formula)] -> [Formula] -> Check ()
          match'assumptions n@((_, n'fm) : n'fms) (fm : fms)
            = if n'fm `equivalent` fm
              then match'assumptions n'fms fms
              else match'assumptions n (fm : fms)

          match'assumptions [] _ = return ()
          match'assumptions _ []
            = throwError $! Wrong'Assumptions "Theorem doesn't allow any more assumptions but the proof mentions some more." -- TODO: make it better

check'assumptions (Universal [String]) = do
  throwError $! Disallowed "Introducing universal variables is not allowed in the premise of a theorem proof."


check'conclusion :: Judgment -> Formula -> Check ()
check'conclusion c@(Claim (Claim { formula })) fm
  = unless  (formula `alpha'equivalent'to` fm)
            (throwError $! Wrong'Conclusion fm c)
check'conclusion der fm
  = throwError $! Wrong'Conclusion fm der


check'judgment :: Judgment -> Check ()
check'judgment (Sub'Proof p@Proof{ name, assumption, derivations }) = do
  check'proof p

check'judgment (Claim c@Claim{ formula, justification }) = do
  justification `justifies` formula


justifies :: Justification -> Formula -> Check ()
justifies Rule{ kind = rule, on = identifiers } fm = do
  judgments <- mapM id'to'jud identifiers
  
  check'rule rule judgments fm

justifies (Theorem { name, on = identifiers }) fm = do
  Theorem { assumptions, conclusion, proof } <- look'up'theorem name

  identifiers `are'compatible'with` assumptions

  fm `is'compatible'with` conclusion

justifies Unproved _ = do
  return ()

justifies (Induction { on = identifiers }) fm = do
  --  TODO: I need to figure out what (inductively defined) property
  --        is this reasoning about.
  --        Maybe like this:

  --        We have the formula, a bunch of base cases and a bunch of inductive cases.

  --        The formula the induction justifies looks something like this:
  --        ∀ x P[x]
  --        where P[x] is any formula where `x` is occuring.
  --
  --        The base cases look something like this:
  --        P[x -> α]
  --        where [x -> α] means that where above would be `x`, here it will be one of the
  --        non-inductive, base-case constants.
  --
  --        All the base cases should sort-of unify with the P[x] part if we consider `x`
  --        to be a unification variable.
  --        Example P[x] ≈ P[x -> Zero]
  --
  --        The inductive cases look something like this:
  --        ∀ y P[x -> y] ==> P[x -> ƒ(y)]
  --        where `ƒ` means some inductive-case function.
  --
  --
  --        From all this, it should be obvious which inductively-defined relation
  --        are we talking about.
  --        We should handle all the cases.
  --        They should preferably be in the correct order, but maybe I can deal
  --        with them being in any order.

  undefined

justifies (Substitution{ on, using }) fm = do
  undefined --  TODO: implement
  --  using is a claim of equivalence (identifier that represents it, rather)
  --  on    is a claim that proves something
  --  fm    and `on` can unify under the equivalence


id'to'jud :: String -> Check (Either Formula Judgment)
id'to'jud identifier = do
  scope <- asks judg'scope
  case Map.lookup scope identifier of
    Nothing -> do
      throwError $! Unknown'Identifier identifier
    Just either -> do
      return either


are'compatible'with :: [String] -> [Formula] -> Check ()
are'compatible'with identifiers formulae = do
  --  TODO: Get all the identifiers.
  --        They need to bind claims and assumptions.
  --        Those formulae need to unify together.
  --        This might result in a substitution.
  undefined


is'compatible'with :: Formula -> Formula -> Check ()
is'compatible'with fm fm' = do
  fm `unify` fm'


decompose'implication :: Formula -> Assumption -> Check ([Formula], Formula)
decompose'implication _ (Universal _) = do
  throwError $! Wrong'Assumptions "A sub-proof justifying implication can not have universal as its assumption."
decompose'implication impl (Formula bindings) = do
  decompose impl bindings
    where decompose :: Formula -> [(Maybe String, Formula)] -> Check ([Formula], Formula)
          decompose concl []
            = return ([], concl)
          decompose (Impl left right) ((_, fm) : bindings) = do
            (prems, concl) <- decompose right bindings
            return (left : prems, concl)


check'rule :: Rule -> [Either Formula Judgment] -> Formula -> Check ()
check'rule Impl'Intro [Right (Sub'Proof proof)] impl@(Impl _ _) = do
  let Proof{ name, assumption, derivations } = proof

  --  I need to check that whole proof.
  --  I need to check that the last claim of the proof is identical to the conclusion
  --    I suppose they could be not exactly identical but unifiable together
  --    I might experiment with this later. For now they must be α-equivalent.
  --  All the assumptions of of the proof must also be α-equivalent to the premises.
  --    If there are many assumptions, there should be more implications nested in the concl.
  
  --  TODO: This is a complete nonsense!
  --        At this point, the proof has already been checked.
  --        I don't need to check it again. What would that achieve?
  --        Instead, I just get the last derivation directly.
  --        
  case List.unsnoc derivations of
    Nothing -> do
      throwError $! undefined --  TODO: error!
    Just (_, last) -> do
      (premises, conclusion) <- decompose'implication impl assumption

      check'assumptions assumption premises
      check'conclusion last conclusion

check'rule Impl'Elim [Right (Claim claim), Left pre] conclusion = do
  let Claim{ formula } = claim

  case formula of
    Impl left right -> do
      left `unify` pre
      right `unify` conclusion

    _ -> do
      throwError $! Rule'Mismatch "The rule ==>-elim only accepts proofs of implications."

check'rule Conj'Intro [Right (Claim claim'a), Right (Claim claim'b)] (And a' b') = do
  --  the claim'a needs to claim a
  let Claim{ formula = a } = claim'a
  --  the claim'b needs to claim b
  let Claim{ formula = b } = claim'b

  --  a and a' and also b and b' should be the same up to α-equivalence, I think
  --  making them the same shouldn't probably cause any unification?
  --  maybe it could?
  --  I am just worried that this could be used to first justify something with the a'
  --  and then to make it work for the conjunction, it will change something in the a'
  --  the question is, can I change (later) something that would cause a problem? I don't know.And

  a `alpha'equivalent'to` a'
  b `alpha'equivalent'to` b'

check'rule Conj'Elim [Right (Claim Claim{ formula = a `And` b })] formula = do
  if a `alpha'equivalent'to` formula || b `alpha'equivalent'to` formula
  then return ()
  else throwError $! Wrong'Justification Conj'Elim [Right (Claim Claim{ formula = a `And` b })] formula
    --  TODO: make the error reporting better (different constructor), this is ridiculous!

check'rule Disj'Intro [Right (Claim Claim{ formula })] (Or a b) = do
  --  TODO: the formula might be a or it might be b
  if formula `alpha'equivalent'to` a || formula `alpha'equivalent'to` b
  then return ()
  else throwError $! Wrong'Justification Disj'Intro [Right (Claim Claim{ formula })] (Or a b)

check'rule Disj'Elim  [ Right (Claim Claim{ formula = Or a b })
                      , Right (Sub'Proof Proof{ assumption = Formula [(_, a')], derivations = der'a })
                      , Right (Sub'proof Proof{ assumption = Formula [(_, b')], derivations = der'b }) ] formula = do
  --  The judgments are three things
  --  the first one is a claim that a ∨ b
  --  the second and third are proofs
  --  both proofs have to justify the same thing and that thing is the formula
  --  all three are equivalent up to the α-renaming
  --  the first proof assumes exactly a
  --  the second proof assumes exactly b

  a `alpha'equivalent'to` a'
  b `alpha'equivalent'to` b'

  goal'a <- last'derivation der'a
  goal'b <- last'derivation der'b

  goal'a `alpha'equivalent'to` goal'b
  goal'b `alpha'equivalent'to` formula

check'rule Neg'Elim [ Right (Claim Claim{ formula = a })
                    , Right (Claim Claim{ formula = a' }) ] F.False = do
  a `is'negated` a'

check'rule Equiv'Intro  [ Right (Claim Claim{ formula = Impl a b })
                        , Right (Claim Claim{ formula = Impl b' a' }) ] formula = do
  a `alpha'equivalent'to` a'
  b `alpha'equivalent'to` b'

check'rule Equiv'Elim [Right (Claim Claim{ formula = Eq a b })] (Impl x y) = do
  --  Either  a <==> b justifies a ==> b
  --  or      a <==> b justifies b ==> a

  unless  (a `alpha'equivalent'to` x && b `alpha'equivalent'to` y)
          ||
          (a `alpha'equivalent'to` y && b `alpha'equivalent'to` x)
  throwError $! undefined --  TODO: error!

check'rule True'Intro [] Term.True = do
  return ()

check'rule Proof'By'Contradiction [Right (Sub'Proof Proof{ assumption = Formula [(_, Not a)], derivations })] formula = do
  m <- asks mode
  case m of
    Intuitionistic -> do
      throwError Disallowed'By'Contradiction
    Classical -> do
      last <- last'derivation derivations
      case last of
        F.False -> do
          a `alpha'equivalent'to` formula
        _ -> do
          throwError $! undefined --  TODO: error!

check'rule Contra'Elim [Right (Claim Claim{ formula = F.False })] formula = do
  return ()

check'rule Forall'Intro judgments formula = do
  undefined

check'rule Forall'Elim judgments formula = do
  --  NOTE: This one is interesting, because it can introduce implicit universals.
  undefined

check'rule Exists'Introduction judgments formula = do
  undefined

check'rule Exists'Elimination judgments formula = do
  undefined

check'rule Repetition [Right (Claim Claim{ formula = fm })] formula = do
  formula `alpha'equivalent'to` fm

--  TODO: I need to implement support for this.
check'rule (Custom name) judgments formula = do
  undefined

check'rule rule judgments formula = do
  throwError $! Wrong'Justification rule judgments formula


last'derivation :: [Judgment] -> Check Judgment
last'derivation derivations = do
  case List.unsnoc derivations of
    Nothing -> do
      throwError $! undefined
    Just (_, last) -> do
      return last
module Check.Substitute where


import Data.Map.Strict qualified as Map

import Check.Environment ( Environment(assert'scope, Env) )
import Check.Assertion ( Assertion(..) )
import Check.Substitution ( Substitution, Binding(..) )
import Check.Substitution qualified as Substitution
import Check.Constraint ( Constraint(..) )

import Syntax.Judgment ( Judgment(..) )
import Syntax.Judgment qualified as J
import Syntax.Assumption ( Assumption(..) )
import Syntax.Proof ( Proof(..) )
import Syntax.Claim ( Claim(..) )
import Syntax.Claim qualified as C
import Syntax.Justification ( Justification(..) )
import Syntax.Formula ( Formula(Exists, Atom, Not, And, Or, Impl, Eq, Forall) )
import Syntax.Formula qualified as F
import Syntax.Relation ( Relation(..), Prop'Var(..) )
import Syntax.Term ( Term(..), Bound(..) )


compose :: Substitution -> Substitution -> Substitution
sub'l `compose` sub'r = (apply sub'l) sub'r ++ sub'l


--  NOTE: I will try to avoid using merge.
-- merge :: Substitution -> Substitution -> Check Substitution
-- sub'l `merge` sub'r
--   = if agree
--       then return $! sub'l ++ sub'r  --  TODO: This is not ideal, I keep duplicates. But they agree so it doesn't matter, I think.
--       else throwError undefined --  TODO: error; unification error or something
--         where
--           agree = all equivalent (Map.keys sub'l `intersect` Map.keys sub'r)
--           equivalent :: k -> Bool
--           equivalent var = apply s1 lifted == apply s2 lifted
--             where
--               lifted :: v
--               lifted = lift var


--  substituting for k the a within b
class Substitute b where
  apply :: Substitution -> b -> b


--  TODO: So here's a question.
--        If I am applying a substitution to a Term or a Formula
--        should I apply it to the collected constraints as well?
--        Or maybe the other way around—should I solve the constraints, apply the
--        resulting substitution to the Term or Formula and only then apply the
--        substitution to it?
--        The idea behind this question is the followig.
--        The Term or the Formula might contain some free-vars.
--        Those might be unified with something else
--        like some Term or another free-var.
--        If I want to apply a substitution to change some free-vars to do
--        some rule-checking, I might need to apply the implicit substitution first
--        Here's why. If I first apply the substitution to not fully specified term
--        the resulting constraint-substitution will then change it so that
--        some of the changes that would have happened, will not have happened.
--        So I guess, any time I do substitution during the proof-checking
--        I should be absolutely sure that this unintended side-effect will not take place.


instance Substitute Binding where
  apply :: Substitution -> Binding -> Binding
  apply subst (Free'2'Term f t) = Free'2'Term f (apply subst t)
  apply subst (Bound'2'Term b t) = Bound'2'Term b (apply subst t)
  apply subst (Prop'2'Formula p f) = Prop'2'Formula p (apply subst f)


instance Substitute Term where
  apply :: Substitution -> Term -> Term
  apply subst term@(Bound b)
    = case Substitution.lookup b subst of
        Nothing -> term
        Just t -> t

  --  NOTE: This is sort-of a hack. When I am checking ∀-intro
  --        I substitute all the constants for bound variables and unify it with the universal.
  --        Maybe I should change this in the future. I don't love it.
  apply subst (App c [])
    = case Substitution.lookup c subst of
        Nothing -> App c []
        Just t -> t
  
  apply subst (App c args) = App c (apply subst args)

  apply subst term@(Free f)
    = case Substitution.lookup f subst of
        Nothing -> term
        Just t -> t


instance Substitute Formula where
-- instance Substitute Free Term Formula where
  apply :: Substitution -> Formula -> Formula
  apply _ F.True = F.True

  apply _ F.False = F.False

  apply subst (Atom (Rel n args)) = Atom (Rel n (apply subst args))

  apply subst fm@(Atom (Meta'Rel v@(Prop'Var _)))
    = case Substitution.lookup v subst of
        Nothing -> fm
        Just f -> f

  apply subst (Not fm) = Not (apply subst fm)

  apply subst (left `And` right) = apply subst left `And` apply subst right

  apply subst (left `Or` right) = apply subst left `Or` apply subst right

  apply subst (left `Impl` right) = apply subst left `Impl` apply subst right

  apply subst (left `Eq` right) = apply subst left `Eq` apply subst right

  apply subst (Forall var fm) = Forall var (apply (Substitution.remove (B var) subst) fm)

  apply subst (Exists var fm) = Exists var (apply (Substitution.remove (B var) subst) fm)


instance Substitute Judgment where
  apply :: Substitution -> Judgment -> Judgment
  apply subst (Sub'Proof proof) = Sub'Proof (apply subst proof)

  apply subst (J.Claim claim) = J.Claim (apply subst claim)


instance Substitute Proof where
  apply :: Substitution -> Proof -> Proof
  apply subst p@Proof{ assumption, derivations }
    = p { assumption = apply subst assumption
        , derivations = apply subst derivations }


instance Substitute Assumption where
  apply :: Substitution -> Assumption -> Assumption
  apply subst (Formula pairs) = Formula (apply subst pairs)

  apply _ a@(Universal _) = a

  apply subst (Existential pairs constants) = Existential (apply subst pairs) constants


instance Substitute c => Substitute (x, c) where
  apply :: Substitution -> (x, c) -> (x, c)
  apply subst (x, c) = (x, apply subst c)


instance Substitute Claim where
  apply :: Substitution -> Claim -> Claim
  apply subst c@C.Claim{ formula, justification }
    = c { formula = apply subst formula
        , justification = apply subst justification }


instance Substitute Justification where
  apply :: Substitution -> Justification -> Justification
  apply _ j@Rule{} = j

  apply _ j@Theorem{} = j

  apply _ j@Unproved = j

  apply _ j@Induction{} = j

  apply subst j@Substitution{ on' } = j{ on' = apply subst on' }


instance Substitute b => Substitute [b] where
  apply :: Substitution -> [b] -> [b]
  apply _ [] = []

  apply subst (b : bs) = apply subst b : apply subst bs


instance Substitute a => Substitute (Constraint a) where
  apply :: Substitution -> Constraint a -> Constraint a
  apply subst (a :≡: a') = apply subst a :≡: apply subst a'


instance Substitute Environment where
  apply subst e@Env { assert'scope }
    = e{ assert'scope = Map.map (apply subst) assert'scope }


instance Substitute Assertion where
  apply subst (Assumed fm) = Assumed (apply subst fm)
  apply subst (Claimed fm) = Claimed (apply subst fm)
  apply subst (Axiom fm) = Axiom (apply subst fm)
  apply subst (Derived assumption fm) = Derived (apply subst assumption) (apply subst fm)


--  TODO: report this error message as not correct
{-
• Illegal instance declaration for ‘Substitute b [a]’:
    All instance types must be of the form (T a1 ... an)
    where a1 ... an are *distinct type variables*,
    and each type variable appears at most once in the instance head.
• In the instance declaration for ‘Substitute b [a]’
• Perhaps you intended to use FlexibleInstancestypecheck
-}
--  each type variable appears at most once in each class argument not in the whole head
-- instance Substitute a a => Substitute b [a] where
  -- apply = undefined


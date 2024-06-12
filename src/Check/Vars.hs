{-# LANGUAGE UndecidableInstances #-}

module Check.Vars where


import Data.Set qualified as Set
import Data.Foldable ( foldl' )

import Syntax.Term ( Term(..), Var(..), Free(..), Rigid(..), Constant )
import Syntax.Formula ( Formula(Exists, Atom, Not, And, Or, Impl, Eq, Forall) )
import Syntax.Formula qualified as F
import Syntax.Relation ( Relation(..), Rel'Args(..) )
import Syntax.Judgment
import Syntax.Claim qualified as C
import Syntax.Justification
import Syntax.Case ( Case(..) )
import Syntax.Proof ( Proof(..) )
import Syntax.Assumption ( Assumption(..) )


class Ord v => Vars v a where
  free :: a -> Set.Set v


instance Vars Free Var where
  free :: Var -> Set.Set Free
  free (Free f) = Set.singleton f

  free (Rigid _) = Set.empty


instance Vars Free Term where
  free :: Term -> Set.Set Free
  free (Bound _) = Set.empty

  free (App _ terms) = foldl' (\ s t -> s `Set.union` free t) Set.empty terms

  free (Var v) = free v


instance Vars Free Formula where
  free :: Formula -> Set.Set Free
  free F.True = Set.empty
  
  free F.False = Set.empty
  
  free (Atom relation) = free relation
  
  free (Not fm) = free fm
  
  free (And left right) = free left `Set.union` free right
  
  free (Or left right) = free left `Set.union` free right
  
  free (Impl left right) = free left `Set.union` free right
  
  free (Eq left right) = free left `Set.union` free right
  
  free (Forall _ fm) = free fm
  
  free (Exists _ fm) = free fm


instance Vars Free Relation where
  free :: Relation -> Set.Set Free
  free (Rel _ rel'args) = free rel'args
  
  free (Meta'Rel _) = Set.empty


instance Vars Free Rel'Args where
  free :: Rel'Args -> Set.Set Free
  free (RL'Terms terms) = free terms
  free (RL'Formulae fms) = free fms


instance Vars Free C.Claim where
  free C.Claim{ C.formula, C.justification } = free formula `Set.union` free justification


-- instance Vars Constant Justification where
--   free Rule { } = Set.empty
--   free Theorem { } = Set.empty
--   free Unproved = Set.empty
--   free Induction { } = Set.empty
--   free Substitution { on' } = free on'
--   free Case'Analysis { proofs } = free proofs


instance Vars Free Justification where
  free :: Justification -> Set.Set Free
  free Rule{ } = Set.empty
  free Theorem { } = Set.empty
  free Unproved = Set.empty
  free Induction { } = Set.empty
  free Substitution { on' } = free on'
  free Case'Analysis { proofs } = free proofs


instance Vars Free Proof where
  free (Proof{ assumption, derivations }) = free assumption `Set.union` free derivations


-- instance Vars Constant Proof where
--   --  Constants registered in the assumption should not be collected now. They are not "free".
--   --  They should also not be collected from derivations.
--   --  But other constants from the assumption and from all the derivations should be collected.
--   free (Proof{ assumption = Formula formulae, derivations }) = free (map snd formulae) `Set.union` free derivations
--   free (Proof{ assumption = Universal constant, derivations }) = undefined
--   free (Proof{ assumption = Existential formula constants, derivations }) = undefined


instance Vars Free Assumption where
  free (Formula formulae) = free (map snd formulae)
  free (Universal constant) = Set.empty
  free (Existential formula constants) = free (snd formula)


instance Vars Free Judgment where
  free (Sub'Proof proof) = free proof
  free (Claim claim) = free claim
  free (Alias _ fm) = free fm
  free (Prove fm) = free fm


-- instance Vars Constant Judgment where
--   free (Sub'Proof proof) = free proof
--   free (Claim claim) = free claim
--   free (Alias _ fm) = free fm


instance Vars Free Case where
  free (Case _ proof) = free proof


-- instance Vars Constant Case where
--   free (Case term proof) = free proof `Set.difference` free term



instance Vars Free a => Vars Free [a] where
  free = foldl' (\ s a -> s `Set.union` free a) Set.empty

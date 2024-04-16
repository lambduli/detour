{-# LANGUAGE UndecidableInstances #-}

module Check.Vars where


import Data.Set qualified as Set
import Data.Foldable ( foldl' )

import Syntax.Term ( Term(..), Free, Constant )
import Syntax.Formula ( Formula(Exists, Atom, Not, And, Or, Impl, Eq, Forall) )
import Syntax.Formula qualified as F
import Syntax.Relation ( Relation(..) )
import Syntax.Judgment
import Syntax.Claim qualified as C
import Syntax.Justification


--  TODO: Do I even use this type class anywhere?

class Ord v => Vars v a where
  free :: a -> Set.Set v


instance Vars Free Term where
  free :: Term -> Set.Set Free
  free (Bound _) = Set.empty

  free (App _ terms) = foldl' (\ s t -> s `Set.union` free t) Set.empty terms

  free (Free f) = Set.singleton f


instance Vars Constant Term where
  free :: Term -> Set.Set Constant
  free (Bound _) = Set.empty

  free (App c terms) = foldl' (\ s t -> s `Set.union` free t) (Set.singleton c) terms

  free (Free _) = Set.empty


instance (Vars a Term, Ord a) => Vars a Formula where
  free :: Formula -> Set.Set a
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


instance (Vars a Term, Ord a) => Vars a Relation where
  free :: Relation -> Set.Set a
  free (Rel _ terms) = free terms
  
  free (Meta'Rel _) = Set.empty


instance (Vars a Formula, Vars a Term, Ord a) => Vars a C.Claim where
  free C.Claim{ C.formula, C.justification } = free formula `Set.union` free justification


instance (Vars a Term, Ord a) => Vars a Justification where
  free Rule { } = Set.empty
  free Theorem { } = Set.empty
  free Unproved = Set.empty
  free Induction { } = Set.empty
  free Substitution { on' } = free on'


instance (Ord v, Vars v a) => Vars v [a] where
  free = foldl' (\ s a -> s `Set.union` free a) Set.empty

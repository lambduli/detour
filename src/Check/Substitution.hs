module Check.Substitution where


import Data.List ( find )

import Syntax.Term ( Free, Bound, Term, Rigid )
import Syntax.Formula ( Formula )
import Syntax.Relation ( Prop'Var )
import Syntax.Type ( Type )


--  TODO: refactor??? #var
data Binding  = Free'2'Term Free Term
              | Rigid'2'Term Rigid Term
              | Bound'2'Term Bound Term
              | Prop'2'Formula Prop'Var Formula
              | Meta'2'Type String Type
  deriving (Show, Eq)


type Substitution = [Binding]


empty :: Substitution
empty = []


infix 5 ==>

class Bind a b | a -> b where
  (==>) :: a -> b -> Substitution
  lookup :: a -> Substitution -> Maybe b
  remove :: a -> Substitution -> Substitution


instance Bind Free Term where
  (==>) :: Free -> Term -> Substitution
  (==>) f t = [Free'2'Term f t]

  lookup :: Free -> Substitution -> Maybe Term
  lookup k subst = do
    Free'2'Term _ t <- find (\ case Free'2'Term f _ | f == k -> True
                                    _ -> False) subst
    return t

  remove :: Free -> Substitution -> Substitution
  remove f subst = filter (\ case Free'2'Term free _ -> free /= f
                                  _ -> False) subst


instance Bind Bound Term where
  (==>) :: Bound -> Term -> Substitution
  (==>) b t = [Bound'2'Term b t]

  lookup :: Bound -> Substitution -> Maybe Term
  lookup k subst = do
    Bound'2'Term _ t <- find (\ case  Bound'2'Term f _ | f == k -> True
                                      _ -> False) subst
    return t

  remove :: Bound -> Substitution -> Substitution
  remove bound subst = filter (\ case Bound'2'Term b _ -> bound /= b
                                      _ -> True) subst


instance Bind Rigid Term where
  (==>) :: Rigid -> Term -> Substitution
  (==>) f t = [Rigid'2'Term f t]

  lookup :: Rigid -> Substitution -> Maybe Term
  lookup k subst = do
    Rigid'2'Term _ t <- find (\ case  Rigid'2'Term f _ | f == k -> True
                                      _ -> False) subst
    return t

  remove :: Rigid -> Substitution -> Substitution
  remove f subst = filter (\ case Rigid'2'Term free _ -> free /= f
                                  _ -> True) subst


instance Bind Prop'Var Formula where
  (==>) :: Prop'Var -> Formula -> Substitution
  (==>) p f = [Prop'2'Formula p f]

  lookup :: Prop'Var -> Substitution -> Maybe Formula
  lookup k subst = do
    Prop'2'Formula _ t <- find (\ case  Prop'2'Formula f _ | f == k -> True
                                        _ -> False) subst
    return t

  remove :: Prop'Var -> Substitution -> Substitution
  remove prop subst = filter (\ case  Prop'2'Formula p _ -> prop /= p
                                      _ -> True) subst


instance Bind String Type where
  (==>) :: String -> Type -> Substitution
  (==>) p f = [Meta'2'Type p f]

  lookup :: String -> Substitution -> Maybe Type
  lookup k subst = do
    Meta'2'Type _ t <- find (\ case Meta'2'Type f _ | f == k -> True
                                    _ -> False) subst
    return t

  remove :: String -> Substitution -> Substitution
  remove prop subst = filter (\ case  Meta'2'Type p _ -> prop /= p
                                      _ -> True) subst

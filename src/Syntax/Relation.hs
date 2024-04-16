module Syntax.Relation where

import Data.List qualified as List


import Syntax.Term ( Term )


data Relation = Rel String [Term]     -- P(x, ƒ(x, y))
              | Meta'Rel Prop'Var
  deriving (Eq, Ord)


instance Show Relation where
  show (Rel n args) = n ++ "(" ++ List.intercalate ", " (map show args) ++ ")"
  show (Meta'Rel prop'var) = show prop'var


newtype Prop'Var = Prop'Var String
  deriving (Eq, Ord)


instance Show Prop'Var where
  show (Prop'Var n) = '_' : n

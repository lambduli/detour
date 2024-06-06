module Syntax.Relation where

import Data.List qualified as List


import Syntax.Term ( Term )
import {-# SOURCE #-} Syntax.Formula


data Relation = Rel String Rel'Args     -- P(x, ƒ(x, y))
              | Meta'Rel Prop'Var
  deriving (Eq)


instance Show Relation where
  show (Rel n (RL'Terms args)) = n ++ "(" ++ List.intercalate ", " (map show args) ++ ")"
  show (Rel n (RL'Formulae args)) = n ++ "(" ++ List.intercalate ", " (map show args) ++ ")"
  show (Meta'Rel prop'var) = show prop'var


newtype Prop'Var = Prop'Var String
  deriving (Eq, Ord)


instance Show Prop'Var where
  show (Prop'Var n) = '_' : n


data Rel'Args = RL'Terms [Term]
              | RL'Formulae [Formula]
  deriving (Eq)

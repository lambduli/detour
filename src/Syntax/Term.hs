module Syntax.Term where


import Data.List ( intercalate )


data Term = Bound Bound                 -- x, y, z
          | App Constant [Term]         -- ƒ(x, y), αᶜ, aᶜ, β(), b()
          | Free Free                   -- a, b, c
  deriving (Eq, Ord)


newtype Bound = B String
  deriving (Eq, Ord)


data Free = F String
  deriving (Eq, Ord)


data Constant = C String
  deriving (Eq, Ord)


pattern Bound'Var :: String -> Term
pattern Bound'Var n = Bound (B n)


pattern Free'Var :: String -> Term
pattern Free'Var n = Free (F n)


pattern Const :: String -> Term
pattern Const n = App (C n) []


instance Show Term where
  show (Bound n) = show n ++ "ᵇ"
  show (App c []) = show c ++ "ᶜ"
  show (App c terms) = (show c) ++ "(" ++ intercalate ", " (map show terms) ++ ")"
  show (Free n) = show n


instance Show Bound where
  show (B n) = n


instance Show Free where
  show (F n) = n


instance Show Constant where
  show (C n) = n

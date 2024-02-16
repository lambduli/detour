module Syntax.Term where


import Data.List ( intercalate )


data Term = Var String                  -- x, y, z
          | Fn String [Term]            -- ƒ(x, y), αᶜ, aᶜ, β(), b()
  deriving (Eq, Ord)


instance Show Term where
  show (Var n) = n
  show (Fn n []) = n
  show (Fn n terms) = n ++ "(" ++ intercalate ", " (map show terms) ++ ")"

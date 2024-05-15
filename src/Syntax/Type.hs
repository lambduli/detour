module Syntax.Type where


import Data.List ( intercalate )


data Type = Type'Const String
          | Type'Var String
          | Type'Fn Type Type
  deriving (Eq)


instance Show Type where
  show (Type'Const str) = str ++ "ᶜ"
  show (Type'Var str) = str ++ "?"
  show (Type'Fn arg't res't) = show arg't ++ " -> " ++ show res't


data Type'Scheme = Forall'T [String] Type
  deriving (Eq)


instance Show Type'Scheme where
  show (Forall'T params t) = "forall " ++ intercalate " " params ++ " . " ++ show t

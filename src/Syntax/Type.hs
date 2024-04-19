module Syntax.Type where


newtype Type = Type String
  deriving (Show, Eq)


--  TODO: Replace the above with the below.
-- data Type = Type'Const String
--           | Type'Var String
--   deriving (Show, Eq)

module Check.Environment where


import Data.Map.Strict qualified as Map

import Syntax.Theorem ( Theorem )

import {-# SOURCE #-} Check.Assertion ( Assertion )


--  TODO: When I implement the simple version of type-checking
--    [ for the stuff like ∀ ℕ P(ℕ) to be instantiable only to variables and
--      terms of "type" ℕ ]
--        This is not something I am dealing with right now.
data Environment = Env{ lem                 :: Bool
                      , theorems            :: Map.Map String Theorem
                      , depth               :: Int
                      , assert'scope        :: Map.Map String Assertion }
  deriving (Show, Eq)


init'env :: Bool -> Environment
init'env lem = Env{ lem           = lem
                  , theorems      = Map.empty
                  , assert'scope  = Map.empty
                  , depth         = 0 }

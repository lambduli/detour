module Check.Environment where


import Data.Map.Strict qualified as Map

import Syntax.Formula ( Formula )
import Syntax.Term( Term )
import Syntax.Theorem ( Theorem )
import Syntax.Judgment ( Judgment )

import Check.Check ( Check )
import Check.Meta ( Meta)


--  TODO: When I implement the simple version of type-checking
--    [ for the stuff like ∀ ℕ P(ℕ) to be instantiatable only to variables and
--      terms of "type" ℕ ]
--        This is not something I am dealing with right now.
data Environment = Env{ mode :: Logic
                      , theorems :: Map.Map String Theorem
                      , var'scope :: Map.Map String Int
                      , judg'scope :: Map.Map String (Either Formula Judgment) }
                        --  It's either formula or judgment.
                        --  The formula is for assumptions.
                        --  The Judgment is for sub-proofs and claims.
  deriving (Show, Eq)


data Logic = Classical | Intuitionistic
  deriving (Show, Eq)


look'up'theorem :: String -> Check Theorem
look'up'theorem name = do
  thms <- asks theorems

  case Map.lookup name thms of
    Nothing -> do
      throwError $! Unknown'Theorem name
    
    Just thm -> do
      return thm

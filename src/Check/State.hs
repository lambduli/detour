module Check.State where


import Data.Map.Strict qualified as Map


import Syntax.Term ( Term, Free, Constant )
import Syntax.Formula ( Formula )

import Check.Constraint ( Constraint )


data Level  = Unrestricted Int
            | Restricted Int
  deriving (Show, Eq, Ord)
  --  TODO: remove Ord; implement the comparison in a correct way


data State = State{ counter             :: Int
                  , term'constraints    :: [Constraint Term]
                  , formula'constraints :: [Constraint Formula]
                  , const'depth'context :: Map.Map Constant Level
                  , free'depth'context  :: Map.Map Free Int }
  deriving (Show, Eq)


init'state :: State
init'state = State{ counter             = 0
                  , term'constraints    = []
                  , formula'constraints = []
                  , const'depth'context = Map.empty
                  , free'depth'context  = Map.empty }

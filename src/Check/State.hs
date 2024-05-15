module Check.State where


import Data.Map.Strict qualified as Map


import Syntax.Term ( Term, Free, Constant, Rigid )
import Syntax.Formula ( Formula )
import Syntax.Type ( Type, Type'Scheme )
import Syntax.Jud ( Jud )
import Syntax.Syntax ( Syntax )

import Check.Constraint ( Constraint )


data Level  = Unrestricted Int
            | Restricted Int
  deriving (Show, Eq)


data State = State{ counter             :: Int
                  , term'constraints    :: [Constraint Term]
                  , formula'constraints :: [Constraint Formula]
                  , type'constraints    :: [Constraint Type]
                  , free'depth'context  :: Map.Map Free Int
                  , rigid'depth'context :: Map.Map Rigid Int
                  , typing'ctx          :: Map.Map String Type'Scheme
                  , judgments           :: [Jud]
                  , syntax              :: [(String, Syntax)] }
  deriving (Show, Eq)


empty'state :: State
empty'state = State { counter             = 0
                    , term'constraints    = []
                    , formula'constraints = []
                    , type'constraints    = []
                    , free'depth'context  = Map.empty
                    , rigid'depth'context = Map.empty
                    , typing'ctx          = Map.empty
                    , judgments           = []
                    , syntax              = [] }

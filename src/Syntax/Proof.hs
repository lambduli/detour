module Syntax.Proof where


import Data.List.Extra ( intercalate )

import Syntax.Assumption ( Assumption )
import Syntax.Judgment ( Judgment )


data Proof = Proof{ name :: Maybe String
                  , assumption :: Assumption
                  , derivations :: [Judgment] }
  deriving (Eq)


instance Show Proof where
  show Proof{ name = Nothing, assumption, derivations }
    = "_" ++ " : "
        ++ "| " ++ show assumption ++ "\n"
        ++ intercalate "\n    | " (map show derivations)
  show Proof{ name = Just n, assumption, derivations }
    = n ++ " : "
        ++ "| " ++ show assumption ++ "\n"
        ++ intercalate "\n    | " (map show derivations)

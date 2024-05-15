module Syntax.Assumption where


import Data.List.Extra ( intercalate )


import Syntax.Formula ( Formula )
import Syntax.Term ( Rigid )
import Syntax.Type ( Type(..), Type'Scheme )


data Assumption = Formula [(Maybe String, Formula)]
                | Universal [(Rigid, Type'Scheme)]
                | Existential (Maybe String, Formula) [(Rigid, Type'Scheme)]
  deriving (Eq)


instance Show Assumption where
  show (Formula bindings) = concatMap (\case  (Nothing, fm) -> "_ : " ++ show fm ++ "\n"
                                              (Just n, fm) -> n ++ " : " ++ show fm ++ "\n") bindings
  
  show (Universal constants) = "for all " ++ intercalate ", " (map show constants)
  
  show (Existential (Nothing, fm) constants  ) = "_ : " ++ show fm ++ " for some " ++ intercalate ", " (map show constants) ++ "\n"
  show (Existential (Just n, fm) constants) = n ++ " : " ++ show fm ++ " for some " ++ intercalate ", " (map show constants) ++ "\n"

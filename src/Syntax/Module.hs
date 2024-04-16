module Syntax.Module where


import Data.List.Extra ( intercalate )

-- import Syntax.Definition ( Definition )
import Syntax.Term ( Term )
import Syntax.Formula ( Formula )
import Syntax.Theorem ( Theorem )


data Module = Module  { name      :: String
                      , constants :: [String] --  TODO: Why do I even need this?
                      , aliases   :: [(String, Term)] --  TODO: Why do I even need this?
                      , axioms    :: [(String, Formula)]
                      , theorems  :: [Theorem] }
                      
                      -- , definitions :: [Definition] }
  deriving (Eq)


instance Show Module where
  show Module { name, constants, aliases, axioms, theorems }
    = "module " ++ name
        ++ "\n\n" ++
      "constants : " ++ intercalate ", " (map show constants)
        ++ "\n\n" ++
      "aliases : " ++ intercalate ", " (map show aliases)
        ++ "\n\n" ++
      "axioms : " ++ intercalate ", " (map show axioms)
        ++ "\n\n" ++
      intercalate "\n\n" (map show theorems)

module Syntax.Module where


import Data.List.Extra ( intercalate )

-- import Syntax.Definition ( Definition )
import Syntax.Term ( Term )
import Syntax.Formula ( Formula )
import Syntax.Theorem ( Theorem )
import Syntax.Type ( Type'Scheme )
import Syntax.Syntax ( Syntax )
import Syntax.Jud ( Jud )


data Module = Module  { name      :: String
                      , constants :: [(String, Type'Scheme)]
                      , aliases   :: [(String, Term)] --  TODO: Why do I even need this?
                      , axioms    :: [(String, Formula)]
                      , syntax    :: [(String, Syntax)]
                      , judgments :: [Jud]
                      , theorems  :: [Theorem] }
                      
                      --  , definitions :: [Definition] }
  deriving (Eq)


instance Show Module where
  show Module { name, constants, aliases, axioms, syntax, judgments, theorems }
    = "module " ++ name
        ++ "\n\n" ++
      "constants : " ++ intercalate ", " (map show constants)
        ++ "\n\n" ++
      "aliases : " ++ intercalate ", " (map show aliases)
        ++ "\n\n" ++
      "axioms : " ++ intercalate ", " (map show axioms)
        ++ "\n\n" ++
      "syntax : " ++ intercalate "  \n" (map show syntax)
        ++ "\n\n" ++
      "judgments : " ++ intercalate "  \n" (map show judgments)
        ++ "\n\n" ++
      intercalate "\n\n" (map show theorems)

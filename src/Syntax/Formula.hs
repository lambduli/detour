module Syntax.Formula where


import Prelude hiding (True, False)
import Prelude qualified as P
import Data.List ( intercalate )

-- import Syntax.Term ( Term(..) )
import Syntax.Relation ( Relation(..), Prop'Var(..) )
import Syntax.Type ( Type )



data Formula  = True                    -- ⊤
              | False                   -- ⊥
              | Atom Relation           -- P(x, ƒ(x, y))
              | Not Formula             -- ¬P(x, ƒ(x, y))
              | And Formula Formula     -- ⊤ ∧ ⊤
              | Or Formula Formula      -- ⊤ ∨ ⊥
              | Impl Formula Formula    -- ⊥ ⟹ R
              | Eq Formula Formula      -- F(x) ⟺ G(y)
              -- | Forall String Formula   -- ∀ x : P(x)
              -- | Exists String Formula   -- ∃ y : G(y)

              | Forall (String, Type) Formula  --  ∀ ℕ : P(ℕ)
              | Exists (String, Type) Formula  --  ∃ ℕ : P(ℕ)
  deriving (Eq)


instance Show Formula where
  show :: Formula -> String
  show True = "⊤"
  show False = "⊥"
  show (Atom (Rel n [])) = n
  show (Atom (Rel n terms)) = n ++ "(" ++ intercalate ", " (map show terms) ++ ")"
  show (Atom (Meta'Rel (Prop'Var n))) = "_" ++ n
  show (Not p) | is'compound p  = "¬(" ++ show p ++ ")"
  show (Not p) = "¬" ++ show p

  show (And p q)
    | (And _ _) <- p, (And _ _) <- q  = show p ++ " ∧ " ++ show q
    | (And _ _) <- p, is'compound q  = show p ++ " ∧ (" ++ show q ++ ")"
    | (And _ _) <- q, is'compound p  = "(" ++ show p ++ ") ∧ " ++ show q
    | is'compound p, is'compound q  = "(" ++ show p ++ ") ∧ (" ++ show q ++ ")"
    | is'compound p                 = "(" ++ show p ++ ") ∧ " ++ show q
    | is'compound q                 = show p ++ " ∧ (" ++ show q ++ ")"

  show (And p q) = show p ++ " ∧ " ++ show q
  -- show (And p q) = "[" ++ show p ++ " ∧ " ++ show q ++ "]"   -- just leaving this for future debugging
  
  show (Or p q)
    | (Or _ _) <- p, (Or _ _) <- q  = show p ++ " ∨ " ++ show q
    | (Or _ _) <- p, is'compound q  = show p ++ " ∨ (" ++ show q ++ ")"
    | (Or _ _) <- q, is'compound p  = "(" ++ show p ++ ") ∨ " ++ show q
    | is'compound p, is'compound q  = "(" ++ show p ++ ") ∨ (" ++ show q ++ ")"
    | is'compound p                 = "(" ++ show p ++ ") ∨ " ++ show q
    | is'compound q                 = show p ++ " ∨ (" ++ show q ++ ")"
  
  show (Or p q) = show p ++ " ∨ " ++ show q
  -- show (Or p q) = "[" ++ show p ++ "] ∨ [" ++ show q ++ "]"   -- just leaving this for future debugging

  show (Impl p q)
    --  F ==> (G ==> H)
    | (Impl _ _) <- q, (Not _) <- p = show p ++ " ==> " ++ show q
    | (Impl _ _) <- q, not (is'compound p) = show p ++ " ==> " ++ show q

    | (Not _) <- p, (Not _) <- q = show p ++ " ==> " ++ show q
    | (Not _) <- p, not (is'compound q) = show p ++ " ==> " ++ show q
    | (Not _) <- p = show p ++ " ==> " ++ show q
    | (Not _) <- q, not (is'compound p) = show p ++ " ==> " ++ show q
    | (Not _) <- q = "(" ++ show p ++ ") ==> " ++ show q

    | not (is'compound p), not (is'compound q) = show p ++ " ==> " ++ show q
    | not (is'compound p) = show p ++ " ==> (" ++ show q ++ ")"
    | not (is'compound q) = "(" ++ show p ++ ") ==> " ++ show q

  -- show (Impl p q) = show p ++ " ==> " ++ show q
  show (Impl p q) = "(" ++ show p ++ ") ==> (" ++ show q ++ ")"

  -- show (Eq p q) = show p ++ " <==> " ++ show q
  show (Eq p q) = "(" ++ show p ++ ") <==> (" ++ show q ++ ")"

  -- show (Forall x p) = "∀ " ++ x ++ " : " ++ show p
  -- show (Exists x p) = "∃ " ++ x ++ " : " ++ show p

  show (Forall (x, t) p) = "∀ " ++ x ++ " : " ++ show p
  show (Exists (x, t) p) = "∃ " ++ x ++ " : " ++ show p


is'compound :: Formula -> Bool
is'compound True = P.False
is'compound False = P.False
is'compound (Atom (Rel _ _)) = P.False
is'compound (Atom (Meta'Rel _)) = P.False
is'compound (Not _) = P.True
is'compound (And _ _) = P.True
is'compound (Or _ _) = P.True
is'compound (Impl _ _) = P.True
is'compound (Eq _ _) = P.True
-- is'compound (Forall _ _) = P.True
-- is'compound (Exists _ _) = P.True
is'compound (Forall _ _) = P.True
is'compound (Exists _ _) = P.True

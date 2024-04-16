{-# LANGUAGE FunctionalDependencies #-}

module Check.Assertion where


import Control.Monad.Except ( throwError )

import Syntax.Formula ( Formula(..) )
import Syntax.Assumption ( Assumption )

import Check.Check ( Check )
import Check.Error ( Error(..) )


data Assertion  = Assumed Formula
                | Claimed Formula
                | Axiom Formula
                | Derived Assumption Formula
  deriving (Show, Eq)


asserts'formula :: Assertion -> Check Formula
asserts'formula (Assumed fm) = return fm
asserts'formula (Claimed fm) = return fm
asserts'formula (Axiom fm) = return fm
asserts'formula (Derived _ _) = throwError $! Err "Unexpected sub-proof. I was expecting an assertion of a formula (claim/axiom/assumption) but was given a name of a proof."

module Check.Module where


import Data.Map.Strict qualified as Map

import Control.Monad.State ( MonadState(put) )
import Control.Monad.Except ( throwError )
import Control.Monad.Reader ( local )
import Control.Monad ( unless )

import Check.Check ( Check, because )
import Check.Environment ( Environment(assert'scope) )
import Check.Error ( Error(..) )
import Check.State ( State(..), empty'state )
import Check.State qualified as S
import Check.Theorem ( check'theorem )
import Check.Assertion ( Assertion(..) )

import Syntax.Module ( Module(Module) )
import Syntax.Module qualified as M
import Syntax.Type ( Type(..), Type'Scheme(..) )
import Syntax.Syntax ( Constructor(..), Syntax(..) )
import Syntax.Theorem qualified as T


-- TODO:  This module implements checking for the whole module.
--        The idea is to load all the axioms into the environment
--        and check one theorem at a time.


--  TODO:   Later it should return the substitution.
check'module :: Module -> Check ()
check'module Module { M.name, M.constants, M.aliases, M.axioms, M.syntax, M.judgments, M.theorems } = do
  let patch = Map.fromList $! map (\ (n, fm) -> (n, Axiom fm)) axioms

  local (\ e -> e{ assert'scope = (assert'scope e) `Map.union` patch })
        (mapM_ (\ t -> clean'state >> because ("when I was trying to check the theorem `" ++ T.name t ++ "'") (check'theorem t)) theorems)

  where clean'state :: Check ()
        clean'state = do
          let ctx'1 = Map.fromList constants

          let ctx'2 = Map.fromList $! concatMap (\ (tn, Syntax constrs) -> map (\ (Constructor c'name types) -> (c'name , Forall'T [] (foldr Type'Fn (Type'Const tn) types))) constrs) syntax

          unless  (Map.null (Map.intersection ctx'1 ctx'2))
                  (throwError $! Err "Constants section might not define syntax constructors.")

          let t'ctx = ctx'1 `Map.union` ctx'2

          let new'state = empty'state { typing'ctx = t'ctx
                                      , S.judgments = judgments
                                      , S.syntax = syntax }

          put new'state

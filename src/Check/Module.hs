module Check.Module where


import Data.Map.Strict qualified as Map

import Control.Monad.State ( MonadState(get, put) )
import Control.Monad.Reader ( local )

import Check.Check ( Check )
import Check.Environment ( Environment(assert'scope) )
import Check.Error ( Error )
import Check.State ( State, init'state )
import Check.Theorem ( check'theorem )
import Check.Assertion ( Assertion(..) )

import Syntax.Module ( Module(..) )


-- TODO:  This module implements checking for the whole module.
--        The idea is to load all the axioms into the environment
--        and check one theorem at a time.

--        This file needs to initialize the environment and state.
--        This means these functions are gonna work over Check monad stack.
--        Maybe I will leave this to Main


--  I only really care about the list of definitions int he Module.
--  TODO: Start writing the function that does the checking!!!


--  TODO: This is a very simple version of the function.
--        Later it should return 
check'module :: Module -> Check ()
check'module Module { name, constants, aliases, axioms, theorems } = do

  let patch = Map.fromList $! map (\ (n, fm) -> (n, Axiom fm)) axioms

  local (\ e -> e{ assert'scope = (assert'scope e) `Map.union` patch })
        (mapM_ (\ t -> check'theorem t >> clean'state) theorems)


clean'state :: Check ()
clean'state = do
  put init'state

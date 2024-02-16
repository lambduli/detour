module Check.Module where


import Check.Check ( Check )
import Check.Environment ( Environment )
import Check.Error ( Error )
import Check.State ( State )
import Check.Theorem ( Theorem )


-- TODO:  This module implements checking for the whole module.
--        The idea is to load all the axioms into the environment
--        and check one theorem at a time.

--        This file needs to initialize the environment and state.
--        This means these functions are gonna work over Check monad stack.
--        Maybe I will leave this to Main


--  I only really care about the list of definitions int he Module.
--  TODO: Start writing the function that does the checking!!!

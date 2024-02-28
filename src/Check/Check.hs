module Check.Check where


import Control.Monad.Reader ( ReaderT(runReaderT) )
import Control.Monad.State ( MonadState(get, put), gets, evalStateT, StateT )
import Control.Monad.Except ( Except, runExcept )

import Check.Environment ( Environment )
import Check.Error ( Error )
import Check.State ( State )


type Check a
  = ReaderT
      Environment
      (StateT
        State
        (Except Error))
      a

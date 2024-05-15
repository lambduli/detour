module Check.Check where


import Control.Monad.Reader ( ReaderT )
import Control.Monad.State ( StateT )
import Control.Monad.Except ( Except )

import Check.Error ( Error(..) )
import Check.Environment ( Environment(..) )
import Check.State ( State(..) )

import Syntax.Type ( Type )


type Check a
  = ReaderT
      Environment
      (StateT
        State
        (Except Error))
      a


fresh'type :: Check Type
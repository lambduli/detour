module Check.Types where


import Syntax.Type ( Type'Scheme(..), Type(..) )

import {-# SOURCE #-} Check.Check ( Check )


instantiate'scheme :: Monad m => Type'Scheme -> Check m Type

module Check.Types where


import Syntax.Type ( Type'Scheme(..), Type(..) )

import {-# SOURCE #-} Check.Check ( Check )


instantiate'scheme :: Type'Scheme -> Check Type

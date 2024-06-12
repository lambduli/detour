module Check.Types where


import Syntax.Type ( Type'Scheme(..), Type(..) )

import Check.Check ( Check, fresh'type )
import Check.Substitute
import Check.Substitution


instantiate'scheme :: Monad m => Type'Scheme -> Check m Type
instantiate'scheme (Forall'T vars ty) = do
  mappings <- mapM (\ s -> do { t <- fresh'type ; return (s, t) } ) vars
  let subst = map (\ (s, t) -> Meta'2'Type s t) mappings
  return $! apply subst ty



instantiate'scheme'at :: Monad m => Type'Scheme -> [Type] -> Check m Type
instantiate'scheme'at (Forall'T vars ty) types = do
  mappings <- zip'and'fill vars types
  let subst = map (\ (s, t) -> Meta'2'Type s t) mappings
  return $! apply subst ty

  where zip'and'fill :: Monad m => [String] -> [Type] -> Check m [(String, Type)]
        zip'and'fill [] [] = return []

        zip'and'fill (s : ss) [] = do
          t <- fresh'type
          rest <- zip'and'fill ss []
          return ((s, t) : rest)

        zip'and'fill (s : ss) (t : ts) = do
          rest <- zip'and'fill ss ts
          return ((s, t) : rest)

        zip'and'fill _ _ = return []
        --  if the type-scheme doesn't have parameters there's no point in making the substitution

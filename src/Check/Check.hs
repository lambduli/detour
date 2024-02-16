module Check.Check where

type Check a
  = ReaderT
      Environment
      (StateT
        State
        (Except Error))
      a

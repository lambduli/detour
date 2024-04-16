module Main where


import Prelude hiding ( lex )

import Control.Monad.Reader ( runReaderT )
import Control.Monad.State ( runStateT )
import Control.Monad.Except ( runExcept )


import System.Environment ( getArgs )
import System.IO ( hFlush, stdout, openFile, IOMode(ReadMode), hGetContents )

import Data.List.Extra qualified as List

import Parser.Parser ( parse'module, lex )

import Check.Check
import Check.Environment ( init'env )
import Check.State
import Check.Module ( check'module )


--  TODO: parse the cmd line arguments
--        LEM?
--        just lex?
--        just parse?

main :: IO ()
main = do
  args <- getArgs

  mapM_ check'file args


  return ()



check'file :: String -> IO ()
check'file file'path = do
  file'handle <- openFile (List.trim file'path) ReadMode
  file'content <- hGetContents file'handle

  -- case lex file'content of
  --   Left (msg, toks) -> do
  --     putStrLn msg
  --     putStrLn "I parsed these tokens:"
  --     mapM_ (putStrLn . show) toks

  --   Right toks -> do
  --     putStrLn "I parsed these tokens:"
  --     mapM_ (putStrLn . show) toks

  -- putStrLn "----------------------------------------"

  case parse'module file'content of
    Left err -> do
      putStrLn ("error at " ++ file'path ++ ":" ++ err)
    Right mod -> do
      -- putStrLn "Module parsed"
      -- print mod

      case runExcept $ runStateT (runReaderT (check'module mod) (init'env True)) init'state of
        Left err -> do
          putStrLn ("❌ " ++ show err)

        Right ((), state) -> do
          putStrLn ("✅ module checked successfully")

  return ()


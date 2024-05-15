module Main where


import Prelude hiding ( lex )

import Control.Monad.Reader ( runReaderT )
import Control.Monad.State ( runStateT )
import Control.Monad.Except ( runExcept )


import System.Environment ( getArgs )
import System.IO ( openFile, IOMode(ReadMode), hGetContents )

import Data.List.Extra qualified as List
import Data.Map.Strict qualified as Map

import Parser.Parser ( parse'module, lex )

import Check.Environment ( init'env )
import Check.State ( empty'state )
import Check.Module ( check'module )

import Syntax.Module qualified as M


main :: IO ()
main = do
  args <- getArgs

  let (lem, file'paths) = split'args args

  mapM_ (check'file lem) file'paths

  return ()


split'args :: [String] -> (Bool, [String])
split'args [] = (False, [])
split'args ("--no-lem" : args) = (False, args)
split'args ("--lem" : args) = (True, args)
split'args args = (False, args) --  Default is --no-lem


check'file :: Bool -> String -> IO ()
check'file lem file'path = do
  file'handle <- openFile (List.trim file'path) ReadMode
  file'content <- hGetContents file'handle

  case lex file'content of
    Left (msg, toks) -> do
      putStrLn msg
      putStrLn "I parsed these tokens:"
      mapM_ (putStrLn . show) toks

    Right toks -> do
      putStrLn "I parsed these tokens:"
      mapM_ (putStrLn . show) toks

  putStrLn "----------------------------------------"

  case parse'module file'content of
    Left err -> do
      putStrLn ("error at " ++ file'path ++ ":" ++ err)
    Right mod -> do
      putStrLn "Module parsed"
      print mod
      putStrLn "\n\nModule printed"

      case runExcept $ runStateT (runReaderT (check'module mod) (init'env lem)) empty'state of
        Left err -> do
          putStrLn ("❌ " ++ show err)

        Right ((), state) -> do
          putStrLn ("✅ module checked successfully")

  return ()


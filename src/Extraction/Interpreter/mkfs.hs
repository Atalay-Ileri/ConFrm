{-# LANGUAGE PackageImports #-}
module Main where

import qualified File
import qualified Interpreter
import qualified Data.Map
import Directory
import qualified System.Directory
import System.Environment
import Data.IORef
import System.IO
import System.Posix.IO
import "unix-bytestring" System.Posix.IO.ByteString

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fn] -> do
      confsInit fn
    _ -> do
      putStrLn $ "Usage: mkfs diskpath"

confsInit:: String -> IO ()
confsInit disk_fn = do
  print "--MKFS--"
  print disk_fn
  _ <- writeIORef Interpreter.txnList []
  _ <- writeIORef Interpreter.cache Data.Map.empty
  _ <- writeIORef Interpreter.cipherMap Data.Map.empty
  fs <- openFd disk_fn ReadWrite (Just 0o666) defaultFileFlags
  writeIORef Interpreter.fsImage fs
  File.init
  initializeDirMap
module Main where

import qualified File
import qualified Interpreter
import qualified Data.Map
import Directory
import qualified System.Directory
import System.Environment
import Data.IORef
import System.IO

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
  fs <- openBinaryFile disk_fn ReadWriteMode
  writeIORef Interpreter.fsImage fs
  File.init
  initializeDirMap
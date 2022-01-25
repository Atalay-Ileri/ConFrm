module Main where

import qualified File
import System.Environment

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fn] -> do
      putStrLn $ "Initializing file system"
      res <- File.init
      case res of
        Nothing -> error $ "mkfs failed"
        Just _ -> putStrLn "Initialization OK!"
    _ -> do
      putStrLn $ "Usage: mkfs diskpath"

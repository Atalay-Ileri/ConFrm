{-# LANGUAGE RankNTypes, MagicHash #-}

module Main where

import qualified Data.ByteString as BS
import qualified System.Directory
import Foreign.C.Error
import System.Posix.Types
import System.Posix.Files
import System.Posix.IO
import System.FilePath.Posix
import System.Fuse
import System.Environment
import Control.Concurrent.MVar
import Text.Printf
import Data.IORef
import System.IO
import Text.Read
import qualified Data.Map
import qualified System.Process
import qualified Data.List
import Control.Monad
import GHC.IO.Unsafe
import System.Posix.User
import qualified BaseTypes
import qualified File
import qualified Interpreter


-- Handle type for open files; we will use the inode number
type HT = BaseTypes.Coq_addr

verboseFuse :: Bool
verboseFuse = False

-- This controls whether HFuse will use upcalls (FUSE threads entering GHC runtime)
-- or downcalls (separate FUSE threads using a queue, and GHC accessing this queue
-- using its own threads).
useDowncalls :: Bool
useDowncalls = True

debug :: String -> IO ()
debug msg =
  if verboseFuse then
    putStrLn msg
  else
    return ()

debugStart :: Show a => String -> a -> IO ()
debugStart op msg = debug $ op ++ ": " ++ (show msg)

debugMore :: Show a => a -> IO ()
debugMore msg = debug $ " .. " ++ (show msg)

main :: IO ()
main = do
  args <- getArgs
  case args of
    fn:rest -> run_fuse fn rest
    _ -> putStrLn $ "Usage: fuse disk -f /tmp/ft"

run_fuse :: String -> [String] -> IO ()
run_fuse disk_fn fuse_args = do
  fileExists <- System.Directory.doesFileExist disk_fn
  {- 
    ds <- case disk_fn of
    "/tmp/crashlog.img" -> init_disk_crashlog disk_fn
    _ -> init_disk disk_fn
  -}
  _ <- writeIORef Interpreter.txnList []
  _ <- writeIORef Interpreter.cache Data.Map.empty
  _ <- writeIORef Interpreter.cipherMap Data.Map.empty
  s <- if fileExists
  then
    do
      putStrLn $ "Recovering file system"
      File.recover
  else
    do
      putStrLn $ "Initializing file system"
      fs <- openBinaryFile disk_fn ReadWriteMode
      _ <- writeIORef Interpreter.fsImage fs
      File.init
  putStrLn $ "Starting file system."
  fuseRun "confs" fuse_args (confsFSOps getFuseContext) defaultExceptionHandler

-- See the HFuse API docs at:
-- https://hackage.haskell.org/package/HFuse-0.2.1/docs/System-Fuse.html
confsFSOps :: IO FuseContext -> FuseOperations HT
confsFSOps getctx  = defaultFuseOps
  { fuseOpen = confsOpen
  , fuseRead = confsRead
  , fuseWrite = confsWrite
  , fuseRemoveLink = confsUnlink
  , fuseSetOwnerAndGroup = confsChown
  , fuseCreateDevice = confsCreateDevice
  , fuseCreateDirectory = confsCreateDirectory
  , fuseOpenDirectory = confsOpenDirectory
  }

-- needed for tests
confsCreateDevice :: FilePath -> EntryType -> FileMode -> DeviceID -> IO Errno
confsCreateDevice _ _ _ _ = return eOK

confsCreateDirectory :: FilePath -> FileMode -> IO Errno
confsCreateDirectory _ _ = return eOK

confsOpenDirectory :: FilePath -> IO Errno
confsOpenDirectory _ = return eOK
  
writeSubsets' :: [[(Integer, a)]] -> [[(Integer, a)]]
writeSubsets' [] = [[]]
writeSubsets' (heads : tails) =
    tailsubsets ++ (concat $ map (\ts -> map (\hd -> hd : ts) heads) tailsubsets)
  where
    tailsubsets = writeSubsets' tails

writeSubsets :: [(Integer, a)] -> [[(Integer, a)]]
writeSubsets writes = writeSubsets' addrWrites
  where
    addrWrites = Data.List.groupBy sameaddr writes
    sameaddr (x, _) (y, _) = (x == y)

-- I will use this as create, ignoring path, modes etc.
confsOpen :: FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
confsOpen _ _ _ = do
  uid <- System.Posix.User.getEffectiveUserID
  r <- File.create uid
  case r of
    Nothing -> return $ Left $ eIO
    Just inum -> return $ Right inum

-- use path as string representation of handle
confsUnlink :: FilePath -> IO Errno
confsUnlink path = do
  case readMaybe path of
    Just i -> do
      r <- File.delete i
      case r of
        Just _ -> return eOK
        Nothing -> return eIO
    Nothing -> return eIO

-- use file path as string rep of handle.
confsChown :: FilePath -> UserID -> GroupID -> IO Errno
confsChown path uid _  = do
  case readMaybe path of
    Just i -> do
      r <- File.change_owner i (fromIntegral (toInteger uid))
      case r of
        Just _ -> return eOK
        Nothing -> return eIO
    Nothing -> return eIO

blocksize :: Int
blocksize = BaseTypes.block_size `div` 8

data BlockRange =
  BR !Int !Int !Int   -- blocknumber, offset-in-block, count-from-offset

compute_ranges_int :: Int -> Int -> [BlockRange]
compute_ranges_int off count = map mkrange $ zip3 blocknums startoffs endoffs
  where
    mkrange (blk, startoff, endoff) = BR blk startoff (endoff-startoff)
    blocknums = [off `div` blocksize .. (off + count - 1) `div` blocksize]
    startoffs = [off `mod` blocksize] ++ replicate (length blocknums - 1) 0
    endoffs = replicate (length blocknums - 1) blocksize ++ [(off + count - 1) `mod` blocksize + 1]

compute_ranges :: FileOffset -> ByteCount -> [BlockRange]
compute_ranges off count =
  compute_ranges_int (fromIntegral off) (fromIntegral count)

confsRead :: FilePath -> HT -> ByteCount -> FileOffset -> IO (Either Errno BS.ByteString)
confsRead _ inum byteCount offset = do
  pieces <- mapM read_piece $ compute_ranges offset byteCount
  return $ Right $ BS.concat pieces
  where
    read_piece (BR blk off count) = do
      ok_buf <- File.read inum blk
      case ok_buf of
        Just buf ->
          return $ BS.take count $ BS.drop off $ buf
        Nothing ->
          error "Read ERROR"

compute_range_pieces :: FileOffset -> BS.ByteString -> [(BlockRange, BS.ByteString)]
compute_range_pieces off buf = zip ranges pieces
  where
    ranges = compute_ranges_int (fromIntegral off) (BS.length buf)
    pieces = map getpiece ranges
    getpiece (BR blk boff bcount) = BS.take (fromIntegral bcount) $ BS.drop (fromIntegral bufoff) buf
      where bufoff = (blk * blocksize) + boff - (fromIntegral off)

data WriteState =
   WriteOK !ByteCount
 | WriteErr !ByteCount

-- This should automatically extend if it passes file length
confsWrite :: FilePath -> HT -> BS.ByteString -> FileOffset -> IO (Either Errno ByteCount)
confsWrite _ inum bs offset = do
  mlen <- File.get_file_size inum
  case mlen of
    Just len -> do
      r <- foldM (write_piece inum len) (WriteOK 0) (compute_range_pieces offset bs)
      case r of
        WriteOK c -> return (Right c)
        WriteErr c ->
          if c == 0 then
            return (Left eIO)
          else
            return (Right c)
    Nothing -> do
      return (Left eIO)
  where
    write_piece _ _ (WriteErr c) (BR blk off cnt, piece_bs) = return (WriteErr c)
    write_piece inum init_len (WriteOK c) (BR blk off cnt, piece_bs) = do
      if blk < init_len then
        if cnt == blocksize then do
          r <- File.write inum (fromIntegral blk) piece_bs
          case r of
            Just _ -> return (WriteOK (c + (fromIntegral cnt)))
            Nothing -> return (WriteErr c)
        else do
          mob <- File.read inum (fromIntegral blk)
          case mob of
            Just old_block -> do
              let new_block = BS.append (BS.take (fromIntegral off) old_block) (BS.append piece_bs (BS.drop ((fromIntegral off) + (fromIntegral cnt)) old_block))
              r <- File.write inum (fromIntegral blk) new_block
              case r of
                Just _ -> return (WriteOK (c + (fromIntegral cnt)))
                Nothing -> return (WriteErr c)
            Nothing -> return (WriteErr c)
      else do
        r <- File.extend inum piece_bs
        case r of
          Just _ -> return (WriteOK (c + (fromIntegral cnt)))
          Nothing -> return (WriteErr c)
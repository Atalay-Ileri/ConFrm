{-# LANGUAGE RankNTypes, MagicHash, PackageImports, BangPatterns #-}
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
import Interpreter
import Data.Serialize
import Directory
import qualified Data.Text
import Data.Text.Encoding (encodeUtf8, decodeUtf8)
import qualified Helpers
import qualified Data.ByteString.Char8 as BSC8
import System.Posix.IO

-- Handle type for open files; we will use the inode number
type HT = BaseTypes.Coq_addr

blocksize :: Int
blocksize = block_size `div` 8

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
  putStrLn $ "Starting file system."
  fuseRun "confs" fuse_args (confsFSOps disk_fn getFuseContext) defaultExceptionHandler

fileStat :: FuseContext -> FileStat
fileStat ctx = FileStat { statEntryType = RegularFile
, statFileMode = foldr1 unionFileModes
                    [ ownerReadMode, ownerWriteMode, ownerExecuteMode
                    , groupReadMode, groupWriteMode, groupExecuteMode
                    , otherReadMode, otherWriteMode, otherExecuteMode
                    ]
, statLinkCount = 1
, statFileOwner = fuseCtxUserID ctx
, statFileGroup = fuseCtxGroupID ctx
, statSpecialDeviceID = 0
, statFileSize = 0
, statBlocks = 1
, statAccessTime = 0
, statModificationTime = 0
, statStatusChangeTime = 0
}

dirStat :: FuseContext -> FileStat
dirStat ctx = FileStat { statEntryType = Directory
  , statFileMode = foldr1 unionFileModes
                      [ ownerReadMode, ownerWriteMode, ownerExecuteMode
                      , groupReadMode, groupExecuteMode
                      , otherReadMode, otherExecuteMode
                      ]
  , statLinkCount = 2
  , statFileOwner = fuseCtxUserID ctx
  , statFileGroup = fuseCtxGroupID ctx
  , statSpecialDeviceID = 0
  , statFileSize = 4096
  , statBlocks = 1
  , statAccessTime = 0
  , statModificationTime = 0
  , statStatusChangeTime = 0
  }

-- See the HFuse API docs at:
-- https://hackage.haskell.org/package/HFuse-0.2.1/docs/System-Fuse.html
confsFSOps :: String -> IO FuseContext -> FuseOperations HT
confsFSOps disk_fn getctx  = defaultFuseOps
  { fuseGetFileStat = confsGetFileStat getctx
  , fuseReadSymbolicLink = \ path -> do
    -- print "--confsReadSymbolicLink--"
    -- print path
    return (Left eIO)
  , fuseCreateDevice = confsCreateDevice
  , fuseCreateDirectory = confsCreateDirectory
  , fuseRemoveLink = confsUnlink
  , fuseRemoveDirectory = confsRemoveDirectory
  , fuseCreateSymbolicLink = \ _ _ -> return eOK
  , fuseRename = confsRename
  , fuseCreateLink = \ _ _ -> return eOK
  , fuseSetFileMode = \ _ _ -> return eOK
  , fuseSetOwnerAndGroup = confsChown
  , fuseSetFileSize = \ _ _ -> return eOK
  , fuseSetFileTimes = \ _ _ _ -> return eOK
  , fuseOpen = confsOpen
  , fuseRead = confsRead
  , fuseWrite = confsWrite
  , fuseGetFileSystemStats = confsGetFileSystemStats
  , fuseFlush = \ _ _ -> return eOK
  , fuseRelease = \ _ _ -> return ()
  , fuseSynchronizeFile = \ _ _ -> return eOK
  , fuseOpenDirectory = confsOpenDirectory
  , fuseReadDirectory = confsReadDirectory getctx
  , fuseReleaseDirectory = \ _ -> return eOK
  , fuseSynchronizeDirectory = \ _ _ -> return eOK
  , fuseAccess = \ _ _ -> return eOK
  , fuseInit = confsInit disk_fn
  , fuseDestroy = confsDestroy
  }

confsDestroy :: IO ()
confsDestroy = do
  stats <- Interpreter.diskClose
  print "--- Disk Close Stats ---"
  Interpreter.printStats stats
  print "--- --- ---  --- --- ---"

confsReadDirectory :: IO FuseContext -> FilePath -> IO (Either Errno [(FilePath, FileStat)])  
confsReadDirectory getctx path = do
  let path_list = (splitDirectories path)
  r <- onDirMap (isValidDirPath path_list)
  r <- if r then do
    msd <- onDirMap (getSubdirs (last path_list))
    case msd of
      Just sd -> do
        ctx <- getctx
        return (Right (map (\s -> (s, dirStat ctx)) sd))
      Nothing -> return (Left eIO)
  else
    return (Left eIO)
  return r

confsGetFileStat :: IO FuseContext -> FilePath -> IO (Either Errno FileStat)
confsGetFileStat getctx path 
    | (last (splitDirectories path) == "stats") || 
      (last (splitDirectories path) == "sync") ||
      (last (splitDirectories path) == "clear-stats") = do
        ctx <- getctx
        return (Right (fileStat ctx))
    | otherwise = do
    let path_list = (splitDirectories path)
    r <- onDirMap (isValidDirPath path_list)
    r <- if r then do
      ctx <- getctx
      return (Right (dirStat ctx))
    else do
      r <- onDirMap (isValidFilePath path_list)
      if r then do
        ctx <- getctx
        return (Right (fileStat ctx))
      else do
        return (Left eNOENT)
    return r

confsRename :: FilePath -> FilePath -> IO Errno
confsRename src dst = do
  let src_path_list = (splitDirectories src)
  let dst_path_list = (splitDirectories dst)
  r <- onDirMap (isValidPath src_path_list)
  r <- if r then do
    r <- onDirMap (isValidDirPath (take (length dst_path_list - 1) dst_path_list))
    if r then do
      rinum <- onDirMap (getInumPath dst_path_list)
      r <- modifyDirMap (Directory.rename src_path_list dst_path_list)
      persistDirMap
      --Interpreter.diskSync
      case r of
        eOK -> 
          case rinum of
            Just i -> do 
              --Interpreter.diskSync
              File.delete i
            Nothing -> return Nothing
        _ -> return Nothing
      return r
    else 
      return eIO
  else
    return eIO
  
  return r

confsRemoveDirectory :: FilePath -> IO Errno
confsRemoveDirectory path = do
  let path_list = (splitDirectories path)
  r <- modifyDirMap (removeDir path_list)
  return r

confsGetFileSystemStats :: String -> IO (Either Errno FileSystemStats)
confsGetFileSystemStats path = do
  return $ Right $ FileSystemStats
    { fsStatBlockSize = 4096
    , fsStatBlockCount = 2 * 8 * 4096
    , fsStatBlocksFree = 2 * 8 * 4096
    , fsStatBlocksAvailable = 2 * 8 * 4096
    , fsStatFileCount = 8 * 4096
    , fsStatFilesFree = 2 * 8 * 4096
    , fsStatMaxNameLength = 128
    }

confsInit:: String -> IO ()
confsInit disk_fn = do
  _ <- writeIORef Interpreter.txnList []
  _ <- writeIORef Interpreter.cache Data.Map.empty
  _ <- writeIORef Interpreter.cipherMap Data.Map.empty
  _ <- writeIORef Interpreter.bufferCache Data.Map.empty
  fileExists <- System.Directory.doesFileExist disk_fn
  fs <- openFd disk_fn ReadWrite (Just 0o666) defaultFileFlags
  writeIORef Interpreter.fsImage fs
  if fileExists then do
    putStrLn $ "Recovering file system"
    File.recover
    recoverDirMap
  else do
    putStrLn $ "Initializing file system"
    File.init
    initializeDirMap
  putStrLn $ "Initializing Done"

confsCreateDevice :: FilePath -> EntryType -> FileMode -> DeviceID -> IO Errno
confsCreateDevice path entryType _ _ = do
  r <- case entryType of
    RegularFile -> do
      let path_list = (splitDirectories path)
      r <- onDirMap (isValidDirPath (take (length path_list - 1) path_list))
      if r then do
        r <- onDirMap (Data.Map.notMember (last path_list))
        if r then do 
            uid <- getEffectiveUserID
            minum <- File.create uid
            case minum of  
              Just inum -> do
                --Interpreter.diskSync
                modifyDirMap (addFile path_list inum)
              Nothing -> return eNOSPC
        else do
          return eEXIST
      else do
        return eNOTDIR
    _ -> return eIO
  return r

confsCreateDirectory :: FilePath -> FileMode -> IO Errno
confsCreateDirectory path _ = do
  let path_list = (splitDirectories path)
  modifyDirMap (addDir path_list)

confsOpenDirectory :: FilePath -> IO Errno
confsOpenDirectory path 
  | (last (splitDirectories path) == "stats") || 
    (last (splitDirectories path) == "sync") ||
    (last (splitDirectories path) == "clear-stats") = return eOK
  | otherwise = do
    let path_list = (splitDirectories path)
    r <- onDirMap (isValidDirPath path_list)
    r <- if r then
      return eOK
    else
      return eIO
    return r
  
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

-- modes etc.
confsOpen :: FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
confsOpen path _ _ 
  | (last (splitDirectories path) == "stats") || 
    (last (splitDirectories path) == "sync") = return $ Right 0
  | (last (splitDirectories path) == "clear-stats") = do
    Interpreter.clearStats
    return $ Right 0
  | otherwise = do
    let path_list = (splitDirectories path)
    r <- onDirMap (isValidFilePath path_list)
    r <- if r then do
      minum <- onDirMap (getInum (last path_list))
      case minum of
        Just inum -> do
          return (Right inum)
        Nothing -> do
          return (Left eIO)
    else do
      return (Left eIO)
    return r

confsUnlink :: FilePath -> IO Errno
confsUnlink path = do
  let path_list = (splitDirectories path)
  r <- onDirMap (isValidFilePath path_list)
  r <- if r then do
    minum <- onDirMap (getInum (last path_list))
    case minum of
      Just inum -> do 
        r <- File.delete inum
        case r of
          Just _ -> do 
            --Interpreter.diskSync
            modifyDirMap (removeFile path_list)
          Nothing -> return eIO
      Nothing -> 
        return eIO
  else do 
    mdir <- onDirMap (isValidDirPath path_list)
    if mdir then do
      modifyDirMap (removeDir path_list)
    else
      return eIO
  return r

confsChown :: FilePath -> UserID -> GroupID -> IO Errno
confsChown path uid _  = do
  r <- onDirMap (isValidFilePath (splitDirectories path))
  if r then do
    minum <- onDirMap (getInum (takeFileName path))
    case minum of
      Just inum -> do 
        r <- File.change_owner inum (fromIntegral (toInteger uid))
        case r of
          Just _ -> do 
            --Interpreter.diskSync
            return eOK
          Nothing -> return eIO
      Nothing -> return eIO
  else
    return eIO

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
confsRead path inum byteCount offset 
  | last (splitDirectories path) == "stats" = do
    Interpreter.Stats r w s <- Interpreter.getStats
    Interpreter.clearStats
    let bs = BSC8.pack ("Reads:  " ++ (show r) ++ " Writes: " ++ (show w) ++ " Syncs:  " ++ (show s))
    print bs
    return $ (Right bs)

  | otherwise = do
    pieces <- mapM read_piece $ compute_ranges offset byteCount
    return $ Right $ BS.concat pieces
    where
      read_piece (BR blk off count) = do
        ok_buf <- File.read inum blk
        case ok_buf of
          Just buf -> do
            --Interpreter.diskSync
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
confsWrite path inum !bs offset = do
  mlen <- File.get_file_size inum
  case mlen of
    Just len -> do
      r <- foldM (write_piece inum len) (WriteOK 0) (compute_range_pieces offset bs)
      case r of
        WriteOK c -> do
          --Interpreter.diskSync
          return (Right c)
        WriteErr c -> do
          --Interpreter.diskSync
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
        r <- File.extend inum (BS.append piece_bs (BS.replicate (blocksize - BS.length piece_bs) 0))
        case r of
          Just _ -> return (WriteOK (c + (fromIntegral cnt)))
          Nothing -> return (WriteErr c)
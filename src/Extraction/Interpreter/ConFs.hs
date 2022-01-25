{-# LANGUAGE RankNTypes, MagicHash #-}

module Main where

import qualified Data.ByteString as BS
import qualified System.Directory
import Foreign.C.Error
import System.Posix.Types
import System.Posix.Files
import System.Posix.IO
import System.FilePath.Posix
import Fuse
import qualified DirName
import System.Environment
import Control.Concurrent.MVar
import Text.Printf
import qualified System.Process
import qualified Data.List
import Control.Monad
import GHC.IO.Unsafe
import System.Posix.User
import qualified BaseTypes
import qualified File


-- Handle type for open files; we will use the inode number
type HT = Coq_addr

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

run_fuse :: String -> [String] -> IO()
run_fuse disk_fn fuse_args = do
  fileExists <- System.Directory.doesFileExist disk_fn
  {- ds <- case disk_fn of
    "/tmp/crashlog.img" -> init_disk_crashlog disk_fn
    _ -> init_disk disk_fn
  -}
  s <- if fileExists
  then
    do
      putStrLn $ "Recovering file system"
      res <- File.recover
      case res of
        Nothing -> error $ "recovery failed; not an confs fs?"
        Just _ -> return (Just ())
  else
    do
      putStrLn $ "Initializing file system"
      res <- File.init
      case res of
        Nothing -> error $ "mkfs failed"
        Just _ -> return (Just ())
  case s of
    Nothing -> return ()
    Just _ -> do
      putStrLn $ "Starting file system."
      fuseRun "confs" fuse_args (confsFSOps getFuseContext) defaultExceptionHandler useDowncalls

-- See the HFuse API docs at:
-- https://hackage.haskell.org/package/HFuse-0.2.1/docs/System-Fuse.html
confsFSOps :: IO FuseContext -> FuseOperations HT
confsFSOps getctx  = defaultFuseOps
  { fuseOpen = confsOpen
  , fuseRead = confsRead
  , fuseWrite = confsWrite
  , fuseUnlink = confsUnlink
  , fuseSetOwnerAndGroup = confsChown
  }

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
confsOpen :: OpenMode -> OpenFileFlags -> IO (Either Errno HT)
confsOpen _ _ =
  r <- File.create uid
  case r of
    Nothing -> return $ Left $ eIO
    Just inum -> return $ Right inum

-- use path as string representation of handle
confsUnlink :: FilePath -> IO Errno
confsUnlink path = do
  mInt <- readMaybe path :: Int
  case mInt of
    Just i ->
      r <- File.delete i
      case r of
        Just _ -> return eOK
        Nothing -> return eIO
    Nothing -> return eIO

-- use file path as string rep of handle.
confsChown :: FilePath -> UserID -> GroupID -> IO Errno
confsChown path uid _  = do
  mInt <- readMaybe path :: Int
  case mInt of
    Just i ->
      r <- File.change_owner i (fromIntegral (toInteger uid))
      case r of
        Just _ -> return eOK
        Nothing -> return eIO
    Nothing -> return eIO

blocksize :: Integer
blocksize = BaseTypes.block_size `div` 8

data BlockRange =
  BR !Integer !Integer !Integer   -- blocknumber, offset-in-block, count-from-offset

compute_ranges_int :: Integer -> Integer -> [BlockRange]
compute_ranges_int off count = map mkrange $ zip3 blocknums startoffs endoffs
  where
    mkrange (blk, startoff, endoff) = BR blk startoff (endoff-startoff)
    blocknums = [off `div` blocksize .. (off + count - 1) `div` blocksize]
    startoffs = [off `mod` blocksize] ++ replicate (length blocknums - 1) 0
    endoffs = replicate (length blocknums - 1) blocksize ++ [(off + count - 1) `mod` blocksize + 1]

compute_ranges :: FileOffset -> ByteCount -> [BlockRange]
compute_ranges off count =
  compute_ranges_int (fromIntegral off) (fromIntegral count)

confsRead :: HT -> ByteCount -> FileOffset -> IO (Either Errno BS.ByteString)
confsRead inum byteCount offset = do
  (wlen, ()) <- fr $ AsyncFS._AFS__file_get_sz fsxp inum
  len <- return $ fromIntegral $ wordToNat 64 wlen
  offset' <- return $ min offset len
  byteCount' <- return $ min byteCount $ (fromIntegral len) - (fromIntegral offset')
  pieces <- mapM read_piece $ compute_ranges offset' byteCount'
  return $ Right $ BS.concat pieces

  where
    read_piece (BR blk off count) = do
      ok_buf <- fr $ File.read inum blk
      case ok_buf of
        Just buf ->
          return $ BS.take (fromIntegral count) $ BS.drop (fromIntegral off) $ buf
        Nothing ->
          error "Read ERROR"

compute_range_pieces :: FileOffset -> BS.ByteString -> [(BlockRange, BS.ByteString)]
compute_range_pieces off buf = zip ranges pieces
  where
    ranges = compute_ranges_int (fromIntegral off) $ fromIntegral $ BS.length buf
    pieces = map getpiece ranges
    getpiece (BR blk boff bcount) = BS.take (fromIntegral bcount) $ BS.drop (fromIntegral bufoff) buf
      where bufoff = (blk * blocksize) + boff - (fromIntegral off)

data WriteState =
   WriteOK !ByteCount
 | WriteErr !ByteCount

-- This should automatically extend if it passes file length
confsWrite :: HT -> BS.ByteString -> FileOffset -> IO (Either Errno ByteCount)
confsWrite inum bs offset = do
  (wlen, ()) <- fr $ AsyncFS._AFS__file_get_sz fsxp inum
  len <- return $ fromIntegral $ wordToNat 64 wlen
  endpos <- return $ (fromIntegral offset) + (fromIntegral (BS.length bs))
  (okspc, do_log) <- if len < endpos then do
    (ok, _) <- fr $ AsyncFS._AFS__file_truncate fsxp inum ((endpos + 4095) `div` 4096)
    return (ok, True)
  else do
    bslen <- return $ fromIntegral $ BS.length bs
    if ((fromIntegral offset) `mod` 4096 == 0) && (bslen `mod` 4096 == 0) && bslen > 4096 * 5 then
      -- block is large and aligned -> bypass write
      return $ (Errno.OK (), False)
    else
      return $ (Errno.OK (), True)
  case okspc of
    Errno.OK _ -> do
      r <- foldM (write_piece do_log fsxp len) (WriteOK 0) (compute_range_pieces offset bs)
      case r of
        WriteOK c -> do
          okspc2 <- if len < endpos then do
            (ok, _) <- fr $ AsyncFS._AFS__file_set_sz fsxp inum (W endpos)
            return ok
          else
            return $ (Errno.OK ())
          case okspc2 of
            Errno.OK _ -> return $ Right c
            Errno.Err _ -> return $ Left eNOSPC
        WriteErr c ->
          if c == 0 then
            return $ Left eIO
          else
            return $ Right c
    Errno.Err e -> do
      return $ Left $ errnoToPosix e
  where
    write_piece _ _ _ (WriteErr c) _ = return $ WriteErr c
    write_piece do_log fsxp init_len (WriteOK c) (BR blk off cnt, piece_bs) = do
      new_bs <- if cnt == blocksize then
          -- Whole block writes don't need read-modify-write
          return piece_bs
        else do
          old_bs <- if (init_len <= blk*blocksize) || (off == 0 && init_len <= blk*blocksize + cnt) then
              -- If we are doing a partial block write, we don't need RMW in two cases:
              -- (1.) The file was smaller than the start of this block.
              -- (2.) The partial write of this block starts immediately at offset 0
              --      in this block, and writes all the way up to (and maybe past)
              --      the original end of the file.
              return $ BS.replicate (fromIntegral blocksize) 0
            else do
              (ok_block, ()) <- fr $ AsyncFS._AFS__read_fblock fsxp inum blk
              case ok_block of
                Errno.OK block ->
                  case block of
                    W w -> i2bs w 4096
                    WBS bs' -> return bs'
                Errno.Err _ ->
                  error "PERMISSION ERROR"
          return $ BS.append (BS.take (fromIntegral off) old_bs)
                 $ BS.append piece_bs
                 $ BS.drop (fromIntegral $ off + cnt) old_bs
      okb <- if do_log then do
        (okb, ()) <- fr $ AsyncFS._AFS__update_fblock fsxp inum blk (WBS new_bs)
        return okb
      else do
        (okb, ()) <- fr $ AsyncFS._AFS__update_fblock_d fsxp inum blk (WBS new_bs)
        return okb
      case okb of
        Errno.Err _ -> return $ WriteErr c
        Errno.OK _ -> return $ WriteOK (c + (fromIntegral cnt))


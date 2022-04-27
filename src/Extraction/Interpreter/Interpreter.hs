{-# LANGUAGE PackageImports, BangPatterns #-}
module Interpreter where

import Prelude
import BaseTypes
import Helpers
import Crypto.Hash
import Crypto.Hash.Algorithms
import Data.IORef
import "cipher-aes" Crypto.Cipher.AES
import Data.Map
import System.Random
import System.Random.Stateful
import System.IO
import System.IO.Unsafe
import qualified Data.ByteString as BS
import Data.ByteString.Random
import qualified Data.ByteArray

import System.IO
import System.Posix.Types
import System.Posix.Unistd
import System.Posix.Files
import System.Posix.IO
import qualified "unix-bytestring" System.Posix.IO.ByteString as PBS
import qualified Data.ByteString.Internal as BSI
import GHC.Exts
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc
import System.Clock
import Text.Printf


addrsPerBlock :: Int
addrsPerBlock = div block_size intSize 

cache :: IORef (Map Coq_addr Coq_value)
{-# NOINLINE cache #-}
cache = unsafePerformIO (newIORef empty)

bufferCache :: IORef (Map Coq_addr Coq_value)
{-# NOINLINE bufferCache #-}
bufferCache = unsafePerformIO (newIORef empty)

txnList :: IORef [(Coq_addr, Coq_value)]
{-# NOINLINE txnList #-}
txnList = unsafePerformIO (newIORef [])

dirty :: IORef Bool
{-# NOINLINE dirty #-}
dirty = unsafePerformIO (newIORef False)

-- Haskell doesn't allow us to access the key explicitly. 
-- You get to initialize by giving a seed. 
-- What I will do is keep 32-bit random seeds as "keys" in the header
-- then initialize the cipherMap as it accesses. 
cipherMap :: IORef (Map Coq_key AES)
{-# NOINLINE cipherMap #-}
cipherMap = unsafePerformIO (newIORef empty)

getCipher :: Coq_key -> IO AES
getCipher k = do
  cm <- readIORef cipherMap
  case (Data.Map.lookup k cm) of
    Just c -> return c
    Nothing -> 
      do
      let newCipher = initAES k
      _ <- writeIORef cipherMap (insert k newCipher cm)
      return newCipher


fsImage :: IORef (Fd)
{-# NOINLINE fsImage #-}
fsImage = unsafePerformIO (newIORef (Fd 0))

-- DiskStats counts the number of reads, writes, and syncs
data DiskStats = Stats !Int !Int !Int

stats :: IORef (DiskStats)
{-# NOINLINE stats #-}
stats = unsafePerformIO (newIORef (Stats 0 0 0))

bumpRead :: IO ()
bumpRead = do
  Stats r w s <- readIORef stats
  writeIORef stats (Stats (r+1) w s)

bumpWrite :: IO ()
bumpWrite = do
  Stats r w s <- readIORef stats
  writeIORef stats (Stats r (w+1) s)

bumpSync :: IO ()
bumpSync = do
  Stats r w s <- readIORef stats
  writeIORef stats (Stats r w (s+1))

getStatsString :: DiskStats -> String
getStatsString (Stats r w s) =
  "Disk I/O stats:" ++ 
  "\nReads:  " ++ (show r) ++
  "\nWrites: " ++ (show w) ++
  "\nSyncs:  " ++ (show s)

printStats :: DiskStats -> IO ()
printStats (Stats r w s) = do
  putStrLn $ "Disk I/O stats:"
  putStrLn $ "Reads:  " ++ (show r)
  putStrLn $ "Writes: " ++ (show w)
  putStrLn $ "Syncs:  " ++ (show s)

clearStats :: IO ()
clearStats = writeIORef stats (Stats 0 0 0)

getStats :: IO DiskStats
getStats = readIORef stats

opTimes :: Bool
opTimes = False

perSyscallStats :: Bool
perSyscallStats = False

syscallTimes :: Bool
syscallTimes = False

fsTimes :: Bool
fsTimes = False

internalTimes :: Bool
internalTimes = False

getSyscallOpStats :: String -> IO a -> IO a
getSyscallOpStats name f =
  if perSyscallStats then do
    clearStats
    ret <- f
    Stats r w s <- getStats
    clearStats
    printf "--%s Disk Operation Counts--\nReads: %s\nWrites: %s\nSyncs: %s\n-----" name (show r) (show w) (show s)
    return ret
  else
    f

timeItNamed b s m = 
  if b then do
    start <- getTime Realtime
    r <- m
    end <- getTime Realtime
    printf "%s: %d\n" s (nsec end - nsec start)
    return r
  else 
    m

-- Disk Operations
diskRead' :: Coq_addr -> IO Coq_value
diskRead' a = timeItNamed opTimes "Disk Read"--return BaseTypes.value0
  (do
  bumpRead
  fs <-  readIORef fsImage
  PBS.fdSeek fs AbsoluteSeek (fromIntegral(4096 Prelude.* a))
  PBS.fdRead fs 4096)

diskRead :: Coq_addr -> IO Coq_value
diskRead a = diskRead' a
{-
  do 
  c <- readIORef bufferCache
  case Data.Map.lookup a c of
    Just v -> 
      return v
    Nothing -> do
      v <- diskRead' a
      modifyIORef' bufferCache (insert a v)
      return v
-}

diskWrite' :: Coq_addr -> Coq_value -> IO ()
diskWrite' a v = timeItNamed opTimes "Disk Write" --return ()
  (do
  bumpWrite
  writeIORef dirty True
  fs <-  readIORef fsImage
  PBS.fdSeek fs AbsoluteSeek (fromIntegral(4096 Prelude.* a))
  _ <- PBS.fdWrite fs v
  return ())

diskWrite :: Coq_addr -> Coq_value -> IO ()
diskWrite a !v = do
  --modifyIORef' bufferCache (insert a v)
  diskWrite' a v

diskSync :: IO ()
diskSync = timeItNamed opTimes "Disk Sync"
  (do  --return ()
  d <- readIORef dirty
  if d then do
    bumpSync
    fs <-  readIORef fsImage
    fileSynchronise fs
    writeIORef dirty False
  else
    return ())

diskClose :: IO DiskStats
diskClose = do 
  fs <- readIORef fsImage
  closeFd fs
  readIORef stats

-- Cache Operations
cacheRead :: Coq_addr -> IO (Maybe Coq_value)
cacheRead a = timeItNamed opTimes "Cache Read"
  (do 
  c <- readIORef cache
  return (Data.Map.lookup a c))

cacheWrite :: Coq_addr -> Coq_value -> IO ()
cacheWrite a v = timeItNamed opTimes "Cache Write" (modifyIORef' cache (insert a v))

cacheFlush :: IO ()
cacheFlush = timeItNamed opTimes "Cache Flush" (writeIORef cache empty)

-- List Operations
listGet :: IO [(Coq_addr , Coq_value)]
listGet = timeItNamed opTimes "List Get" (readIORef txnList)

listPut :: (Coq_addr , Coq_value) -> IO ()
listPut av = timeItNamed opTimes "List Put" (modifyIORef' txnList ((:) av))

listDelete :: IO ()
listDelete = timeItNamed opTimes "List Delete" (writeIORef txnList [])

-- Crypto Operations
cryptoHash :: Coq_hash -> Coq_value -> IO Coq_hash
cryptoHash h v = timeItNamed opTimes "Crypto Hash"
  (return (toByteString (hash (BS.append h v) :: Digest MD5)))

cryptoGetKey :: IO Coq_key
cryptoGetKey = timeItNamed opTimes "Crypto GetKey"
  (uniformByteStringM 32 globalStdGen)

cryptoEncrypt :: Coq_key -> Coq_value -> IO Coq_value
cryptoEncrypt k v = timeItNamed opTimes "Crypto Encrypt"
  (do 
  cipher <- getCipher k;
  return (encryptECB cipher v))

cryptoDecrypt :: Coq_key -> Coq_value -> IO Coq_value
cryptoDecrypt k v = timeItNamed opTimes "Crypto Decrypt"
  (do 
  cipher <- getCipher k;
  return (decryptECB cipher v))
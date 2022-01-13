{-# LANGUAGE PackageImports #-}
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



addrsPerBlock :: Int
addrsPerBlock = div block_size intSize 

cache :: IORef (Map Coq_addr Coq_value)
{-# NOINLINE cache #-}
cache = unsafePerformIO (newIORef empty)

txnList :: IORef [(Coq_addr, Coq_value)]
{-# NOINLINE txnList #-}
txnList = unsafePerformIO (newIORef [])

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


fsImage :: Handle
{-# NOINLINE fsImage #-}
fsImage = unsafePerformIO (openBinaryFile "fs_image" ReadWriteMode)

-- Disk Operations
diskRead :: Coq_addr -> IO Coq_value
diskRead a = --return BaseTypes.value0
  do 
  hSeek fsImage AbsoluteSeek (fromIntegral(4096 Prelude.* a))
  BS.hGet fsImage 4096

diskWrite :: Coq_addr -> Coq_value -> IO ()
diskWrite a v = --return ()
  do
  hSeek fsImage AbsoluteSeek (fromIntegral(4096 Prelude.* a))
  BS.hPut fsImage v

diskSync :: IO ()
diskSync = --return ()
  hFlush fsImage

-- Cache Operations
cacheRead :: Coq_addr -> IO (Maybe Coq_value)
cacheRead a = do 
  c <- readIORef cache
  return (Data.Map.lookup a c)

cacheWrite :: Coq_addr -> Coq_value -> IO ()
cacheWrite a v = modifyIORef' cache (insert a v)

cacheFlush :: IO ()
cacheFlush = writeIORef cache empty

-- List Operations
listGet :: IO [(Coq_addr , Coq_value)]
listGet = readIORef txnList

listPut :: (Coq_addr , Coq_value) -> IO ()
listPut av = modifyIORef' txnList ((:) av)

listDelete :: IO ()
listDelete = writeIORef txnList []

-- Crypto Operations
cryptoHash :: Coq_hash -> Coq_value -> IO Coq_hash
cryptoHash h v = return (toByteString (hash (BS.append h v) :: Digest MD5))

cryptoGetKey :: IO Coq_key
cryptoGetKey = uniformByteStringM 32 globalStdGen

cryptoEncrypt :: Coq_key -> Coq_value -> IO Coq_value
cryptoEncrypt k v = do 
  cipher <- getCipher k;
  return (encryptECB cipher v)

cryptoDecrypt :: Coq_key -> Coq_value -> IO Coq_value
cryptoDecrypt k v = do 
    cipher <- getCipher k;
    return (decryptECB cipher v)
module Helpers where

import Prelude
import qualified Data.Bits
import qualified Data.Word
import qualified Data.Char
import qualified Data.ByteArray as BA
import qualified Data.ByteString as BS
import qualified Data.Serialize as BIN
import qualified Data.List.Split as L
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8, decodeUtf8)

intSize :: Int
intSize = Data.Bits.finiteBitSize (1::Int)

toBits :: Data.Word.Word8 -> [Bool]
toBits x = [Data.Bits.testBit x i | i <- [0.. Data.Bits.finiteBitSize x - 1] ]
--toBits x = replicate (Data.Bits.finiteBitSize x) False

toByte :: [Bool] -> Data.Word.Word8
toByte list = toByteRec list 0 0

toByteRec :: [Bool] -> Int -> Data.Word.Word8 -> Data.Word.Word8
toByteRec list 8 result = result
toByteRec list i result 
    | head list == True = toByteRec (tail list) (i + 1) (result Data.Bits..|. (2^i :: Data.Word.Word8))
    | otherwise = toByteRec (tail list) (i + 1) result

byteStringToBoolList :: BS.ByteString -> [Bool]
byteStringToBoolList bs =
  concatMap toBits (BS.unpack bs)

boolListToByteString :: [Bool] -> BS.ByteString 
boolListToByteString  bl =
  BS.pack (map toByte (L.chunksOf 8 bl))


toByteString :: BA.ByteArrayAccess a => a -> BS.ByteString
toByteString = BS.pack . BA.unpack

setToBlockSize:: Int -> BS.ByteString -> BS.ByteString
setToBlockSize bytesPerBlock bs 
  | (BS.length bs) < bytesPerBlock = BS.append bs (BS.replicate (bytesPerBlock - BS.length bs) 0)
  | otherwise = BS.take bytesPerBlock bs

stringToBlock :: Int -> String -> BS.ByteString
stringToBlock len str = (setToBlockSize len . encodeUtf8 . T.pack) str

blockToString :: BS.ByteString -> String
blockToString bs = (T.unpack . (T.takeWhile Data.Char.isPrint) . decodeUtf8) bs

--written by Baricus

padList :: Int -> [Int] -> [Int]
padList intsPerBlock l | length l `mod` intsPerBlock == 0 = l
          | otherwise = let addend = intsPerBlock - length l `mod` intsPerBlock in l ++ replicate addend 0

intListToByteStringList :: Int -> [Int] -> [BS.ByteString]
intListToByteStringList intsPerBlock list = map (BS.drop 8 . BIN.encode) $ (L.chunksOf intsPerBlock . padList intsPerBlock) list

decodeChunk :: BS.ByteString -> [Int]
decodeChunk bytes | BS.null bytes = []
                  | otherwise = let (n, rest) = BS.splitAt (fromIntegral $ Data.Bits.finiteBitSize (1 :: Int) `div` 8) bytes
                        in (case BIN.decode n of
                          Left _ -> 0
                          Right i -> i) : decodeChunk rest

byteStringListToIntList :: [BS.ByteString] -> [Int]
byteStringListToIntList = concatMap (decodeChunk)
module Helpers where

import Prelude
import qualified Data.Bits as B
import qualified Data.Word as W
import qualified Data.Char
import qualified Data.ByteArray as BA
import qualified Data.ByteString as BS
import qualified Data.Persist as BIN
import qualified Data.List.Split as L
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8, decodeUtf8)

intSize :: Int
intSize = B.finiteBitSize (1::Int)

maxWord8 :: W.Word8
maxWord8 = B.complement B.zeroBits

changeBitWord8 :: Int -> Bool -> W.Word8 -> W.Word8
changeBitWord8 a b w = 
  if b then
    B.setBit w a
  else
    B.clearBit w a

changeBit :: Int -> Bool -> BS.ByteString -> BS.ByteString
changeBit a b bs =
  let bs_index = div a 8 in
  let word_index = mod a 8 in
    if bs_index < BS.length bs then
      BS.append (BS.take bs_index bs) (BS.cons (changeBitWord8 word_index b (BS.index bs bs_index)) (BS.drop (bs_index + 1) bs)) 
    else 
      bs

setBit :: Int -> BS.ByteString -> BS.ByteString
setBit a bs = changeBit a True bs

unsetBit :: Int -> BS.ByteString -> BS.ByteString
unsetBit a bs = changeBit a False bs

testBit :: Int -> BS.ByteString -> Bool
testBit a bs =
  let bs_index = div a 8 in
  let word_index = mod a 8 in
    if bs_index < BS.length bs then
      B.testBit (BS.index bs bs_index) word_index
    else 
      False

getFirstZeroIndexWord8Rec :: Int -> W.Word8 -> Int
getFirstZeroIndexWord8Rec 8 w = 8
getFirstZeroIndexWord8Rec n w =
  if B.testBit w n then
    getFirstZeroIndexWord8Rec (n + 1) w
  else
    n

getFirstZeroIndexWord8 :: W.Word8 -> Int
getFirstZeroIndexWord8 w = getFirstZeroIndexWord8Rec 0 w

getFirstZeroIndex :: BS.ByteString -> Int
getFirstZeroIndex bs =
  let mIndex = BS.findIndex (\w -> w /= maxWord8) bs in
    case mIndex of
      Nothing -> BS.length bs * 8
      Just i -> 
        let wIndex = getFirstZeroIndexWord8 (BS.index bs i) in
          8 * i + wIndex


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
                  | otherwise = let (n, rest) = BS.splitAt intSize bytes
                        in (case BIN.decode n of
                          Left _ -> 0
                          Right i -> i) : decodeChunk rest

byteStringListToIntList :: [BS.ByteString] -> [Int]
byteStringListToIntList = concatMap (decodeChunk)
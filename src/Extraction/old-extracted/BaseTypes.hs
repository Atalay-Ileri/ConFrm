module BaseTypes where

import qualified Prelude
import qualified List

type EqDec t = t -> t -> Prelude.Bool

type Coq_addr = Int

type Coq_value = Data.ByteString.ByteString

value0 :: Coq_value
value0 = Data.ByteString.pack (Data.List.replicate (div block_size 8) (0::Data.Word.Word8))

block_size :: Prelude.Int
block_size = 8 * 4096

disk_size :: Coq_addr
disk_size = 4 * 1024 * 1024 * 1024 + 1

addr_list_to_blocks :: (([]) Coq_addr) -> ([])
                       Coq_value
addr_list_to_blocks = Helpers.intListToByteStringList (div block_size Helpers.intSize)

blocks_to_addr_list :: (([]) Coq_value) -> ([])
                       Coq_addr
blocks_to_addr_list = Helpers.byteStringListToIntList

get_first_zero_index :: (([]) Prelude.Bool) ->
                        Prelude.Int
get_first_zero_index l =
  case l of {
   ([]) -> 0;
   (:) hd tl ->
    case hd of {
     Prelude.True -> Prelude.succ
      (get_first_zero_index tl);
     Prelude.False -> 0}}

zero_bitlist :: ([]) Prelude.Bool
zero_bitlist =
  List.repeat Prelude.False block_size

value_to_bits :: Coq_value -> ([]) Prelude.Bool
value_to_bits = Helpers.byteStringToBoolList

bits_to_value :: (([]) Prelude.Bool) -> Coq_value
bits_to_value = Helpers.boolListToByteString

type Coq_hash = Data.ByteString.ByteString

hash_eq_dec :: EqDec Coq_hash
hash_eq_dec = (Prelude.==)

hash0 :: Coq_hash
hash0 = Helpers.toByteString (Crypto.Hash.hash value0 :: Crypto.Hash.Digest Crypto.Hash.Algorithms.MD5)

type Coq_key = Data.ByteString.ByteString

type Coq_user = System.Posix.Types.UserID

addr_dec :: EqDec Coq_addr
addr_dec =
  (Prelude.==)

hash_dec :: EqDec Coq_hash
hash_dec =
  hash_eq_dec


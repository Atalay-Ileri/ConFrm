{-# OPTIONS_GHC -cpp -XMagicHash #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE BangPatterns #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Log where

import qualified Prelude
import qualified BaseTypes
import qualified BatchOperations
import qualified Datatypes
import qualified FSParameters
import qualified List
import qualified PeanoNat
import Interpreter

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

data Coq_txn_record =
   Build_txn_record BaseTypes.Coq_key Prelude.Int Prelude.Int Prelude.Int

key :: Coq_txn_record -> BaseTypes.Coq_key
key t =
  case t of {
   Build_txn_record key0 _ _ _ -> key0}

start :: Coq_txn_record -> Prelude.Int
start t =
  case t of {
   Build_txn_record _ start0 _ _ -> start0}

addr_count :: Coq_txn_record -> Prelude.Int
addr_count t =
  case t of {
   Build_txn_record _ _ addr_count0 _ -> addr_count0}

data_count :: Coq_txn_record -> Prelude.Int
data_count t =
  case t of {
   Build_txn_record _ _ _ data_count0 -> data_count0}

data Coq_header_part =
   Build_header_part BaseTypes.Coq_hash Prelude.Int (([]) Coq_txn_record)

hash :: Coq_header_part -> BaseTypes.Coq_hash
hash h =
  case h of {
   Build_header_part hash1 _ _ -> hash1}

count :: Coq_header_part -> Prelude.Int
count h =
  case h of {
   Build_header_part _ count0 _ -> count0}

records :: Coq_header_part -> ([]) Coq_txn_record
records h =
  case h of {
   Build_header_part _ _ records0 -> records0}

header_part0 :: Coq_header_part
header_part0 =
  Build_header_part BaseTypes.hash0 0 ([])

data Coq_header =
   Build_header Coq_header_part Coq_header_part

old_part :: Coq_header -> Coq_header_part
old_part h =
  case h of {
   Build_header old_part0 _ -> old_part0}

current_part :: Coq_header -> Coq_header_part
current_part h =
  case h of {
   Build_header _ current_part0 -> current_part0}

header0 :: Coq_header
header0 =
  Build_header header_part0 header_part0

update_hdr :: Coq_header -> Coq_header_part -> Coq_header
update_hdr hdr hdr_part =
  Build_header (current_part hdr) hdr_part

encode_header :: Coq_header -> BaseTypes.Coq_value
encode_header = (Helpers.setToBlockSize (Prelude.div BaseTypes.block_size 8) Prelude.. Data.Serialize.encode)

decode_header :: BaseTypes.Coq_value -> Coq_header
decode_header = \x -> case Data.Serialize.decode x of {
Prelude.Left _ -> header0; 
Prelude.Right h -> h }

read_header :: Prelude.IO Coq_header
read_header =
  (Prelude.>>=)
    ( ( (unsafeCoerce (Interpreter.diskRead FSParameters.hdr_block_num))))
    (\hd -> Prelude.return (decode_header (unsafeCoerce hd)))

write_header :: Coq_header -> Prelude.IO ()
write_header hdr =
   (timeItNamed internalTimes "Internal DiskWriteHeader" GHC.Base.$
    (unsafeCoerce (Interpreter.diskWrite FSParameters.hdr_block_num
      (encode_header hdr))))

update_header :: Coq_header_part -> Prelude.IO ()
update_header hdr_part =
  (Prelude.>>=) (unsafeCoerce read_header) (\hdr ->
    timeItNamed internalTimes "Internal WriteHeader" GHC.Base.$ write_header (update_hdr (unsafeCoerce hdr) hdr_part))

check_hash :: (([]) BaseTypes.Coq_value) -> BaseTypes.Coq_hash -> Prelude.IO
              Prelude.Bool
check_hash log hash1 =
  (Prelude.>>=) (unsafeCoerce BatchOperations.hash_all BaseTypes.hash0 log)
    (\log_hash ->
    case BaseTypes.hash_dec (unsafeCoerce log_hash) hash1 of {
     Prelude.True -> Prelude.return Prelude.True;
     Prelude.False -> Prelude.return Prelude.False})

decrypt_txn :: Coq_txn_record -> (([]) BaseTypes.Coq_value) -> Prelude.IO
               ((,) (([]) BaseTypes.Coq_addr) (([]) BaseTypes.Coq_value))
decrypt_txn txn_record log_blocks =
  let {key0 = key txn_record} in
  let {start0 = start txn_record} in
  let {addr_count0 = addr_count txn_record} in
  let {data_count0 = data_count txn_record} in
  let {
   txn_blocks = List.firstn ((Prelude.+) addr_count0 data_count0)
                  (List.skipn start0 log_blocks)}
  in
  (Prelude.>>=) (unsafeCoerce BatchOperations.decrypt_all key0 txn_blocks)
  (\plain_blocks ->
  let {addr_blocks = List.firstn addr_count0 (unsafeCoerce plain_blocks)} in
  let {data_blocks = List.skipn addr_count0 (unsafeCoerce plain_blocks)} in
  let {
   addr_list = List.firstn data_count0
                 (BaseTypes.blocks_to_addr_list addr_blocks)}
  in
  Prelude.return ((,) addr_list data_blocks))

apply_txn :: Coq_txn_record -> (([]) BaseTypes.Coq_value) -> Prelude.IO ()
apply_txn txn_record log_blocks =
  (Prelude.>>=) (unsafeCoerce decrypt_txn txn_record log_blocks) (\al_db ->
    let {addr_list = Datatypes.fst (unsafeCoerce al_db)} in
    let {data_blocks = Datatypes.snd (unsafeCoerce al_db)} in
    BatchOperations.write_batch addr_list data_blocks)

apply_txns :: (([]) Coq_txn_record) -> (([]) BaseTypes.Coq_value) ->
              Prelude.IO ()
apply_txns txn_records log_blocks =
  case txn_records of {
   ([]) -> Prelude.return ();
   (:) txn_record txn_records' -> (Prelude.>>=)
    (unsafeCoerce apply_txn txn_record log_blocks) (\_ ->
    apply_txns txn_records' log_blocks)}

flush_txns :: (([]) Coq_txn_record) -> (([]) BaseTypes.Coq_value) ->
              Prelude.IO ()
flush_txns txn_records log_blocks =
  (Prelude.>>=) (unsafeCoerce apply_txns txn_records log_blocks) (\_ ->
    (Prelude.>>=) ( ( (unsafeCoerce Interpreter.diskSync))) (\_ ->
    (Prelude.>>=) (unsafeCoerce update_header header_part0) (\_ ->
     ( (unsafeCoerce Interpreter.diskSync)))))

read_encrypted_log :: Prelude.IO
                      ((,) Coq_header_part (([]) BaseTypes.Coq_value))
read_encrypted_log =
  (Prelude.>>=) (unsafeCoerce read_header) (\hdr ->
    let {current_part0 = current_part (unsafeCoerce hdr)} in
    let {old_part0 = old_part (unsafeCoerce hdr)} in
    (Prelude.>>=)
    (unsafeCoerce BatchOperations.read_consecutive FSParameters.log_start
      (count current_part0)) (\log -> (Prelude.>>=)
    (unsafeCoerce check_hash log (hash current_part0)) (\success ->
    case unsafeCoerce success of {
     Prelude.True -> Prelude.return ((,) current_part0 (unsafeCoerce log));
     Prelude.False -> (Prelude.>>=)
      (unsafeCoerce BatchOperations.read_consecutive FSParameters.log_start
        (count old_part0)) (\log0 -> Prelude.return ((,) old_part0
      (unsafeCoerce log0)))})))

apply_log :: Prelude.IO ()
apply_log =
  (Prelude.>>=) (unsafeCoerce read_encrypted_log) (\hdr_log ->
    let {hdr_part = Datatypes.fst (unsafeCoerce hdr_log)} in
    let {log = Datatypes.snd (unsafeCoerce hdr_log)} in
    let {txn_records = records hdr_part} in flush_txns txn_records log)

commit_txn :: (([]) BaseTypes.Coq_value) -> (([]) BaseTypes.Coq_value) ->
              Prelude.IO ()
commit_txn !addr_l !data_l =
  (Prelude.>>=) (unsafeCoerce read_header) (\hdr ->
    let {hash1 = hash (current_part (unsafeCoerce hdr))} in
    let {count0 = count (current_part (unsafeCoerce hdr))} in
    let {txn_records = records (current_part (unsafeCoerce hdr))} in
    (Prelude.>>=) ( ( (unsafeCoerce Interpreter.cryptoGetKey))) (\new_key ->
    (Prelude.>>=)
    (timeItNamed internalTimes "Internal EncryptAll" GHC.Base.$ unsafeCoerce BatchOperations.encrypt_all new_key
      (Datatypes.app addr_l data_l)) (\enc_data -> (Prelude.>>=)
    (timeItNamed internalTimes "Internal HashAll" GHC.Base.$ unsafeCoerce BatchOperations.hash_all hash1 enc_data) (\new_hash ->
    (Prelude.>>=)
    (timeItNamed internalTimes "Internal WriteConsecutive" GHC.Base.$ unsafeCoerce BatchOperations.write_consecutive
      ((Prelude.+) FSParameters.log_start count0) enc_data) (\_ ->
    let {
     new_count = (Prelude.+) count0
                   ((Prelude.+) (Datatypes.length addr_l)
                     (Datatypes.length data_l))}
    in
    let {
     new_txn = Build_txn_record (unsafeCoerce new_key) count0
      (Datatypes.length addr_l) (Datatypes.length data_l)}
    in
    let {
     new_hdr_part = Build_header_part (unsafeCoerce new_hash) new_count
      (Datatypes.app txn_records ((:) new_txn ([])))}
    in
    (Prelude.>>=) (timeItNamed internalTimes "Internal UpdateHeader" GHC.Base.$ unsafeCoerce update_header new_hdr_part) (\_ ->
     (timeItNamed internalTimes "Internal DiskSyncCommit" GHC.Base.$ (unsafeCoerce Interpreter.diskSync))))))))

commit :: (([]) BaseTypes.Coq_value) -> (([]) BaseTypes.Coq_value) ->
          Prelude.IO Prelude.Bool
commit addr_l data_l =
  (Prelude.>>=) (timeItNamed internalTimes "Internal LogReadHeader" GHC.Base.$ unsafeCoerce read_header) (\hdr ->
    let {cur_count = count (current_part (unsafeCoerce hdr))} in
    let {
     new_count = (Prelude.+) cur_count
                   ((Prelude.+) (Datatypes.length addr_l)
                     (Datatypes.length data_l))}
    in
    case PeanoNat._Nat__ltb FSParameters.log_length new_count of {
     Prelude.True -> Prelude.return Prelude.False;
     Prelude.False -> (Prelude.>>=) (timeItNamed internalTimes "Internal LogCommitTxn" GHC.Base.$ unsafeCoerce commit_txn addr_l data_l)
      (\_ -> Prelude.return Prelude.True)})

decrypt_txns :: (([]) Coq_txn_record) -> (([]) BaseTypes.Coq_value) ->
                Prelude.IO
                (([])
                ((,) (([]) BaseTypes.Coq_addr) (([]) BaseTypes.Coq_value)))
decrypt_txns txn_records log_blocks =
  case txn_records of {
   ([]) -> Prelude.return ([]);
   (:) record txn_records' -> (Prelude.>>=)
    (unsafeCoerce decrypt_txn record log_blocks) (\al_db -> (Prelude.>>=)
    (unsafeCoerce decrypt_txns txn_records' log_blocks) (\l_al_db ->
    Prelude.return ((:) (unsafeCoerce al_db) (unsafeCoerce l_al_db))))}

recover :: Prelude.IO
           (([]) ((,) (([]) BaseTypes.Coq_addr) (([]) BaseTypes.Coq_value)))
recover =
  (Prelude.>>=) (unsafeCoerce read_encrypted_log) (\hdr_log ->
    let {valid_hdr_part = Datatypes.fst (unsafeCoerce hdr_log)} in
    let {log = Datatypes.snd (unsafeCoerce hdr_log)} in
    let {txn_records = records valid_hdr_part} in
    (Prelude.>>=)
    (unsafeCoerce write_header (Build_header valid_hdr_part valid_hdr_part))
    (\_ -> (Prelude.>>=) ( ( (unsafeCoerce Interpreter.diskSync))) (\_ ->
    decrypt_txns txn_records log)))

init :: (([]) ((,) BaseTypes.Coq_addr BaseTypes.Coq_value)) -> Prelude.IO ()
init l_av =
  (Prelude.>>=) (unsafeCoerce write_header header0) (\_ -> (Prelude.>>=)
    (unsafeCoerce BatchOperations.write_batch (List.map Datatypes.fst l_av)
      (List.map Datatypes.snd l_av)) (\_ ->
     ( (unsafeCoerce Interpreter.diskSync))))


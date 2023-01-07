From Coq Require Extraction.
Require Import ExtrHaskellBasic.
(* Require Import ExtrHaskellNatInteger. *)
(** This is dangerous since Int is bounded, unlike Integer.
    Leaves the code open to overflows. 
    Until I find a better alternative,
    this is the hacky way to go. **)
Require Import ExtrHaskellNatInt. 
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Extraction Language Haskell.

Require Import Framework FSParameters.
Require LogCache Transaction BlockAllocator File.

(** Write to a file to test the system **)
Extract Constant addr => "Int".
Extract Inlined Constant addr_eq_dec => "(Prelude.==)".

Extract Constant user => "System.Posix.Types.UserID".
Extract Constant value => "Data.ByteString.ByteString".
Extract Inlined Constant block_size => "8 * 4096". (** 4KB blocks **)
Extract Constant value0 => "Data.ByteString.pack (Data.List.replicate (div (8 * 4096) 8) (0::Data.Word.Word8))".
Extract Inlined Constant file_blocks_count => "4096". (** 4K data blocks *)
Extract Inlined Constant log_length => "1024". (** 1024 log blocks *)
Extract Inlined Constant inode_count => "4096". (** 4K inodes *)
Extract Constant disk_size => "4 * 1024 * 1024 * 1024 + 1". (** 4 GB disk *)

Extract Constant addr_list_to_blocks => 
"Helpers.intListToByteStringList (div (8 * 4096) Helpers.intSize)".

Extract Constant blocks_to_addr_list => 
"Helpers.byteStringListToIntList".

Extract Constant hash => "Data.ByteString.ByteString".
Extract Constant hash0 => "Helpers.toByteString (Crypto.Hash.hash value0 :: Crypto.Hash.Digest Crypto.Hash.Algorithms.MD5)".
Extract Constant hash_eq_dec => "(Prelude.==)".

Extract Constant key => "Data.ByteString.ByteString".

Extract Constant bitmap => "Data.ByteString.ByteString".
Extract Constant zero_bitmap => "value0".
Extract Constant set_bit => "Helpers.setBit".
Extract Constant unset_bit => "Helpers.unsetBit".
Extract Constant test_bit => "Helpers.testBit".
Extract Constant get_first_zero_index => "Helpers.getFirstZeroIndex".

Extract Inlined Constant value_to_bits => "".

Extract Inlined Constant bits_to_value => "".

(** These need to be defined as well **)
Extract Constant Log.encode_header => "(Helpers.setToBlockSize (Prelude.div (8 Prelude.* 4096) 8) Prelude.. Data.Persist.encode)".
Extract Constant Log.decode_header =>
"\x -> case Data.Persist.decode x of {
Prelude.Left _ -> header0; 
Prelude.Right h -> h }".

Extract Constant Inode.encode_inode => "(Helpers.setToBlockSize (Prelude.div (8 Prelude.* 4096) 8) Prelude.. Data.Persist.encode)".
Extract Constant Inode.decode_inode =>
"\x -> case Data.Persist.decode x of {
Prelude.Left _ -> Build_Inode 0 []; 
Prelude.Right h -> h }".


(** Eliminate Horizontal Composition **) 
Extraction Implicit lift_L1 [ 1 2 ].
Extraction Implicit lift_L2 [ 1 2 ]. 
Extract Inlined Constant lift_L1 => "".
Extract Inlined Constant lift_L2 => "".

Extraction Inline Core.operation.
Extraction Inline LayerImplementation.prog. 

Extract Inductive LayerImplementation.prog' => "Prelude.IO" [ "" "Prelude.return" "(Prelude.>>=)" ].

(** Using file as a disk *)

Extract Inductive DiskLayer.disk_prog => "Prelude.IO" [ "Interpreter.diskRead" "Interpreter.diskWrite" "Interpreter.diskSync" ].
Extract Inductive CryptoLayer.crypto_prog => "Prelude.IO" [ "Interpreter.cryptoGetKey" "Interpreter.cryptoHash" "Interpreter.cryptoEncrypt" "Interpreter.cryptoDecrypt" ].
Extract Inductive CacheLayer.cache_prog => "Prelude.IO" [ "Interpreter.cacheRead" "Interpreter.cacheWrite" "Interpreter.cacheFlush"]. 
Extract Inductive ListLayer.list_prog => "Prelude.IO" [ "Interpreter.listGet" "Interpreter.listPut" "Interpreter.listDelete" ].


Extract Inductive AuthenticationLayer.authentication_prog =>
"Prelude.IO" [ "(\u -> do uid <- System.Posix.User.getEffectiveUserID; Prelude.return (u Prelude.== uid))" ].

Extract Inductive LoggedDiskLayer.logged_disk_prog => "Prelude.IO" [ "LogCache.read" "LogCache.write" "LogCache.recover" "LogCache.init" ].
Extract Inductive TransactionalDiskLayer.transactional_disk_prog => "Prelude.IO" [ "Transaction.read" "Transaction.write" "Transaction.commit" "Transaction.abort" "Transaction.recover" "Transaction.init" ].

Separate Extraction
           File.read File.write
           File.change_owner File.extend
           File.delete File.create
           File.get_file_size
           File.recover File.init
           Transaction.read
           Transaction.write Transaction.commit
           Transaction.abort
           Transaction.recover Transaction.init
           LogCache.read LogCache.write
           LogCache.recover LogCache.init.


(** Run compile.sh now *)

From Coq Require Extraction.
Require Import ExtrHaskellBasic.
(* Require Import ExtrHaskellNatInteger. *)
(** This is dangerous since Int is bounded, unlike Integer.
    Leaves the code open to overflows. Until I find a better alternative,
    this is the hacky way to go. **)
Require Import ExtrHaskellNatInt. 
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Extraction Language Haskell.

Require Import Framework FSParameters.
Require LogCache Transaction File.


Extract Constant addr => "Prelude.Int".
Extract Inlined Constant addr_eq_dec => "(Prelude.==)".

Extract Constant user => "System.Posix.Types.UserID".
Extract Constant value => "Prelude.Int". (** We need to change this but to what? **)
Extract Constant block_size => "8 Prelude.* 4096". (** 4KB blocks **) 
Extract Constant file_blocks_count => "4096". (** 4K data blocks *)
Extract Constant log_length => "500". (** 500 log blocks *)
Extract Constant inode_count => "4096". (** 4K inodes *)
Extract Constant disk_size => "4 Prelude.* 1024 Prelude.* 1024 Prelude.* 1024". (** 4 GB disk *)

(** These need to be defined as well
Extract Constant BlockAllocator.bits_to_value => "".
Extract Constant BlockAllocator.value_to_bits => "".

Extract Constant addr_list_to_blocks => "".
Extract Constant blocks_to_addr_list => "".

Extract Constant Log.encode_header => "".
Extract Constant Log.decode_header => "".

Extract Constant hash => "".
Extract Inline Constant hash_eq_dec => "".
Extract Inline Constant hash0 => "".

Extract Constant key => "".
Extract Constant Inode.encode_inode => "".
Extract Constant Inode.decode_inode => "".
**)

(** Eliminate Horizontal Composition **) 
Extraction Implicit lift_L1 [ 1 2 ].
Extraction Implicit lift_L2 [ 1 2 ]. 
Extract Inlined Constant lift_L1 => "".
Extract Inlined Constant lift_L2 => "".

Extraction Inline Core.operation.
Extraction Inline Language.prog. 

Extract Inductive Language.prog' => "Prelude.IO" [ "" "Prelude.return" "(Prelude.>>=)" ].

(** Use these to implement actual functionality 
Extract Inductive DiskLayer.disk_prog => "Prelude.IO" [ "DISK_READ" "DISK_WRITE" "DISK_SYNC" ].
Extract Inductive CryptoLayer.crypto_prog => "Prelude.IO" [ "GET_KEY" "HASH" "ENCRYPT" "DECRYPT" ].
Extract Inductive CacheLayer.cache_prog => "Prelude.IO" [ "CACHE_READ" "CACHE_WRITE" "CACHE_FLUSH"]. 
Extract Inductive ListLayer.list_prog => "Prelude.IO" [ "GET" "PUT" "DELETE" ].
*)

Extract Inductive AuthenticationLayer.authentication_prog => "Prelude.IO" [ "(\u -> do uid <- System.Posix.User.getEffectiveUserID; Prelude.return (u Prelude.== uid))" ].

Extract Inductive LoggedDiskLayer.logged_disk_prog => "Prelude.IO" [ "LogCache.read" "LogCache.write" "LogCache.recover" "LogCache.init" ].
Extract Inductive TransactionalDiskLayer.transactional_disk_prog => "Prelude.IO" [ "Transaction.read" "Transaction.write" "Transaction.commit" "Transaction.abort" "Transaction.recover" "Transaction.init" ].

Separate Extraction
           File.read File.write
           File.change_owner File.extend
           File.delete File.create
           File.recover File.init
           Transaction.read
           Transaction.write Transaction.commit
           Transaction.abort
           Transaction.recover Transaction.init
           LogCache.read LogCache.write
           LogCache.recover LogCache.init.


(** Run compile.sh now *)

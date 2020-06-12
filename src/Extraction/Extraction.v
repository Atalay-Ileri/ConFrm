From Coq Require Extraction.
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.
Extraction Language Haskell.

Require Import Framework FSParameters.
Require LogCache Transaction File.

Extract Inlined Constant addr => "Prelude.Integer".
Extract Constant user => "Prelude.Int".
Extract Constant value => "Prelude.Int".
Extract Constant file_blocks_count => "4096".
Extract Constant log_length => "500".
Extract Constant inode_count => "4096".
Extract Constant disk_size => "10 Prelude.* 4096".

(* Eliminate Horizontal Composition *) 
Extraction Implicit lift_L1 [ 1 2 ].
Extraction Implicit lift_L2 [ 1 2 ]. 
Extract Inlined Constant lift_L1 => "".
Extract Inlined Constant lift_L2 => "".

Extraction Inline Operation.prog.
Extraction Inline Language.prog. 

Extract Inductive Language.prog' => "Prelude.IO" [ "" "Prelude.return" "(Prelude.>>=)" ].

(* Use these to implement actual functionality
Extract Inductive DiskLayer.disk_prog => "Prelude.IO" [ "DISK_READ" "DISK_WRITE"  ].
Extract Inductive CryptoLayer.crypto_prog => "Prelude.IO" [ "GET_KEY" "HASH" "ENCRYPT" "DECRYPT" ].
Extract Inductive CacheLayer.cache_prog => "Prelude.IO" [ "CACHE_READ" "CACHE_WRITE" "CACHE_FLUSH"]. 
Extract Inductive AuthenticationLayer.authentication_prog => "Prelude.IO" [ "AUTHENTICATE" ].
Extract Inductive StorageLayer.storage_prog => "Prelude.IO" [ "GET" "PUT" "DELETE" ].
*)

Extract Inductive LoggedDiskLayer.logged_disk_prog => "Prelude.IO" [ "LogCache.read" "LogCache.write" ].
Extract Inductive TransactionalDiskLayer.transactional_disk_prog => "Prelude.IO" [ "Transaction.start" "Transaction.read" "Transaction.write" "Transaction.commit" "Transaction.abort" ].

Separate Extraction
           File.read File.write
           File.change_owner File.extend
           File.delete File.create
           Transaction.start Transaction.read
           Transaction.write Transaction.commit
           Transaction.abort
           LogCache.read LogCache.write.




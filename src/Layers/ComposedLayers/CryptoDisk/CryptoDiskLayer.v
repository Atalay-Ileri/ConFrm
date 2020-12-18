Require Import Framework.
Require Export DiskLayer CryptoLayer.
Import ListNotations.

Set Implicit Arguments.

Definition CryptoDiskOperation  :=  HorizontalComposition CryptoOperation (DiskOperation addr_dec value (fun a => a < disk_size)).
Definition CryptoDiskLang := Build_Language CryptoDiskOperation.  

Notation "'|CP|' p" := (@lift_L1 CryptoOperation (DiskOperation addr_dec value (fun a => a < disk_size)) CryptoLang _ p) (at level 59).
Notation "'|DP|' p" := (@lift_L2 CryptoOperation (DiskOperation addr_dec value (fun a => a < disk_size)) (DiskLang addr_dec value (fun a => a < disk_size)) _ p) (at level 59).
Notation "'|CO|' p" := (@lift_L1 CryptoOperation (DiskOperation addr_dec value (fun a => a < disk_size)) CryptoLang _ (Op CryptoOperation p)) (at level 59).
Notation "'|DO|' p" := (@lift_L2 CryptoOperation (DiskOperation addr_dec value (fun a => a < disk_size)) (DiskLang addr_dec value (fun a => a < disk_size)) _ (Op (DiskOperation addr_dec value (fun a => a < disk_size)) p)) (at level 59). 

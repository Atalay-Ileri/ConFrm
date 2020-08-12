Require Import Framework.
Require Export DiskLayer CryptoLayer.
Import ListNotations.

Set Implicit Arguments.

Definition CryptoDiskOperation :=  HorizontalComposition CryptoOperation (DiskOperation addr_dec value).
Definition CryptoDiskLang := Build_Language CryptoDiskOperation.


Notation "'|CP|' p" := (@lift_L1 CryptoOperation (DiskOperation addr_dec value) CryptoLang _ p) (at level 59).
Notation "'|DP|' p" := (@lift_L2 CryptoOperation (DiskOperation addr_dec value) (DiskLang addr_dec value) _ p) (at level 59).
Notation "'|CO|' p" := (@lift_L1 CryptoOperation (DiskOperation addr_dec value) CryptoLang _ (Op CryptoOperation p)) (at level 59).
Notation "'|DO|' p" := (@lift_L2 CryptoOperation (DiskOperation addr_dec value) (DiskLang addr_dec value) _ (Op (DiskOperation addr_dec value) p)) (at level 59).   
      

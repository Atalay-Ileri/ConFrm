Require Import Framework.
Require Import DiskLayer CryptoLayer.
Import ListNotations.

Set Implicit Arguments.

Definition CryptoDiskOperation :=  HorizontalComposition CryptoOperation DiskOperation.
Definition CryptoDiskLang := Build_Language CryptoDiskOperation.
Definition CryptoDiskHL := Build_HoareLogic CryptoDiskLang.


Notation "'|CP|' p" := (@lift_L1 CryptoOperation DiskOperation CryptoLang _ p) (at level 59).
Notation "'|DP|' p" := (@lift_L2 CryptoOperation DiskOperation DiskLang _ p) (at level 59).
Notation "'|CO|' p" := (@lift_L1 CryptoOperation DiskOperation CryptoLang _ (Op CryptoOperation p)) (at level 59).
Notation "'|DO|' p" := (@lift_L2 CryptoOperation DiskOperation DiskLang _ (Op DiskOperation p)) (at level 59).   
      

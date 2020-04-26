Require Import Framework.
Require Import DiskLayer CryptoLayer.
Import ListNotations.

Set Implicit Arguments.

Definition CryptoDiskOperation :=  HorizontalComposition CryptoOperation DiskOperation.
Definition CryptoDiskLang := Build_Language CryptoDiskOperation.
Definition CryptoDiskHL := Build_HoareLogic CryptoDiskLang.

Notation "| p |" := (Language.Op CryptoDiskOperation _ p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op CryptoDiskOperation _ p1) (fun x => p2))(right associativity, at level 60).

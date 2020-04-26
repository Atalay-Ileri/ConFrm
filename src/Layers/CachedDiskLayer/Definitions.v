Require Import Framework.
Require Import CryptoDiskLayer CacheLayer.
Import ListNotations.

Set Implicit Arguments.

Definition CachedDiskOperation :=  HorizontalComposition CacheOperation CryptoDiskOperation.
Definition CachedDiskLang := Build_Language CachedDiskOperation.
Definition CachedDiskHL := Build_HoareLogic CachedDiskLang.

Notation "| p |" := (Language.Op CachedDiskOperation _ p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op CachedDiskOperation _ p1) (fun x => p2))(right associativity, at level 60).

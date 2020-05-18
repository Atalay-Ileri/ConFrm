Require Import Framework.
Require Export CryptoDiskLayer CacheLayer.
Import ListNotations.

Set Implicit Arguments.

Definition CachedDiskOperation :=  HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation.
Definition CachedDiskLang := Build_Language CachedDiskOperation.
Definition CachedDiskHL := Build_HoareLogic CachedDiskLang.

Notation "'|CDCP|' p" := (@lift_L1 (CacheOperation addr_dec value) CryptoDiskOperation (CacheLang addr_dec value) _ p) (at level 59).
Notation "'|CDDP|' p" := (@lift_L2 (CacheOperation addr_dec value) CryptoDiskOperation CryptoDiskLang _ p) (at level 59).
Notation "'|CDCO|' p" := (@lift_L1 (CacheOperation addr_dec value) CryptoDiskOperation (CacheLang addr_dec value) _ (Op (CacheOperation addr_dec value) p)) (at level 59).
Notation "'|CDDO|' p" := (@lift_L2 (CacheOperation addr_dec value) CryptoDiskOperation CryptoDiskLang _ (Op CryptoDiskOperation p)) (at level 59).

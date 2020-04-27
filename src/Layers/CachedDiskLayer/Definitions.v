Require Import Framework.
Require Import CryptoDiskLayer CacheLayer.
Import ListNotations.

Set Implicit Arguments.

Definition CachedDiskOperation :=  HorizontalComposition CacheOperation CryptoDiskOperation.
Definition CachedDiskLang := Build_Language CachedDiskOperation.
Definition CachedDiskHL := Build_HoareLogic CachedDiskLang.

Notation "'|CDCP|' p" := (@lift_L1 CacheOperation CryptoDiskOperation CacheLang _ p) (at level 59).
Notation "'|CDDP|' p" := (@lift_L2 CacheOperation CryptoDiskOperation CryptoDiskLang _ p) (at level 59).
Notation "'|CDCO|' p" := (@lift_L1 CacheOperation CryptoDiskOperation CacheLang _ (Op CacheOperation p)) (at level 59).
Notation "'|CDDO|' p" := (@lift_L2 CacheOperation CryptoDiskOperation CryptoDiskLang _ (Op CryptoDiskOperation p)) (at level 59).

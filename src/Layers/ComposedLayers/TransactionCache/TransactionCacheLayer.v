Require Import Framework.
Require Export LoggedDiskLayer StorageLayer.
Import ListNotations.

Set Implicit Arguments.

Definition TransactionCacheOperation :=  HorizontalComposition (StorageOperation (list (addr * value))) LoggedDiskOperation.
Definition TransactionCacheLang := Build_Language TransactionCacheOperation.

Notation "'|TCCP|' p" := (@lift_L1 (StorageOperation (list (addr * value))) LoggedDiskOperation (StorageLang (list (addr * value))) _ p) (at level 59).
Notation "'|TCDP|' p" := (@lift_L2 (StorageOperation (list (addr * value))) LoggedDiskOperation LoggedDiskLang _ p) (at level 59).
Notation "'|TCCO|' p" := (@lift_L1 (StorageOperation (list (addr * value))) LoggedDiskOperation (StorageLang (list (addr * value))) _ (Op (StorageOperation (list (addr * value))) p)) (at level 59).
Notation "'|TCDO|' p" := (@lift_L2 (StorageOperation (list (addr * value))) LoggedDiskOperation LoggedDiskLang _ (Op LoggedDiskOperation p)) (at level 59).

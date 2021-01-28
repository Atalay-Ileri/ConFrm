Require Import Framework FSParameters.
Require Export LoggedDiskLayer ListLayer.
Import ListNotations.

Set Implicit Arguments.

Definition TransactionCacheOperation :=  HorizontalComposition (ListOperation (addr * value)) (LoggedDiskOperation log_length data_length).
Definition TransactionCacheLang := Build_Language TransactionCacheOperation.

Notation "'|TCCP|' p" := (@lift_L1 (ListOperation (addr * value)) (LoggedDiskOperation log_length data_length) (ListLang (addr * value)) _ p) (at level 59).
Notation "'|TCDP|' p" := (@lift_L2 (ListOperation (addr * value)) (LoggedDiskOperation log_length data_length) (LoggedDiskLang log_length data_length) _ p) (at level 59).
Notation "'|TCCO|' p" := (@lift_L1 (ListOperation (addr * value)) (LoggedDiskOperation log_length data_length) (ListLang (addr * value)) _ (Op (ListOperation (addr * value)) p)) (at level 59).
Notation "'|TCDO|' p" := (@lift_L2 (ListOperation (addr * value)) (LoggedDiskOperation log_length data_length) (LoggedDiskLang log_length data_length) _ (Op (LoggedDiskOperation log_length data_length) p)) (at level 59).

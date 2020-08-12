Require Import FSParameters Framework.
Require Export AuthenticationLayer TransactionalDiskLayer.
Import ListNotations.

Set Implicit Arguments.

Definition AuthenticatedDiskOperation :=  HorizontalComposition AuthenticationOperation (TransactionalDiskOperation data_length).
Definition AuthenticatedDiskLang := Build_Language AuthenticatedDiskOperation.

Notation "'|ADAP|' p" := (@lift_L1 AuthenticationOperation (TransactionalDiskOperation data_length) AuthenticationLang _ p) (at level 59).
Notation "'|ADDP|' p" := (@lift_L2 AuthenticationOperation (TransactionalDiskOperation data_length) (TransactionalDiskLang data_length) _ p) (at level 59).
Notation "'|ADAO|' p" := (@lift_L1 AuthenticationOperation (TransactionalDiskOperation data_length) AuthenticationLang  _ (Op AuthenticationOperation p)) (at level 59).
Notation "'|ADDO|' p" := (@lift_L2 AuthenticationOperation (TransactionalDiskOperation data_length) (TransactionalDiskLang data_length) _ (Op (TransactionalDiskOperation data_length) p)) (at level 59).

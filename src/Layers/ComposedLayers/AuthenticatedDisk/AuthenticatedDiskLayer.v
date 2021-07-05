Require Import FSParameters Framework.
Require Export AuthenticationLayer TransactionalDiskLayer.
Import ListNotations.

Set Implicit Arguments.

Definition ADOperation :=  HorizontalComposition AuthenticationOperation (TDOperation data_length).
Definition ADLang := Build_Language ADOperation.

Notation "'|ADAP|' p" := (@lift_L1 AuthenticationOperation (TDOperation data_length) AuthenticationLang _ p) (at level 59).
Notation "'|ADDP|' p" := (@lift_L2 AuthenticationOperation (TDOperation data_length) (TDLang data_length) _ p) (at level 59).
Notation "'|ADAO|' p" := (@lift_L1 AuthenticationOperation (TDOperation data_length) AuthenticationLang  _ (Op AuthenticationOperation p)) (at level 59).
Notation "'|ADDO|' p" := (@lift_L2 AuthenticationOperation (TDOperation data_length) (TDLang data_length) _ (Op (TDOperation data_length) p)) (at level 59).

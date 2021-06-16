Require Import Framework FSParameters.
Require Export AuthenticationLayer TransactionCacheLayer.
Require AuthenticatedDiskLayer.
Require TransactionalDiskRefinement.
Require FileDiskNoninterference.
Import ListNotations.

Set Implicit Arguments.

Definition ATCCore :=  HorizontalComposition AuthenticationOperation TransactionCacheOperation.
Definition ATCLang := Build_Language ATCCore.

Import AuthenticatedDiskLayer.
Import TransactionalDiskRefinement.

Import Refinement.

Definition ATC_valid_state := fun s => FileDiskNoninterference.TC_valid_state (fst s) (snd s).
Definition ATC_related_states u exc := fun s1 s2 : ATCLang.(state) => FileDiskNoninterference.TC_related_states u exc (fst s1) (snd s1) (snd s2).

Definition ATC_reboot_list n := map (fun f => fun s: ATCLang.(state) => (fst s, f (snd s))) (transaction_cache_reboot_list n).

Definition ATC_CoreRefinement := HC_Core_Refinement ATCLang AuthenticatedDiskLang TransactionalDiskCoreRefinement.
Definition ATC_Refinement := HC_Refinement ATCLang AuthenticatedDiskLang TransactionalDiskCoreRefinement.

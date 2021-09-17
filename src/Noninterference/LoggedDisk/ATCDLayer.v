Require Import Framework FSParameters.
Require Export AuthenticationLayer ListLayer CachedDiskLayer ATCLayer.
Require TransactionCacheLayer.
Require LoggedDiskRefinement.
Require FileDiskNoninterference.
Import ListNotations.

Set Implicit Arguments.

Definition TCDCore :=  HorizontalComposition (ListOperation (addr * value)) CachedDiskOperation.
Definition TCDLang := Build_Language TCDCore.

Import TransactionCacheLayer.
Import LoggedDiskRefinement.

Import AbstractOracles.

Definition TCD_valid_state := fun s => FileDiskNoninterference.CD_valid_state (fst s) (snd s).
(* Definition TCD_related_states u exc := fun s1 s2 : TCDLang.(state) => FileDiskNoninterference.CD_related_states u exc (fst s1) (snd s1) (snd s2).
*)

Definition TCD_reboot_f selector : TCDLang.(state) -> TCDLang.(state) := 
  fun s: TCDLang.(state) => ([], (empty_mem, 
(fst (snd (snd s)), select_total_mem selector (snd (snd (snd s)))))).
Definition TCD_reboot_list l_selector := map (fun f => fun s: TCDLang.(state) => ([]: list (addr * value), f (snd s))) (cached_disk_reboot_list l_selector).

Definition TCD_CoreRefinement := HC_Core_Refinement TCDLang TransactionCacheLang LoggedDiskCoreRefinement.
Definition TCD_Refinement := HC_Refinement TCDLang TransactionCacheLang LoggedDiskCoreRefinement.



(* ATCD *)
Definition ATCDCore :=  HorizontalComposition AuthenticationOperation TCDCore.
Definition ATCDLang := Build_Language ATCDCore.

(* 
Definition ATCD_valid_state := fun s => TCD_valid_state (fst s) (snd s).
Definition ATCD_related_states u exc := fun s1 s2 : ATCDLang.(state) => FileDiskNoninterference.CD_related_states u exc (fst s1) (snd s1) (snd s2).
*)

Definition ATCD_reboot_f selector := fun s: ATCDLang.(state) => (fst s, TCD_reboot_f selector (snd s)).
Definition ATCD_reboot_list l_selector := map (fun f => fun s: ATCDLang.(state) => (fst s, f (snd s))) (TCD_reboot_list l_selector).

Definition ATCD_refines_reboot selector s_imp s_abs := 
refines_reboot (snd (snd (ATCD_reboot_f selector s_imp))) (snd (snd (ATC_reboot_f s_abs))) /\
fst (ATCD_reboot_f selector s_imp)  = fst (ATC_reboot_f s_abs) /\
fst (snd (ATCD_reboot_f selector s_imp))  = fst (snd (ATC_reboot_f s_abs)).

Definition ATCD_CoreRefinement := HC_Core_Refinement ATCDLang ATCLang TCD_CoreRefinement.
Definition ATCD_Refinement := HC_Refinement ATCDLang ATCLang TCD_CoreRefinement.

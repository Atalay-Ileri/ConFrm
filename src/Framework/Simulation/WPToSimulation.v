Require Import Lia Primitives Layer Simulation.Definitions.

(** Proofs about simplifying Simulation proofs **)

(** WP reasoning for proving Simulations *)
Section LanguageWP.
  Variable O_imp O_abs: Core.
  Variable L_imp: Language O_imp.
  Variable L_abs: Language O_abs.
  Variable R: Refinement L_imp L_abs.

  
(* Per prog ones *)
Definition wp_low_to_high_prog' T (p2: L_abs.(prog) T) :=
  forall o1 o2 s1 s2 s1' v,
     L_imp.(weakest_precondition) (R.(compile) p2)  (fun r s => exists s2', R.(refines_to) s s2' /\ r = v) o1 s1 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     L_imp.(exec) o1 s1 (R.(compile) p2) (Finished s1' v) ->
     L_abs.(weakest_precondition) p2 (fun r s => R.(refines_to) s1' s /\ r = v) o2 s2.

Definition wcp_low_to_high_prog' T (p2: L_abs.(prog) T) :=
  forall o1 o2 s1 s2 s1',
     L_imp.(weakest_crash_precondition) (R.(compile) p2) (fun s => exists s2', R.(refines_to) s s2') o1 s1 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     L_imp.(exec) o1 s1 (R.(compile) p2) (Crashed s1') ->
     L_abs.(weakest_crash_precondition) p2 (fun s => R.(refines_to) s1' s) o2 s2.

Record WP_Simulation_prog T p2:=
  {
    wp_low_to_high_prog : wp_low_to_high_prog' T p2;
    wcp_low_to_high_prog : wcp_low_to_high_prog' T p2;
  }.


End LanguageWP.

(** Proofs about simplifying StrongSimulation proofs **)

(** WP reasoning for proving Simulations *)
Section LanguageWP.
  Variable O_imp O_abs: Core.
  Variable L_imp: Language O_imp.
  Variable L_abs: Language O_abs.
  Variable R: Refinement L_imp L_abs.

  
(* Per prog ones *)
Definition wp_low_to_high_prog' T (p2: L_abs.(prog) T) :=
  forall o1 o2 s1 s2 s1' v,
     L_imp.(weakest_precondition) (R.(compile) p2)  (fun r s => exists s2', R.(refines_to) s s2' /\ r = v) o1 s1 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     L_imp.(exec) o1 s1 (R.(compile) p2) (Finished s1' v) ->
     L_abs.(weakest_precondition) p2 (fun r s => R.(refines_to) s1' s /\ r = v) o2 s2.

Definition wcp_low_to_high_prog' T (p2: L_abs.(prog) T) :=
  forall o1 o2 s1 s2 s1',
     L_imp.(weakest_crash_precondition) (R.(compile) p2) (fun s => exists s2', R.(refines_to_crash) s s2') o1 s1 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     L_imp.(exec) o1 s1 (R.(compile) p2) (Crashed s1') ->
     L_abs.(weakest_crash_precondition) p2 (fun s => R.(refines_to_crash) s1' s) o2 s2.

Record WP_Simulation_prog T p2:=
  {
    wp_low_to_high_prog : wp_low_to_high_prog' T p2;
    wcp_low_to_high_prog : wcp_low_to_high_prog' T p2;
  }.


End LanguageWP.

Arguments wp_low_to_high_prog' {_ _ _ _} _ {_}.
Arguments wcp_low_to_high_prog' {_ _ _ _} _ {_}.
Arguments WP_Simulation_prog {_ _ _ _} _ {_}.

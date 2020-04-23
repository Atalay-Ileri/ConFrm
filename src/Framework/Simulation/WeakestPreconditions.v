Require Import List Primitives Layer Simulation.Definitions.

(* WP reasoning for proving bisimulations *)

Definition wp_low_to_high {O1 O2} {low: Language O1} {high: Language O2}
           (refines_to: low.(state) -> high.(state) -> Prop)
           (compilation_of: forall T, low.(prog) T -> high.(prog) T -> Prop)
           (oracle_refines_to : forall T, low.(state) -> high.(prog) T -> low.(oracle) -> high.(oracle) -> Prop) :=
  forall T o1 o2 s1 s2 s1' v p1 p2,
     low.(weakest_precondition) p1  (fun r s => exists s2', refines_to s s2' /\ r = v) o1 s1 ->
     compilation_of T p1 p2 ->
     refines_to s1 s2 ->
     oracle_refines_to T s1 p2 o1 o2 ->
     low.(exec) o1 s1 p1 (Finished s1' v) ->
     high.(weakest_precondition) p2 (fun r s => refines_to s1' s /\ r = v) o2 s2.

Definition wpc_low_to_high {O1 O2} {low: Language O1} {high: Language O2}
           (refines_to: low.(state) -> high.(state) -> Prop)
           (compilation_of: forall T, low.(prog) T -> high.(prog) T -> Prop)
           (oracle_refines_to : forall T, low.(state) -> high.(prog) T -> low.(oracle) -> high.(oracle) -> Prop) :=
  forall T o1 o2 s1 s2 s1' p1 p2,
     low.(weakest_crash_precondition) p1 (fun s => exists s2', refines_to s s2') o1 s1 ->
     compilation_of T p1 p2 ->
     refines_to s1 s2 ->
     oracle_refines_to T s1 p2 o1 o2 ->
     low.(exec) o1 s1 p1 (Crashed s1') ->
     high.(weakest_crash_precondition) p2 (fun s => refines_to s1' s) o2 s2.

Definition wp_high_to_low {O1 O2} {low: Language O1} {high: Language O2}
           (refines_to: low.(state) -> high.(state) -> Prop)
           (compilation_of: forall T, low.(prog) T -> high.(prog) T -> Prop)
           (oracle_refines_to : forall T, low.(state) -> high.(prog) T -> low.(oracle) -> high.(oracle) -> Prop) :=
  forall T o1 o2 s1 s2 s2' v p1 p2,
     high.(weakest_precondition) p2 (fun r s => exists s1', refines_to s1' s /\ r = v) o2 s2 ->
     compilation_of T p1 p2 ->
     refines_to s1 s2 ->
     oracle_refines_to T s1 p2 o1 o2 ->
     high.(exec) o2 s2 p2 (Finished s2' v) ->
     low.(weakest_precondition) p1 (fun r s => refines_to s s2' /\ r = v) o1 s1.

Definition wpc_high_to_low {O1 O2} {low: Language O1} {high: Language O2}
           (refines_to: low.(state) -> high.(state) -> Prop)
           (compilation_of: forall T, low.(prog) T -> high.(prog) T -> Prop)
           (oracle_refines_to : forall T, low.(state) -> high.(prog) T -> low.(oracle) -> high.(oracle) -> Prop) :=
  forall T o1 o2 s1 s2 s2' p1 p2,
    high.(weakest_crash_precondition) p2 (fun s => exists s1', refines_to s1' s) o2 s2 ->
    compilation_of T p1 p2 ->
    refines_to s1 s2 ->
    oracle_refines_to T s1 p2 o1 o2 ->
    high.(exec) o2 s2 p2 (Crashed s2') ->
    low.(weakest_crash_precondition) p1 (fun s => refines_to s s2') o1 s1.

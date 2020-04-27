Require Import List Primitives Layer Simulation.Definitions.

(* WP reasoning for proving bisimulations *)

Section OperationWP.
Import Operation.

Definition wp_low_to_high_op {low high: Operation}
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

Definition wpc_low_to_high_op {low high: Operation}
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

Definition wp_high_to_low_op {low high: Operation}
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

Definition wpc_high_to_low_op {low high: Operation}
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

End OperationWP.

Section LanguageWP.

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

Definition wp_low_to_high_prog {O1 O2} {low: Language O1} {high: Language O2}
           (refines_to: low.(state) -> high.(state) -> Prop)
           (compilation_of: forall T, low.(prog) T -> high.(prog) T -> Prop)
           (oracle_refines_to : forall T, low.(state) -> high.(prog) T -> low.(oracle) -> high.(oracle) -> Prop)
           {T} (p2: high.(prog) T):=
  forall o1 o2 s1 s2 s1' v p1,
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

End LanguageWP.

Section OperationToLanguageWP.
  
  Fixpoint lift_compilation_of {O1 O2} {L1: Language O1} {L2: Language O2}
             (compilation_of: forall T, O1.(Operation.prog) T -> O2.(Operation.prog) T -> Prop)
             T (p1: L1.(prog) T) (p2: L2.(prog) T) : Prop.
    destruct p2.
    (* Op *)
    - exact (exists p1', p1 = Op _ p1' /\ compilation_of T p1' p).
    (* Ret *)
    - exact (p1 = Ret t).
    (* Bind *)
    - exact (exists px1 py1,
               p1 = Bind px1 py1 /\
               lift_compilation_of O1 O2 L1 L2 compilation_of T px1 p2 /\
               (forall r, lift_compilation_of O1 O2 L1 L2 compilation_of T' (py1 r) (p r))).
  Defined.

  Fixpoint lift_oracle_refines_to {O1 O2} {L1: Language O1} {L2: Language O2}
           (compilation_of: forall T, O1.(Operation.prog) T -> O2.(Operation.prog) T -> Prop)
           (oracle_refines_to : forall T, O1.(Operation.state) -> O2.(Operation.prog) T ->
                                     O1.(Operation.oracle) -> O2.(Operation.oracle) -> Prop)
           T (s1 : L1.(state)) (p2: L2.(prog) T) (o1 : L1.(oracle)) (o2: L2.(oracle)) : Prop :=
    match p2 with
    | Op _ p2' =>
      exists o1' o2',
      o1 = [OpOracle _ o1'] /\
      o2 = [OpOracle _ o2'] /\
      oracle_refines_to _ s1 p2' o1' o2'
    | Ret _ =>
      (o1 = [Cont _] /\ o2 = [Cont _]) \/
      (o1 = [Crash _] /\ o2 = [Crash _])
    | @Bind _ T' T'' px py =>
      exists o1' o1'' o2' o2'',
      o1 = o1'++o1'' /\
      o2 = o2'++o2'' /\
      @lift_oracle_refines_to O1 O2 L1 L2 compilation_of oracle_refines_to _ s1 px o1' o2' /\
      (forall px1,
         @lift_compilation_of O1 O2 L1 L2 compilation_of _ px1 px ->
         forall s1' r,
           L1.(exec) o1' s1 px1 (Finished s1' r) ->
           @lift_oracle_refines_to O1 O2 L1 L2 compilation_of oracle_refines_to _ s1' (py r) o1'' o2'')
    end.
      
    
  Theorem  wp_low_to_high_op_to_lang :
           forall (O_low O_high: Operation) (low: Language O_low) (high: Language O_high)
           (refines_to: O_low.(Operation.state) -> O_high.(Operation.state) -> Prop)
           (compilation_of: forall T, O_low.(Operation.prog) T -> O_high.(Operation.prog) T -> Prop)
           (oracle_refines_to : forall T, O_low.(Operation.state) -> O_high.(Operation.prog) T ->
                                     O_low.(Operation.oracle) -> O_high.(Operation.oracle) -> Prop),

             wp_low_to_high_op refines_to compilation_of oracle_refines_to ->
             @wp_low_to_high O_low O_high low high refines_to (lift_compilation_of compilation_of) (lift_oracle_refines_to compilation_of oracle_refines_to).
  Proof.
    unfold wp_low_to_high_op, wp_low_to_high; intros.

    generalize dependent o1;
    generalize dependent o2;
    generalize dependent s1;
    generalize dependent s2;
    generalize dependent s1';
    generalize dependent v;
    generalize dependent p1;
    generalize dependent p2.
    induction p2; simpl in *; intros; cleanup; invert_exec.
    { (* Op *)
      inversion H0; cleanup; eauto.
    }
    {(* Ret *)
      split_ors; cleanup; eauto.
    }    
    {(* Bind *)
      clear H.
      simpl in *; cleanup.
      
      do 2 eexists; split; eauto.
      eapply wp_complete; intros; eauto.
      instantiate (1:= fun o s => exists s' r, exec high o s p2 (Finished s' r) /\ refines_to x7 s' /\ r = x8) in X.
      simpl in *; cleanup.
      
      do 2 eexists; split; eauto.
      eapply H0.
      eauto.
      eauto.
      admit.
      eapply H8; eauto.
      (* TODO: Maybe finish these transfer lemmas? *)
  Abort.
  
End OperationToLanguageWP.

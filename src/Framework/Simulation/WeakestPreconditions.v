Require Import List Primitives Layer Simulation.Definitions.
Require Simulation.RefinementLift.

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
  Variable OL OH: Operation.
  Variable LL: Language OL.
  Variable LH: Language OH.
  Variable R: Refinement LL LH.

  
(* Per prog ones *)
Definition wp_low_to_high_prog' T (p2: LH.(prog) T) :=
  forall o1 o2 s1 s2 s1' v,
     LL.(weakest_precondition) (R.(compile) p2)  (fun r s => exists s2', R.(refines_to) s s2' /\ r = v) o1 s1 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     LL.(exec) o1 s1 (R.(compile) p2) (Finished s1' v) ->
     LH.(weakest_precondition) p2 (fun r s => R.(refines_to) s1' s /\ r = v) o2 s2.

Definition wp_high_to_low_prog' T (p2: LH.(prog) T) :=
  forall o1 o2 s1 s2 s2' v,
     LH.(weakest_precondition) p2 (fun r s => exists s1', R.(refines_to) s1' s /\ r = v) o2 s2 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     LH.(exec) o2 s2 p2 (Finished s2' v) ->
     LL.(weakest_precondition) (R.(compile) p2) (fun r s => R.(refines_to) s s2' /\ r = v) o1 s1.

Definition wcp_low_to_high_prog' T (p2: LH.(prog) T) :=
  forall o1 o2 s1 s2 s1',
     LL.(weakest_crash_precondition) (R.(compile) p2) (fun s => exists s2', R.(refines_to) s s2') o1 s1 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     LL.(exec) o1 s1 (R.(compile) p2) (Crashed s1') ->
     LH.(weakest_crash_precondition) p2 (fun s => R.(refines_to) s1' s) o2 s2.

Definition wcp_high_to_low_prog' T (p2: LH.(prog) T) :=
  forall o1 o2 s1 s2 s2',
    LH.(weakest_crash_precondition) p2 (fun s => exists s1', R.(refines_to) s1' s) o2 s2 ->
    R.(refines_to) s1 s2 ->
    R.(oracle_refines_to) s1 p2 o1 o2 ->
    LH.(exec) o2 s2 p2 (Crashed s2') ->
    LL.(weakest_crash_precondition) (R.(compile) p2) (fun s => R.(refines_to) s s2') o1 s1.


(* General Ones *)
Definition wp_low_to_high' :=
  forall T o1 o2 s1 s2 s1' v (p2: LH.(prog) T),
     LL.(weakest_precondition) (R.(compile) p2) (fun r s => exists s2', R.(refines_to) s s2' /\ r = v) o1 s1 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     LL.(exec) o1 s1 (R.(compile) p2) (Finished s1' v) ->
     LH.(weakest_precondition) p2 (fun r s => R.(refines_to) s1' s /\ r = v) o2 s2.

Definition wp_high_to_low' :=
  forall T o1 o2 s1 s2 s2' v (p2: LH.(prog) T),
     LH.(weakest_precondition) p2 (fun r s => exists s1', R.(refines_to) s1' s /\ r = v) o2 s2 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     LH.(exec) o2 s2 p2 (Finished s2' v) ->
     LL.(weakest_precondition) (R.(compile) p2) (fun r s => R.(refines_to) s s2' /\ r = v) o1 s1.

Definition wcp_low_to_high'  :=
  forall T o1 o2 s1 s2 s1' (p2: LH.(prog) T),
     LL.(weakest_crash_precondition) (R.(compile) p2) (fun s => exists s2', R.(refines_to) s s2') o1 s1 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     LL.(exec) o1 s1 (R.(compile) p2) (Crashed s1') ->
     LH.(weakest_crash_precondition) p2 (fun s => R.(refines_to) s1' s) o2 s2.

Definition wcp_high_to_low'  :=
  forall T o1 o2 s1 s2 s2' (p2: LH.(prog) T),
    LH.(weakest_crash_precondition) p2 (fun s => exists s1', R.(refines_to) s1' s) o2 s2 ->
    R.(refines_to) s1 s2 ->
    R.(oracle_refines_to) s1 p2 o1 o2 ->
    LH.(exec) o2 s2 p2 (Crashed s2') ->
    LL.(weakest_crash_precondition) (R.(compile) p2) (fun s => R.(refines_to) s s2') o1 s1.

Definition exec_preserves_refinement :=
    forall T (p: LH.(prog) T) o2 s2 ret,
      (exists s1, R.(refines_to) s1 s2) ->
      LH.(exec) o2 s2 p ret ->
      (exists s1', R.(refines_to) s1' (extract_state ret)).

Definition exec_compiled_preserves_refinement  :=
    forall T (p2: LH.(prog) T) o1 s1 ret,
      (exists s2, R.(refines_to) s1 s2) ->
      LL.(exec) o1 s1 (R.(compile) p2) ret ->
      (exists s2', R.(refines_to) (extract_state ret) s2').

Record WP_Bisimulation_prog T p2:=
  {
    wp_low_to_high_prog : wp_low_to_high_prog' T p2;
    wp_high_to_low_prog : wp_high_to_low_prog' T p2;
    wcp_low_to_high_prog : wcp_low_to_high_prog' T p2;
    wcp_high_to_low_prog : wcp_high_to_low_prog' T p2;
  }.

Record WP_Bisimulation :=
  {
    wp_low_to_high : wp_low_to_high';
    wp_high_to_low : wp_high_to_low';
    wcp_low_to_high : wcp_low_to_high';
    wcp_high_to_low : wcp_high_to_low';
  }.
End LanguageWP.

Arguments WP_Bisimulation_prog {_ _ _ _} _ {_}.
Arguments WP_Bisimulation {_ _ _ _}.
Arguments exec_preserves_refinement {_ _ _ _}.
Arguments exec_compiled_preserves_refinement {_ _ _ _}.

(*
Lemma refinement_preservation_from_sp:
  forall O1 O2 (low: Language O1) (high: Language O2)   
    (R.(refines_to) : low.(state) -> high.(state) -> Prop),
    exec_preserves_refinement refines_to.
Proof.
  unfold exec_preserves_refinement; intros; cleanup.
  destruct ret; simpl in *; cleanup.
  {
    eapply_fresh exec_to_sp in H0.
    instantiate (1:= fun o s => exists s1', R.(refines_to) s1' s) in Hx.
    2: simpl; eauto.
Abort.
*)

  Import RefinementLift.
  
  Theorem sbs_ret :
    forall OL OH (LL: Language OL) (LH: Language OH) (Refinement: OperationRefinement LL OH) T (v: T),
    StrongBisimulationForProgram (LiftRefinement LH Refinement) (Ret v).              
  Proof.
    intros.
    constructor; simpl; split; intros;
    invert_exec; cleanup;
    split_ors; cleanup;
    invert_exec; cleanup;
    eexists; intuition eauto;
    try solve [ econstructor; eauto ];
    simpl eauto.
  Qed.

  Theorem sbs_bind:
    forall OL OH (LL: Language OL) (LH: Language OH) (Refinement: OperationRefinement LL OH)
      T1 T2 (p1: LH.(prog) T1) (p2: T1 -> LH.(prog) T2),
      StrongBisimulationForProgram (LiftRefinement LH Refinement) p1 ->
      (forall t, StrongBisimulationForProgram (LiftRefinement LH Refinement) (p2 t)) ->
      StrongBisimulationForProgram (LiftRefinement LH Refinement) (Bind p1 p2).
  Proof.
    intros.
    edestruct H.
    constructor; intros.
    simpl in *; cleanup.

    split; intros.
    - (* Low to High *)
      invert_exec; cleanup.
      
      + split_ors; cleanup.
        eapply_fresh exec_deterministic_wrt_oracle_prefix in H5; eauto; cleanup.
     
        eapply_fresh exec_finished_deterministic_prefix in H5; eauto; cleanup.
        eapply_fresh exec_deterministic_wrt_oracle in H6; eauto; cleanup.
        edestruct strong_bisimulation_for_program_correct; eauto.
        edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H3.
        edestruct H0.
        simpl in *; 
        edestruct strong_bisimulation_for_program_correct0; eauto.
        edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H3.
        destruct x, x0; simpl in *; cleanup.
        eexists; intuition eauto.
        econstructor; eauto.
        simpl; eauto.
        simpl; eauto.
        
      +
        split_ors; cleanup;
        split_ors; cleanup;
        eapply_fresh exec_deterministic_wrt_oracle_prefix in H4; eauto; cleanup;
        try solve [eapply_fresh exec_deterministic_wrt_oracle_prefix in H5; eauto; cleanup].
        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H6; eauto; simpl in *; cleanup; try intuition; clear H6 H7.
          destruct x6; simpl in *; cleanup.
          exists (Crashed s); repeat (split; eauto).
          eapply ExecBindCrash; eauto.

        *
          eapply_fresh exec_finished_deterministic_prefix in H4; eauto; cleanup.
          eapply_fresh exec_deterministic_wrt_oracle in H5; eauto; cleanup.
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H3.
          destruct x0; simpl in *; cleanup.
          edestruct H0.
          simpl in *;
          edestruct strong_bisimulation_for_program_correct0; eauto.
          edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H3.
          destruct x0; simpl in *; cleanup.
          eexists; intuition eauto.
          econstructor; eauto.
          simpl; eauto.
          simpl; eauto.

    - (* High to Low *)
      invert_exec; cleanup.
      

      + split_ors; cleanup.
        edestruct strong_bisimulation_for_program_correct; eauto.
        edestruct H7; eauto; simpl in *; cleanup; try intuition; clear H7 H8.
        eapply_fresh exec_deterministic_wrt_oracle_prefix in H2; eauto; simpl in *; cleanup.
        simpl in *; cleanup.

        edestruct strong_bisimulation_for_program_correct; eauto.
        edestruct H9; eauto; simpl in *; cleanup; try intuition; clear H9 H10.
        
        destruct x10; simpl in *; cleanup; eauto.
        eapply_fresh exec_finished_deterministic_prefix in H2; eauto; cleanup.
        simpl in *.
        edestruct H0.
        simpl in *;
        edestruct strong_bisimulation_for_program_correct0; eauto.
        edestruct H5; eauto; simpl in *; cleanup; try intuition; clear H5 H9; cleanup.           
        eapply_fresh exec_deterministic_wrt_oracle in H3; eauto; simpl in *; cleanup.
        destruct x9; simpl in *; cleanup; eauto.
        eexists; intuition eauto.
        econstructor; eauto.
        simpl; eauto.
        simpl; eauto.
        
      +
        split_ors; cleanup;
        split_ors; cleanup;
        eapply_fresh exec_deterministic_wrt_oracle_prefix in H4; eauto; cleanup;
        try solve [eapply_fresh exec_deterministic_wrt_oracle_prefix in H5; eauto; cleanup].
        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H6; eauto; simpl in *; cleanup; try intuition; clear H6 H7.
          destruct x6; simpl in *; cleanup.
          eapply_fresh exec_deterministic_wrt_oracle_prefix in H3; eauto; cleanup.
          simpl in *.
          exists (Crashed x5); repeat (split; eauto).
          eapply ExecBindCrash; eauto.

        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H8; eauto; simpl in *; cleanup; try intuition; clear H8 H9.
          destruct x8; simpl in *; cleanup.
          eapply_fresh exec_deterministic_wrt_oracle_prefix in H3; eauto; cleanup.

        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H7; eauto; simpl in *; cleanup; try intuition; clear H7 H8.
          destruct x8; simpl in *; cleanup.
          eapply_fresh exec_deterministic_wrt_oracle_prefix in H3; eauto; cleanup.

        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H9; eauto; simpl in *; cleanup; try intuition; clear H9 H10.
          destruct x10; simpl in *; cleanup.
          eapply_fresh exec_finished_deterministic_prefix in H3; eauto; cleanup.
          edestruct H0.
          simpl in *;
          edestruct strong_bisimulation_for_program_correct0; eauto.
          edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H9.
          cleanup.
          eapply_fresh exec_deterministic_wrt_oracle in H5; eauto; cleanup.
          eexists; intuition eauto.
          econstructor; eauto.
    Unshelve.
    all: eauto.
  Qed.

  Hint Resolve sbs_ret sbs_bind.

Theorem bisimulation_from_wp_prog :
  forall OL OH (LL: Language OL) (LH: Language OH) (R: Refinement LL LH) T (p2: LH.(prog) T),

    exec_preserves_refinement R ->

    exec_compiled_preserves_refinement R ->
    
    WP_Bisimulation_prog R p2 ->
    
    StrongBisimulationForProgram R p2.
Proof.  
  intros; eapply Build_StrongBisimulationForProgram;
  intros; cleanup; split; intros.
  {(* low -> high *)
    match goal with
    |[H: exec LL  _ _ _ _,
      H0: exec_compiled_preserves_refinement _ |- _ ] =>
     eapply_fresh H0 in H; eauto; cleanup
    end.
    destruct s1'; simpl in *.
    {(* wp *)
      pose proof exec_to_wp as Hx.
      match goal with
      |[H: exec LL _ _ _ _  |- _ ] =>
       specialize Hx with (1:= H); simpl in *
      end.
      edestruct wp_to_exec.
      eapply wp_low_to_high_prog; eauto.
      cleanup.
      eexists; split; eauto.
    }
    {(* wcp *)
      pose proof exec_to_wcp as Hx.
      match goal with
      |[H: exec LL _ _ _ _  |- _ ] =>
       specialize Hx with (1:= H); simpl in *
      end.
      edestruct wcp_to_exec.
      eapply wcp_low_to_high_prog; eauto.
      cleanup.
      eexists; split; eauto.
    }
  }

  {(* high -> low *)
    match goal with
    |[H: exec LH _ _ _ _,
      H0: exec_preserves_refinement _ |- _ ] =>
     eapply_fresh H0 in H; eauto; cleanup
    end.
    destruct s2'; simpl in *.
    {(* wp *)
      pose proof exec_to_wp as Hx.
      match goal with
      |[H: exec LH _ _ _ _  |- _ ] =>
       specialize Hx with (1:= H); simpl in *
      end.
      edestruct wp_to_exec.
      eapply wp_high_to_low_prog; eauto.
      cleanup.
      eexists; split; simpl; eauto.
    }
    {(* wcp *)
      pose proof exec_to_wcp as Hx.
      match goal with
      |[H: exec LH _ _ _ _  |- _ ] =>
       specialize Hx with (1:= H); simpl in *
      end.
      edestruct wcp_to_exec.
      eapply wcp_high_to_low_prog; eauto.
      cleanup.
      eexists; split; eauto.
    }
  }
Qed.


Lemma sp_impl:
    forall O (L: Language O) T (p: prog L T) (P P': list (Language.token' O) -> Operation.state O -> Prop) s' t,
      (forall o s, P' o s -> P o s) ->
      strongest_postcondition L p P' t s' ->
      strongest_postcondition L p P t s'.
  Proof.
    intros.
    eapply sp_to_exec in H0; cleanup.
    eapply exec_to_sp; eauto.
  Qed.

  Lemma sp_bind:
    forall O (L: Language O) T T' (p1: prog L T) (p2: T -> prog L T') P s' t,
      strongest_postcondition L (Bind p1 p2) P t s' ->
      exists s0 t0,
        strongest_postcondition L p1 (fun o s => exists o2, P (o++o2) s) t0 s0 /\
        strongest_postcondition L (p2 t0)
        (fun o s => strongest_postcondition L p1 (fun ox sx => P (ox++o) sx) t0 s) t s'.
  Proof.
    intros.
    eapply sp_to_exec in H; cleanup.
    invert_exec.
    do 2 eexists; split.
    eapply exec_to_sp; eauto.
    intros.            
    repeat (eapply exec_to_sp; eauto).
  Qed.


Lemma sp_exists_extract:
    forall X O (L: Language O) T (p: prog L T) (P: X -> list (Language.token' O) -> Operation.state O -> Prop) s' t,
      strongest_postcondition L p (fun o s => exists x, P x o s) t s' ->
      (exists x, strongest_postcondition L p (P x) t s').
  Proof.
    intros.
    eapply sp_to_exec in H; cleanup.
    eexists; eapply exec_to_sp; eauto.
  Qed.

Theorem sp_lift1:
  forall O1 O2 (L1 : Language O1) (L2: Language O2) (HL: Language (HorizontalComposition O1 O2))
    T (p: prog L1 T) s t P,
    strongest_postcondition HL (lift_L1 O2 p) P t s ->
    strongest_postcondition L1 p (fun o sx => P (map (fun o' =>
                                                     match o' with
                                                     |OpOracle _ o1 =>
                                                      OpOracle (HorizontalComposition O1 O2) [Oracle1 O1 O2 o1]%list
                                                     |Language.Cont _ =>
                                                      Language.Cont _
                                                     |Language.Crash _ =>
                                                      Language.Crash _
                                                     end) o) (sx, snd s)) t (fst s).
Proof.
  induction p; destruct s; simpl in *; intros; cleanup; eauto.
  eapply H in H0; simpl in *.
  eapply sp_to_exec in H0; cleanup.
  eapply IHp in H1; simpl in *.
  setoid_rewrite <- map_app in H1.
  exists x; intuition eauto.
  eapply exec_to_sp; eauto.
Qed.

Theorem sp_lift2:
  forall O1 O2 (L1 : Language O1) (L2: Language O2) (HL: Language (HorizontalComposition O1 O2))
    T (p: prog L2 T) s t P,
    strongest_postcondition HL (lift_L2 O1 p) P t s ->
    strongest_postcondition L2 p (fun o sx => P (map (fun o' =>
                                                     match o' with
                                                     |OpOracle _ o2 =>
                                                      OpOracle (HorizontalComposition O1 O2) [Oracle2 O1 O2 o2]%list
                                                     |Language.Cont _ =>
                                                      Language.Cont _
                                                     |Language.Crash _ =>
                                                      Language.Crash _
                                                     end) o) (fst s, sx)) t (snd s).
Proof.
  induction p; destruct s; simpl in *; intros; cleanup; eauto.
  eapply H in H0; simpl in *.
  eapply sp_to_exec in H0; cleanup.
  eapply IHp in H1; simpl in *.
  setoid_rewrite <- map_app in H1.
  exists x; intuition eauto.
  eapply exec_to_sp; eauto.
Qed.

Theorem sp_extract_precondition:
  forall O (L : Language O) T (p: prog L T) s t P,
    strongest_postcondition L p P t s ->
    strongest_postcondition L p P t s /\ (exists o s, P o s).
Proof.
  intros; eapply_fresh sp_to_exec in H; cleanup; eauto.
Qed.

(*
Theorem bisimulation_from_wp:
  forall O1 O2 (low: Language O1) (high: Language O2)   
    refines_to
    compilation_of
    oracle_refines_to,
    
    exec_compiled_preserves_refinement
    refines_to
    compilation_of ->

    exec_preserves_refinement refines_to ->

    wp_low_to_high
      refines_to
      compilation_of
      oracle_refines_to ->

    wcp_low_to_high
      refines_to
      compilation_of
      oracle_refines_to ->

    wp_high_to_low
      refines_to
      compilation_of
      oracle_refines_to ->

    wcp_high_to_low
      refines_to
      compilation_of
      oracle_refines_to ->
    
    StrongBisimulation
      low
      high
      refines_to
      compilation_of
      oracle_refines_to.
Proof.  
  intros; eapply Build_StrongBisimulation;
  intros; cleanup; split; intros.
  {(* low -> high *)
    match goal with
    |[H: exec low _ _ _ _ ,
      H0: exec_compiled_preserves_refinement _ _ |- _ ] =>
     eapply_fresh H0 in H; eauto; cleanup
    end.
    destruct s1'; simpl in *.
    {(* wp *)
      pose proof exec_to_wp as Hx.
      match goal with
      |[H: exec low _ _ _ _  |- _ ] =>
       specialize Hx with (1:= H); simpl in *
      end.
      edestruct wp_to_exec.
      match goal with
      |[H: wp_low_to_high _ _ _  |- _ ] =>
       eapply H; eauto
      end.
      cleanup.
      eexists; split; eauto.
    }
    {(* wcp *)
      pose proof exec_to_wcp as Hx.
      match goal with
      |[H: exec low _ _ _ _  |- _ ] =>
       specialize Hx with (1:= H); simpl in *
      end.
      edestruct wcp_to_exec.
      match goal with
      |[H: wcp_low_to_high _ _ _  |- _ ] =>
       eapply H; eauto
      end.
      cleanup.
      eexists; split; eauto.
    }
  }

  {(* high -> low *)
    match goal with
    |[H: exec high _ _ _ _ ,
      H0: exec_preserves_refinement _ |- _ ] =>
     eapply_fresh H0 in H; eauto; cleanup
    end.
    destruct s2'; simpl in *.
    {(* wp *)
      pose proof exec_to_wp as Hx.
      match goal with
      |[H: exec high _ _ _ _  |- _ ] =>
       specialize Hx with (1:= H); simpl in *
      end.
      edestruct wp_to_exec.
      match goal with
      |[H: wp_high_to_low _ _ _  |- _ ] =>
       eapply H; eauto
      end.
      cleanup.
      eexists; split; simpl; eauto.
      simpl; eauto.
    }
    {(* wcp *)
      pose proof exec_to_wcp as Hx.
      match goal with
      |[H: exec high _ _ _ _  |- _ ] =>
       specialize Hx with (1:= H); simpl in *
      end.
      edestruct wcp_to_exec.
      match goal with
      |[H: wcp_high_to_low _ _ _  |- _ ] =>
       eapply H; eauto
      end.
      cleanup.
      eexists; split; eauto.
      simpl; eauto.
    }
  }
Qed.



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
*)

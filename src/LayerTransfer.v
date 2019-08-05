Require Import Primitives Simulation Confidentiality.
Require Import SimpleDisk Omega FunctionalExtensionality.
Require Import ProgLimited Layer2.
Import ListNotations.
Close Scope pred_scope.
Set Implicit Arguments.


Section LayerTransfer.

  Definition right_total_filtered {T1 T2: Type} (R: T1 -> T2 -> Prop) (P: T2 -> Prop):=
    forall t2,
    P t2 ->
    exists t1, R t1 t2.

Definition simulation_preserving {T1 T2: Type} (S1: T1 -> T1 -> Prop) (S2: T2 -> T2 -> Prop)(R: T1 -> T2 -> Prop) :=
  forall t1 t1' t2 t2',
    R t1 t2 ->
    R t1' t2' ->
    S1 t1 t1' <-> S2 t2 t2'.
    
  Definition refines_to (s1 : state) (s2: state2) :=
    Prog.get_user s1 = get_user s2 /\
    Prog.get_oracle s1 = get_oracle s2 /\
    rep (get_disk s2) (Prog.get_disk s1) /\
    Prog.get_store s1 = get_store s2.

  Ltac simpl_refines_to :=
    unfold refines_to, Prog.get_user, get_user,
        Prog.get_oracle, get_oracle,
        Prog.get_disk, get_disk,
        Prog.get_store, get_store in *; simpl in *.

  
  Ltac simpl_states:=
    unfold state, state2 in *; destruct_pairs; simpl in *.

  Definition refines_to_same st1 st2 := exists sr, refines_to st1 sr /\ refines_to st2 sr.


  Lemma exec_preserves_user:
      forall T (p: prog T) st1 st1' tr,
        exec st1 p st1' tr ->
        Prog.get_user st1 = Prog.get_user (extract_state st1').
    Proof.
      induction 1; simpl in *; eauto.
      cleanup; eauto.
    Qed.

    Lemma exec_deterministic_oracle:
      forall T (p: prog T) st1 st2 st1' st2' tr1 tr2,
        exec st1 p st1' tr1 ->
        exec st2 p st2' tr2 ->
        Prog.get_oracle st1 = Prog.get_oracle st2 ->
        Prog.get_oracle (extract_state st1') = Prog.get_oracle (extract_state st2').
    Proof.
      unfold Prog.get_oracle;
        induction p; intros; simpl in *;
          simpl_states; cleanup;
            invert_exec; invert_exec;
              cleanup; simpl in *;
          cleanup; eauto;
      try match goal with
      |[H: _ :: _ = _ :: _ |- _] =>
       inversion H; eauto
          end.      
      simpl_states; cleanup.
   Abort.

  
  Lemma exec_limited_preserves_refinement:
      forall T (p: prog_limited T)  st1 st2 st1' st2',
        exec_limited st1 p st1' ->
        exec_limited st2 p st2' ->
        refines_to_same st1 st2 ->
        refines_to_same (extract_state st1') (extract_state st2').
  Proof.
    unfold refines_to_same, refines_to;
      induction p; simpl in *;
        intros; simpl_refines_to; simpl_states; cleanup.
    
    - inversion H; sigT_eq; clear H;
        inversion H0; sigT_eq; clear H0;
          simpl_states.
      edestruct alloc_ok; eauto.
      apply pimpl_star_emp; eauto.
      destruct H; cleanup.
      destruct_lift H1.
      edestruct alloc_ok; [| apply H6 | eauto].
      apply pimpl_star_emp; eauto.
      destruct H1; cleanup.
      destruct_lift H3.
      destruct H8, H11; cleanup.
  Admitted.
  
  Lemma rep_equivalent_for:
      forall u d1 d2 d1' d2',
        equivalent_for_fst u d1 d1' ->
        rep d2 d1 ->
        rep d2' d1' ->
        equivalent_for u d2 d2'.
    Proof.
      unfold equivalent_for, equivalent_for_fst, rep; intros.
      destruct_lift H0; destruct_lift H1; cleanup.

      specialize (H 0) as Hx; destruct Hx; cleanup.
      erewrite ptsto_valid in H2; [| pred_apply; cancel]; cleanup.
      
      erewrite ptsto_valid in H2; [| pred_apply; cancel]; cleanup.
      erewrite ptsto_valid in H3; [| pred_apply; cancel]; cleanup.
      simpl in *; cleanup.
      specialize (H18 (can_access_public u)); inversion H18; cleanup.

      specialize (H a) as Hx.
      
      destruct (Compare_dec.le_lt_dec a 2); [|intuition].
      destruct a; [intuition|].
      destruct a.
      destruct Hx; cleanup.
      erewrite ptsto_valid in H2; [| pred_apply; cancel]; cleanup.
      
      erewrite ptsto_valid in H2; [| pred_apply; cancel]; cleanup.
      erewrite ptsto_valid in H3; [| pred_apply; cancel]; cleanup.
      simpl in *; cleanup.      
      
      destruct (value_to_nat dummy1); [intuition|].
      destruct n; [intuition|].
      right; do 2 eexists; intuition eauto; simpl in *.
      destruct n; [intuition|].
      destruct n; [intuition|].
      right; do 2 eexists; intuition eauto; simpl in *.
      omega.

      destruct a; [|intuition].
      destruct Hx; cleanup.
      erewrite ptsto_valid in H2; [| pred_apply; cancel]; cleanup.
      
      erewrite ptsto_valid in H2; [| pred_apply; cancel]; cleanup.
      erewrite ptsto_valid in H3; [| pred_apply; cancel]; cleanup.
      simpl in *; cleanup.      
      
      destruct (value_to_nat dummy1); [intuition|].
      destruct n; [intuition|].
      destruct n; [intuition|].
      right; do 2 eexists; intuition eauto; simpl in *.
      destruct n; [intuition|].
      right; do 2 eexists; intuition eauto; simpl in *.
      omega.
    Qed.

    
    Theorem RS_right_total_filtered :
      right_total_filtered refines_to (fun d2 => exists d1, rep (get_disk d2) d1).
    Proof.
      unfold state, state2, refines_to, right_total_filtered; intros;
      simpl_refines_to; simpl_states; cleanup.
      exists (x, x0, x3, x2); destruct_pairs; intuition eauto.
    Qed.

    Lemma RS_simulation_preserving:
      forall u, simulation_preserving refines_to_same (state_equivalent_for u) refines_to.
    Proof.
      unfold simulation_preserving, refines_to_same, refines_to,
      Prog.state_equivalent_for, state_equivalent_for; intros.
      simpl_refines_to; simpl_states; cleanup.
      split; intros; cleanup; intuition.
      admit.
      admit.

      exists(x, x0, x1, x2); intuition eauto.
      simpl in *.
    Abort.
  
    
  

    

    Lemma exec_preserves_rep:
      forall T (p: prog2 T)  st1 d1 st1' tr,
        exec st1 (prog2_to_prog p) st1' tr ->
        rep d1 (Prog.get_disk st1) ->
        exists d1', rep d1' (Prog.get_disk (extract_state st1')).
    Proof.
      induction p; intros; cleanup; simpl in *; eauto;
      unfold Prog.get_disk, state in *; destruct_pairs; simpl in *.
      - edestruct alloc_ok; eauto.
        apply pimpl_star_emp; eauto.
        destruct H1; cleanup;
        destruct_lift H3; eauto.

      - edestruct free_ok; eauto.
        apply pimpl_star_emp; eauto.
        destruct H1; cleanup;
        destruct_lift H3; eauto.

      - edestruct read_ok; eauto.
        apply pimpl_star_emp; eauto.
        destruct H1; cleanup;
        destruct_lift H3; eauto.

      - edestruct write_ok'; eauto.
        apply pimpl_star_emp; eauto.
        destruct H1; cleanup;
          destruct_lift H3; eauto.
        
      - invert_exec; cleanup; simpl in *; eauto.

      - invert_exec.
        eapply IHp in H0; eauto; cleanup; simpl in *.
        eapply H in H2; eauto; cleanup; simpl in *.
        
        destruct H0; cleanup; simpl in *.
        eapply IHp in H0; eauto; cleanup; simpl in *.
        eapply IHp in H0; eauto; cleanup; simpl in *.
        eapply H in H2; eauto; cleanup; simpl in *.
    Qed.

    

    Theorem RS_strong_bisimulation:
      StrongBisimulation prog_LTS prog2_LTS RP RS.
    Proof.
      unfold RP, RS; constructor; intros.
      cleanup; simpl in *.
      unfold Prog.get_user, get_user,
        Prog.get_oracle, get_oracle,
        Prog.get_disk, get_disk,
        Prog.get_store, get_store in *; simpl in *; cleanup.
      unfold state, state2 in *; destruct_pairs; simpl in *.
      split; intros.

      - inversion H; sigT_eq.
        eapply_fresh exec_preserves_rep in H5; cleanup; simpl in *; eauto.
        eapply_fresh exec_preserves_user in H5; simpl in *; cleanup.
        destruct s1'; simpl in *; destruct_pairs; cleanup.
        unfold Prog.get_user, Prog.get_disk in *; simpl in *; cleanup.
        eexists; intuition.
        econstructor; eauto.
        all: simpl; eauto.

        unfold Prog.get_user, Prog.get_disk in *; simpl in *; cleanup.
        eexists; intuition.
        eapply Exec2Crashed; simpl; eauto.
        all: simpl; eauto.

      - inversion H; sigT_eq.
        simpl in *; eexists; intuition.
    Abort.
     *)

    Theorem transfer_low_to_high_self :
  forall T (p: prog2 T),
   ->
  StrongBisimulation prog_LTS prog2_LTS RP RS ->
  (forall T, right_total (@RP T)) ->
  right_total_filtered RS (fun d2 => exists d1, rep (get_disk d2) d1) ->
  (forall u, simulation_preserving (Prog.state_equivalent_for u) (state_equivalent_for u) RS) ->
  data_noninterference p (fun d2 => exists d1, rep (get_disk d2) d1).
Proof.

  Theorem transfer_low_to_high_self :
  forall T (p: prog2 T),
  Prog.data_noninterference (prog2_to_prog p) (fun d1 => exists d2, rep d2 (Prog.get_disk d1)) ->
  StrongBisimulation prog_LTS prog2_LTS RP RS ->
  (forall T, right_total (@RP T)) ->
  right_total_filtered RS (fun d2 => exists d1, rep (get_disk d2) d1) ->
  (forall u, simulation_preserving (Prog.state_equivalent_for u) (state_equivalent_for u) RS) ->
  data_noninterference p (fun d2 => exists d1, rep (get_disk d2) d1).
Proof.
  unfold right_total, right_total_filtered, simulation_preserving, result_same; intros.
  destruct H, H0.
  rename H1 into right_total_op.
  rename H2 into right_total_state.
  rename H3 into simulation_preserving.

  unfold data_noninterference; split.
  - unfold state_noninterference; intros.
    edestruct (right_total_state st1), (right_total_state st2); eauto.
    edestruct (right_total_op T p).
    eapply_fresh strong_bisimulation_correct0 in H5; eauto; cleanup; simpl in *.
    apply H9 in H2; cleanup; clear H8 H9.

    inversion H2; sigT_eq.
    unfold Prog.state_noninterference, Prog.ret_noninterference in *.
    unfold RP in *; cleanup.
    eapply_fresh H in H15; eauto; cleanup.
    eapply_fresh strong_bisimulation_correct0 in H6; eauto; cleanup; simpl in *.
    edestruct H9; [econstructor; eauto|]; cleanup.
    eexists; intuition eauto.
    
    unfold return_state_equivalent_for.
    unfold result_same in *; cleanup; intuition eauto;
    simpl in *;
    unfold state_equivalent_for, Prog.state_equivalent_for in *; cleanup;
    unfold RS in *; simpl in *;
    unfold state, state2 in *; destruct_pairs; simpl in *; cleanup;
    unfold Prog.get_user, get_user,
    Prog.get_oracle, get_oracle,
    Prog.get_disk, get_disk in *; simpl in *; cleanup;
    intuition eauto; eapply rep_equivalent_for; eauto.

    unfold RS in H5; cleanup; eauto.
    eapply simulation_preserving; eauto.

  -  unfold ret_noninterference; intros.
     edestruct (right_total_state st1), (right_total_state st2); eauto.
     edestruct (right_total_op T p).
     eapply_fresh strong_bisimulation_correct0 in H5; eauto; cleanup; simpl in *.
     apply H9 in H2; cleanup; clear H8 H9.
     
     inversion H2; sigT_eq.
     unfold RP in *; cleanup.
     unfold Prog.state_noninterference, Prog.ret_noninterference in *.
     eapply_fresh H4 in H15; eauto; cleanup.
     eapply_fresh strong_bisimulation_correct0 in H6; eauto; cleanup; simpl in *.     
     edestruct H9; [econstructor; eauto|]; cleanup.
     eexists; intuition eauto.
     
     unfold return_equivalent_for.
     unfold result_same in *; cleanup; intuition eauto;
       simpl in *;
       unfold state_equivalent_for, Prog.state_equivalent_for in *; cleanup;
         unfold RS in *; simpl in *;
           unfold state, state2 in *; destruct_pairs; simpl in *; cleanup;
             unfold Prog.get_user, get_user,
             Prog.get_oracle, get_oracle,
             Prog.get_disk, get_disk in *; simpl in *; cleanup;
               intuition eauto; try eapply rep_equivalent_for; eauto.
     
     cleanup; eauto.
     unfold RS in H5; simpl in *; cleanup; eauto.
     pose proof H5 as Hx; unfold RS in H5; simpl in *; cleanup; eauto.
     eapply simulation_preserving; eauto.
Qed.

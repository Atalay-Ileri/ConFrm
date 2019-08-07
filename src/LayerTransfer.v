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

  Definition refines_to (s1 s2: state) :=
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
    unfold state in *; destruct_pairs; simpl in *.

  Definition refines_to_same st1 st2 := exists sr, refines_to st1 sr /\ refines_to st2 sr.


  Lemma exec_preserves_user:
      forall T (p: prog T) st1 st1' tr,
        exec st1 p st1' tr ->
        Prog.get_user st1 = Prog.get_user (extract_state st1').
    Proof.
      induction 1; simpl in *; eauto.
      cleanup; eauto.
    Qed.

    Lemma exec_limited_preserves_user:
      forall T (p: prog_limited T) st1 st1',
        exec_limited st1 p st1' ->
        Prog.get_user st1 = Prog.get_user (extract_state st1').
    Proof.
      induction 1; simpl in *; eauto.
      eapply exec_preserves_user; eauto.
    Qed.

    Lemma rep_equivalent_for_fst_low:
      forall u d1 d2 d1' d2',
        @equivalent_for_fst _ addr_dec _ u d1 d1' ->
        rep d2 d1 ->
        rep d2' d1' ->
        @equivalent_for_fst _ addr_dec _ u d2 d2'.
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

    
    Lemma exec_limited_preserves_rep:
      forall T (p: prog_limited T)  st1 d1 st1',
        exec_limited st1 p st1' ->
        rep d1 (Prog.get_disk st1) ->
        exists d1', rep d1' (Prog.get_disk (extract_state st1')).
    Proof.
      induction p; intros; cleanup; simpl in *; eauto;
        unfold Prog.get_disk, state in *; destruct_pairs; simpl in *;
      try (inversion H; sigT_eq); simpl in *.
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

      - inversion H0; sigT_eq; simpl in *.
        invert_exec.
        edestruct IHp; eauto; cleanup; simpl in *.
        econstructor; eauto.
        simpl; eauto.
        simpl in *.

        edestruct H; eauto; cleanup; simpl in *.
        econstructor; eauto.
        simpl; eauto.
        
        destruct H6; cleanup; simpl in *.
        edestruct IHp; eauto; cleanup; simpl in *.
        econstructor; eauto.
        simpl; eauto.
        simpl; eauto.

        edestruct IHp; eauto; cleanup; simpl in *.
        econstructor; eauto.
        simpl; eauto.
        simpl in *.

        edestruct H; eauto; cleanup; simpl in *.
        econstructor; eauto.
        simpl; eauto.
    Qed.

    

  Definition prog_eq T (p1: Op prog_limited_LTS T) (p2: Op prog2_LTS T) := p1 = p2.

  Definition refines_to_something st1 := exists st2, refines_to st1 st2.
  Definition something_refines_to st2 := exists st1, refines_to st1 st2.

  Lemma exec_limited_preserves_refines_to_something:
      forall T (p: prog_limited T)  st1 st1',
        exec_limited st1 p st1' ->
        refines_to_something st1 ->
        refines_to_something (extract_state st1').
  Proof.
    unfold refines_to_something; intros.
    simpl_refines_to; simpl_states; cleanup.
    eapply exec_limited_preserves_rep in H; eauto; cleanup.
    unfold get_disk in *.
    simpl_states; cleanup.
    exists(fst (fst (fst (extract_state st1'))), snd (fst (fst (extract_state st1'))), x, snd (extract_state st1'));
      intuition eauto.
  Qed.

  Lemma return_state_equivalent_for_refines_to:
    forall T u (x y a b: @Result state T),
      refines_to (extract_state x) (extract_state y) ->
      result_same x y ->
      result_same a b ->
      return_state_equivalent_for u x a ->
      refines_to (extract_state a) (extract_state b) ->
      return_state_equivalent_for u y b.
  Proof.
    unfold return_state_equivalent_for, result_same, state_equivalent_for; intros.
    simpl_refines_to; simpl_states; cleanup; intuition.
    simpl_states; cleanup.
    intuition.
    eapply rep_equivalent_for_fst_low; eauto.
    simpl_states; cleanup.
    intuition.
    eapply rep_equivalent_for_fst_low; eauto.
  Qed.

  Lemma return_equivalent_for_refines_to:
    forall T u (x y a b: @Result state T),
      refines_to (extract_state x) (extract_state y) ->
      result_same x y ->
      result_same a b ->
      (forall def : T, extract_ret def x = extract_ret def y) ->
      (forall def : T, extract_ret def a = extract_ret def b) ->
      return_equivalent_for u x a ->
      refines_to (extract_state a) (extract_state b) ->
      return_equivalent_for u y b.
  Proof.
    unfold return_equivalent_for, result_same, state_equivalent_for; intros.
    simpl_refines_to; simpl_states; cleanup; intuition.
    simpl_states; cleanup.
    intuition.
    eapply rep_equivalent_for_fst_low; eauto.
    simpl_states; intuition; cleanup; eauto.
    simpl_states; cleanup; intuition.   
    eapply rep_equivalent_for_fst_low; eauto.
  Qed.

(*
  Theorem transfer_low_to_high_self :
  forall T (p: prog_limited T) valid_l valid_h refines_to,
  data_noninterference p valid_l ->
  StrongBisimulation prog_limited_LTS prog2_LTS prog_eq refines_to ->
  (forall u, simulation_preserving (Prog.state_equivalent_for u) (state_equivalent_for u) refines_to) ->
  data_noninterference p valid_h.
Proof.
  unfold something_refines_to, refines_to_something, simulation_preserving, result_same, prog_eq; intros.
  destruct H, H0.
  rename H1 into simulation_preserving.

  unfold data_noninterference; split.
  - unfold state_noninterference; intros.
    destruct 
    eapply_fresh strong_bisimulation_correct in H3; eauto; cleanup; simpl in *.

    eapply_fresh H in H3 cleanup.
    simpl_refines_to; simpl_states; cleanup; eauto.
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


*)


Definition simulation_preserving_right_to_left {T1 T2: Type} (S1: T1 -> T1 -> Prop) (S2: T2 -> T2 -> Prop)(R: T1 -> T2 -> Prop) :=
  forall t1 t1' t2 t2',
    R t1 t2 ->
    R t1' t2' ->
    S2 t2 t2' -> S1 t1 t1'.

Lemma test:
  (forall u, SelfSimulation prog_limited_LTS (Prog.state_equivalent_for u)) ->
  SelfSimulation prog_limited_LTS refines_to_same.
Proof.
  intros; constructor; intros; simpl in *.
  eapply_fresh H in H0.
  simpl in *; eauto; cleanup.
  eexists; intuition eauto.
Abort.
  

  Theorem transfer_low_to_high_self :
  forall T (p: prog_limited T),
  ProgLimited.data_noninterference p refines_to_something ->
  StrongBisimulation prog_limited_LTS prog2_LTS prog_eq refines_to ->
  (forall u, simulation_preserving_right_to_left (Prog.state_equivalent_for u) (state_equivalent_for u) refines_to) ->
  data_noninterference p something_refines_to.
Proof.
  unfold something_refines_to, refines_to_something, simulation_preserving_right_to_left, result_same, prog_eq; intros.
  destruct H, H0.
  rename H1 into simulation_preserving.

  unfold data_noninterference; split.
  - unfold state_noninterference; intros; cleanup.
    eapply_fresh strong_bisimulation_correct in H3; eauto; cleanup; simpl in *.

    edestruct H.
    eexists; apply H0.
    eexists; apply H1.
    eauto.

    (* eq_h -> eq_l required here *)
    eapply simulation_preserving; eauto.
    cleanup.

    (* exec_limited preserves refines_to_something required in here *)
    eapply_fresh exec_limited_preserves_refines_to_something in H9; unfold refines_to_something in *;
      eauto; cleanup.
    eapply_fresh exec_limited_preserves_user in H9; unfold get_user in *; simpl in *; cleanup.
                                                                                  
    destruct x2.
    + simpl_states; cleanup; eauto.
      eexists; split.
      simpl_refines_to; cleanup.
      econstructor; eauto.
      simpl_refines_to; cleanup.
      eapply return_state_equivalent_for_refines_to; eauto;
        simpl_refines_to; intuition eauto.
      
    + simpl_states; cleanup; eauto.
      eexists; split.
      simpl_refines_to; cleanup.
      eapply Exec2Crashed; eauto.
      simpl_refines_to; cleanup.
      eapply return_state_equivalent_for_refines_to; eauto;
        simpl_refines_to; intuition eauto.

  - unfold ret_noninterference; intros; cleanup.
    eapply_fresh strong_bisimulation_correct in H3; eauto; cleanup; simpl in *.

    edestruct H2.
    eexists; apply H0.
    eexists; apply H1.
    eauto.
    
    (* eq_h -> eq_l required here *)
    eapply simulation_preserving; eauto.
    simpl_refines_to; cleanup; eauto.
    cleanup.

    (* exec_limited preserves refines_to_something required in here *)
    eapply_fresh exec_limited_preserves_refines_to_something in H9; unfold refines_to_something in *;
      eauto; cleanup.
    eapply_fresh exec_limited_preserves_user in H9; unfold get_user in *; simpl in *; cleanup.
                                                                                  
    destruct x2.
    + simpl_states; cleanup; eauto.
      eexists; split.
      simpl_refines_to; cleanup.
      econstructor; eauto.
      eapply return_equivalent_for_refines_to.
      6: simpl_refines_to; cleanup; eauto.
      all: simpl; eauto.
      simpl_refines_to; cleanup; intuition eauto.
      
    + simpl_states; cleanup; eauto.
      eexists; split.
      simpl_refines_to; cleanup.
      eapply Exec2Crashed; eauto.
      eapply return_equivalent_for_refines_to.
      6: simpl_refines_to; cleanup; eauto.
      all: simpl; eauto.
      simpl_refines_to; cleanup; intuition eauto.
Qed.  


Lemma exec_limited_preserves_refinement:
      forall T (p: prog_limited T)  st1 st2 st1',
        exec_limited st1 p st1' ->
        refines_to_same st1 st2 ->
        exists st2',
          exec_limited st2 p st2' /\
          result_same st1' st2' /\
          refines_to_same (extract_state st1') (extract_state st2') /\
          (forall def : T, extract_ret def st1' = extract_ret def st2').
  Proof.
    unfold refines_to_same; induction p; simpl in *;
        intros; cleanup.
    
    - inversion H; sigT_eq; clear H;
          simpl_states.
      edestruct alloc_ok; eauto.
      apply pimpl_star_emp; eauto.
      simpl_refines_to; cleanup; eauto.

      destruct H; cleanup; destruct_lifts.
      + destruct H7; cleanup.
        simpl_refines_to; cleanup.
      (* needs complete correctness *)
  Admitted.

  Lemma rep_trans:
    forall a b c,
      rep a b ->
      rep c b ->
      rep c =p=> rep a.
  Proof.
    unfold rep; intros.
    destruct_lift H.
    destruct_lift H0.
    norm. cancel.
    intuition eauto.
  Admitted.

  Theorem RS_strong_bisimulation:
      StrongBisimulation prog_limited_LTS prog2_LTS prog_eq refines_to.
    Proof.
      unfold prog_eq; constructor; intros.
      cleanup; simpl in *.
      split; intros.

      - eapply_fresh exec_limited_preserves_rep in H; cleanup; simpl in *; eauto.
        eapply_fresh exec_limited_preserves_user in H; simpl in *; cleanup.
        destruct s1'; simpl_refines_to; simpl_states; cleanup.
        eexists; intuition.
        econstructor; eauto.
        all: simpl; eauto.
        
        eexists; intuition.
        eapply Exec2Crashed; simpl; eauto.
        all: simpl; eauto.

        simpl_refines_to; cleanup; eauto.
        
      - inversion H; sigT_eq; clear H.
        simpl_refines_to; simpl_states; cleanup.
        eapply exec_limited_preserves_refinement in H3; unfold refines_to_same in *;
        simpl in *; cleanup.
        2: {
          exists(u,o,dh,s); split.
          simpl_refines_to; intuition.
          instantiate (1:= (u, o, x1, s)).
          simpl_refines_to; intuition eauto.
        }
        
        simpl_refines_to; cleanup; intuition.
        eexists; intuition.
        eauto.
        all: simpl in *; eauto.
        eapply rep_trans; eauto.

        eapply exec_limited_preserves_refinement in H3; unfold refines_to_same in *;
          simpl in *; cleanup.
         2: {
          exists(u,o,dh,s); split.
          simpl_refines_to; intuition.
          eauto.
        }
        simpl_refines_to; cleanup; intuition.
        eexists; intuition.
        eauto.
        all: simpl in *; eauto.
        eapply rep_trans; eauto.
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


    
    

   



    
  
  
  

    
    
    
                                     (*
    Lemma rep_equivalent_for_fst_high:
      forall u d1 d2 d1' d2',
        @equivalent_for_fst _ addr_dec _ u d2 d2' ->
        rep d2 d1 ->
        rep d2' d1' ->
        @equivalent_for_fst _ addr_dec _ u d1 d1'.
    Proof.
      unfold equivalent_for, equivalent_for_fst, rep; intros.
      destruct_lift H0; destruct_lift H1; cleanup.

      assert_fresh (dummy = dummy1).
      {
        setoid_rewrite <- value_to_nat_to_value.
      
        destruct (value_to_nat dummy1);
          destruct (value_to_nat dummy); intuition; cleanup.
        destruct n; intuition; cleanup.
        specialize (H 1) as Hx; intuition; cleanup.
        destruct n; intuition; cleanup.
        specialize (H 2) as Hx; intuition; cleanup.
        destruct n; intuition; cleanup.
        specialize (H 1) as Hx; intuition; cleanup.

        destruct n; intuition; cleanup.
        specialize (H 1) as Hx; intuition; cleanup.
        destruct n; intuition; cleanup.
        specialize (H 2) as Hx; intuition; cleanup.
        destruct n; intuition; cleanup.
        specialize (H 1) as Hx; intuition; cleanup.

        destruct n; intuition; cleanup.
        destruct n0; intuition; cleanup.
        destruct n0; intuition; cleanup.
        specialize (H 1) as Hx; intuition; cleanup.
        destruct n0; intuition; cleanup.
        specialize (H 2) as Hx; intuition; cleanup.
        
        destruct n; intuition; cleanup.
        destruct n0; intuition; cleanup.
        specialize (H 1) as Hx; intuition; cleanup.
        destruct n0; intuition; cleanup.
        destruct n0; intuition; cleanup.
        specialize (H 1) as Hx; intuition; cleanup.

        destruct n; intuition; cleanup.
        destruct n0; intuition; cleanup.
        specialize (H 2) as Hx; intuition; cleanup.
        destruct n0; intuition; cleanup.
        specialize (H 1) as Hx; intuition; cleanup.
      }

      cleanup.
      
      destruct (Compare_dec.le_lt_dec a 2); [|intuition].
      destruct a; intuition.
      { (* a = 0 *)
        setoid_rewrite ptsto_valid at 3; [| pred_apply; cancel]; cleanup.     
        setoid_rewrite ptsto_valid at 5; [| pred_apply; cancel]; cleanup.
        right; do 2 eexists; intuition eauto.
      }
      
      destruct a; intuition.
      setoid_rewrite ptsto_valid at 3; [| pred_apply; cancel]; cleanup.     
      setoid_rewrite ptsto_valid at 5; [| pred_apply; cancel]; cleanup.
      right; do 2 eexists; intuition eauto.
      simpl in *.
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

*)
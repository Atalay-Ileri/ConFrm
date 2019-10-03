Require Import Primitives Layer1 BlockAllocator.
Require Import Layer2 SimulationLayer.
Require Import FunctionalExtensionality Omega.

Section Layer1to2Refinement.
  
  Fixpoint compile {T} (p2: Layer2.prog T) : Layer1.prog T :=
    match p2 with
    | Read a => read a
    | Write a v => write a v
    | Alloc v => alloc v
    | Free a => free a
    | Ret v => Layer1.Ret v
    | Bind px py => Layer1.Bind (compile px) (fun x => compile (py x))
    end.

  
  Fixpoint oracle_refines_to T (d1: Layer1.state) (p: Layer2.prog T)  (o1: Layer1.oracle) (o2: Layer2.oracle) : Prop :=
    match p with
    | Alloc v =>
      if (in_dec Layer1.token_dec Layer1.Crash o1) then
        o2 = {| token_list := [Crash]; refinement_length := length o1 |}
      else
        let sv := Disk.read d1 0 in
        match sv with
        | Some v =>
          let bits := bits (value_to_bits v) in
          let index := get_first_zero bits in
          
          if lt_dec index block_size then
            o2 = {| token_list := [BlockNum index]; refinement_length := length o1 |}
          else
            o2 = {| token_list := [DiskFull]; refinement_length := length o1 |}
        | None => False
        end
    | @Bind T1 T2 p1 p2 =>

      exists d1',
      (Layer1.exec o1 d1 (compile p1) (Crashed d1') /\
         oracle_refines_to T1 d1 p1 o1 o2) \/
      (exists r o1' o1'' o2' o2'' ret,
         o1 = o1'++o1'' /\
         Layer1.exec o1' d1 (compile p1) (Finished d1' r) /\
         Layer1.exec o1'' d1' (compile (p2 r)) ret /\
         oracle_refines_to T1 d1 p1 o1' o2' /\
         oracle_refines_to T2 d1' (p2 r) o1'' o2'' /\
         o2 = {| token_list:= token_list o2'++ token_list o2'';
                 refinement_length := refinement_length o2' + refinement_length o2'' |})
    | _ =>
      if (in_dec Layer1.token_dec Layer1.Crash o1) then
        o2 = {| token_list := [Crash]; refinement_length := length o1 |}
      else
        o2 = {| token_list := [Cont]; refinement_length := length o1 |}
    end.

  Definition refines_to d1 d2 :=
    exists F, (F * rep d2)%pred d1.

  Definition compilation_of T p1 p2 :=
    p1 = @compile T p2.

  Definition low := Build_LTS (list Layer1.token) Layer1.state Layer1.prog Layer1.exec.

  Definition high := Build_LTS Layer2.oracle Layer2.state Layer2.prog Layer2.exec.

  Lemma star_split:
    forall (AT : Type) (AEQ : EqDec AT) (V : Type)
      (p q : @pred AT AEQ V) (m : @mem AT AEQ V),
      (p * q)%pred m ->
      exists m1 m2, mem_disjoint m1 m2 /\ p m1 /\ q m2 /\ mem_union m1 m2 = m.
  Proof.
    intros; unfold sep_star in *; rewrite sep_star_is in *;
      destruct H; cleanup; eauto.
    do 2 eexists; intuition eauto.
  Qed.
  
  Lemma rep_eq:
    forall d s1 s2 F F',
      (F * rep s1)%pred d ->
      (F' * rep s2)%pred d ->
      s1 = s2.
  Proof.
    intros.
    extensionality k.
    unfold rep in *; simpl in *.
    
    destruct_lift H; destruct_lift H0.
    eapply_fresh ptsto_valid' in H.
    eapply_fresh ptsto_valid in H5; cleanup.
    eapply mem_union_addr in Hx; eauto.
    eapply mem_union_addr in Hx0; eauto.
    all: try solve [apply mem_disjoint_comm; eauto].
    rewrite mem_union_comm in Hx, Hx0; eauto.
    all: try solve [apply mem_disjoint_comm; eauto].
    unfold set in *; simpl in *.
    rewrite H3 in Hx; cleanup.
                             
    destruct_fresh (nth k (bits (value_to_bits dummy)) 0).
    rewrite H9, H11; eauto.
    
    destruct (value_to_bits dummy); simpl in *.
    unfold valid_bitlist in *; cleanup.
    destruct (nth_in_or_default k bits 0); [|cleanup; omega].
    apply H7 in i; cleanup.
    destruct n; cleanup; try omega.
    specialize (H8 _ D).
    specialize (H10 _ D); cleanup; eauto.
    eapply mem_union_addr in H8; eauto.
    eapply mem_union_addr in H10; eauto.
    all: try solve [apply mem_disjoint_comm; eauto].
    rewrite mem_union_comm in H8, H10; eauto.
    all: try solve [apply mem_disjoint_comm; eauto].
    unfold set in *; simpl in *.
    rewrite H3 in H8; cleanup; eauto.    
  Qed.      

  (*
  Lemma oracle_refinement_deterministic:
    forall T p2 ol1 ol2 oh sl1 sl2 p1 sl1' sl2', (* sh1 sh2 sh1' sh2' ,
      refines_to sl1 sh1 ->
      refines_to sl2 sh2 ->
      *)
      compilation_of T p1 p2 ->
      Layer1.exec ol1 sl1 p1 sl1' ->
      Layer1.exec ol2 sl2 p1 sl2' ->
      result_same sl1' sl2' ->
      (forall def, extract_ret def sl1' = extract_ret def sl2') ->
      (*
      Layer2.exec oh sh1 p2 sh1' ->
      Layer2.exec oh sh2 p2 sh2' ->
      result_same sl1' sh1' ->
      result_same sl2' sh2' ->
      result_same sh1' sh2' ->
                                *)
      oracle_refines_to T sl1 p2 ol1 oh ->
      oracle_refines_to T sl2 p2 ol2 oh ->
      ol1 = ol2.
  Proof.
    unfold compilation_of; induction p2; simpl; intros.
    - (* Read *)
      cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a0, t; try tauto.
        erewrite H1; eauto.
    - (* Write *)
        cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a0, t; try tauto.
        erewrite H1; eauto.
    - (* Alloc *)
      destruct (in_dec token_dec Layer1.Crash ol1), (in_dec token_dec Layer1.Crash ol2);
        try solve [cleanup; tauto].
      cleanup.
      + (* Crashed *)
        admit.
      + destruct H4, H5.
        clear H0 H1 H6 H7; cleanup.
        clear H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a, t; try tauto.
        erewrite H1; eauto.
    - (* Free *)
      cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a0, t; try tauto.
        erewrite H1; eauto.
    - (* Ret *)
      cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a, t0; try tauto.
        erewrite H1; eauto.
    - (* Bind *)
      cleanup.
      invert_exec; invert_exec; try tauto.
      + (* Both Finished *)
        specialize (H8 x1).
        specialize (H7 x5).
        cleanup.
        edestruct H10; eauto; cleanup.
        edestruct H11; eauto; cleanup.
        specialize IHp2 with (2:= H0)(3:=H2); simpl in *.
        edestruct IHp2; eauto.
        specialize H with (2:= H1)(3:=H9); simpl in *.
        
      destruct oh; simpl in *.
        cleanup; try tauto.
        unfold refines_to in *; cleanup.
        eapply read_ok in H; cleanup.
        split_ors; destruct_lifts; cleanup.
        edestruct H4.
        
        split_ors; cleanup.
        
        edestruct read_ok.
        pred_apply' H; cancel.
        eassign
   *)

  Axiom finished_crash_not_in :
    forall T o s (p: Layer1.prog T) s' r,
      Layer1.exec o s p (Finished s' r) ->
      ~ In Layer1.Crash o.

  Axiom crashed_crash_in :
    forall T o s (p: Layer1.prog T) s',
      Layer1.exec o s p (Crashed s') ->
      In Layer1.Crash o.

  Axiom layer1_exec_deterministic :
    forall T o s (p: Layer1.prog T) s' s'',
      Layer1.exec o s p s' ->
      Layer1.exec o s p s'' ->
      s' = s''.

  Lemma exec_low_to_high_oracle:
    forall T p2 p1 ol sl sl',
      Layer1.exec ol sl p1 sl' ->
      (forall d, sl' <> Failed d) ->
      compilation_of T p1 p2 ->
      exists oh, oracle_refines_to T sl p2 ol oh.
  Proof.
    unfold compilation_of;
      induction p2; simpl; intros; cleanup;
      try solve [ exists (match sl' with
         | Crashed _ => {| token_list:= [Crash]; refinement_length := length ol |}
         | Finished _ _ => {| token_list:= [Cont]; refinement_length := length ol |}
         | Failed _ => {| token_list:= []; refinement_length := length ol |}
         end); intros;
        destruct sl'; simpl in *; [
      eapply finished_crash_not_in in H;
        destruct (in_dec token_dec Layer1.Crash ol); intuition tauto |
      eapply crashed_crash_in in H;
      destruct (in_dec token_dec Layer1.Crash ol); intuition tauto |
      exfalso; eapply H0; eauto] ].

    - (* Alloc *)
      exists (match sl' with
         | Crashed _ => {| token_list:= [Crash]; refinement_length := length ol |}
         | Finished _ r =>
           match r with
           | Some a => {| token_list:= [BlockNum a]; refinement_length := length ol |}
           | None => {| token_list:= [DiskFull]; refinement_length := length ol |}
           end
         | Failed _ => {| token_list:= []; refinement_length := length ol |}
         end); intros.
      destruct sl'; simpl in *.
      eapply finished_crash_not_in in H;
        destruct (in_dec token_dec Layer1.Crash ol); try intuition tauto.
      (* XXX: We need to know about the behavior of alloc here *)
      admit.
      eapply crashed_crash_in in H;
        destruct (in_dec token_dec Layer1.Crash ol); intuition tauto.
      exfalso; eapply H0; eauto.
      
    - (* Bind *)
      invert_exec; cleanup.      
      + (* Finished *)
        edestruct IHp2; eauto.
        intros d Hx; inversion Hx.
        edestruct H; eauto.
        exists ({| token_list:= token_list x3 ++ token_list x4; refinement_length := refinement_length x3 + refinement_length x4 |}), x1.
        right; intros.
        do 6 eexists; intuition eauto.
      + (* Crashed *)
        split_ors; cleanup.
        * edestruct IHp2; eauto.
          intros d Hx; inversion Hx.
        * edestruct IHp2; eauto.
          intros d Hx; inversion Hx.
          edestruct H; eauto.
          do 2 eexists; right; intros.
          do 6 eexists; intuition eauto.
      + (* Failed *)
        exfalso; eapply H1; eauto.
  Abort.

(*
  Lemma exec_high_to_low_oracle:
    forall T p2 oh sl sh sh',
      refines_to sl sh ->
      Layer2.exec oh sh p2 sh' ->
      exists ol, oracle_refines_to T sl p2 ol oh.
  Proof.
    induction p2; simpl; intros.
    - (* Read *)
      inversion H0; cleanup.
      eexists; intros.
      
      + (* Finished *)
        unfold refines_to in *; cleanup.
        eapply read_ok in H; cleanup.
        split_ors; destruct_lifts; cleanup.
        edestruct H4.
        
        split_ors; cleanup.
        
        edestruct read_ok.
        pred_apply' H; cancel.
      
Abort.
*)

  (* XXX: We need oracle lengths to extract oracle equalities *) 
  Axiom layer1_exec_finished_then_oracle_length_eq :
    forall T (p: Layer1.prog T) s o1 o2 s'1 s'2 r1 r2,
      Layer1.exec o1 s p (Finished s'1 r1) ->
      Layer1.exec o2 s p (Finished s'2 r2) ->
      length o1 = length o2.

  Lemma app_split_length_eq :
    forall T (l1 l2 l1' l2': list T),
      l1++l2 = l1'++l2' ->
      length l1 = length l1' ->
      l1 = l1' /\ l2 = l2'.
  Proof.
    induction l1; simpl; intros.
    symmetry in H0.
    apply length_zero_iff_nil in H0; cleanup.
    simpl; eauto.

    destruct l1'; simpl in *.
    inversion H0.
    cleanup.
    edestruct IHl1; eauto; cleanup; eauto.
  Qed.
    
  Theorem sbs :
    forall valid_h,
      StrongBisimulation
        low high
        (refines_to_valid refines_to valid_h)
        (compiles_to_valid (fun _ _ => True) compilation_of)
        valid_h
        (fun _ _ => True)
        compilation_of refines_to
        oracle_refines_to.              
  Proof.
    constructor.
    intros T p1 p2.
    generalize dependent p1.
    induction p2; intros.
    { (* Read *)
      unfold refines_to_valid, refines_to,
      compiles_to_valid, compilation_of, oracle_refines_to in *; intros.
      simpl in *;
      split.
      + (* Low to High *)
        intros; cleanup.
        * (* Crashed *)
          rewrite H4 in *.
          eapply_fresh (read_ok a) in H3; cleanup.
          eapply_fresh layer1_exec_deterministic in H6; eauto; cleanup.        
          split_ors; cleanup.
          --
            destruct_lifts.
            tauto.
          --
            destruct_lifts.
            eexists; split.
            eapply ExecOpCrash; eauto.
            intros T p1 p2 Hx; inversion Hx.
            simpl in *.
            repeat split; eauto.
            intuition (cleanup; eauto).
            eapply_fresh rep_eq in H0; eauto; cleanup; eauto.
        * (* Finished *)
          rewrite H4 in *.
          eapply_fresh (read_ok a) in H3; cleanup.
          eapply_fresh layer1_exec_deterministic in H6; eauto; cleanup.        
          split_ors; cleanup.
          --
            destruct_lifts.
            eexists; split.
            econstructor; eauto.
            simpl in *.
            repeat split; eauto.
            
            intuition (cleanup; eauto).
            apply star_split in H0; cleanup.
            unfold rep in *.
            destruct_lift H7.          
            erewrite H11; eauto; simpl.
            apply nth_overflow; simpl.
            destruct (value_to_bits dummy); simpl.
            unfold valid_bitlist in *; cleanup; eauto.
            
            intros; cleanup.
            eapply_fresh rep_eq in H0; eauto; cleanup; eauto.
          --
            destruct_lifts.
            exfalso; eauto.

      + (*High to low*)
        intros; cleanup.
        * (* Crashed *)
        eapply (read_ok a) in H3; cleanup.
        split_ors; cleanup.
        --
          destruct_lifts.
          exfalso; eauto.
        --
          destruct_lifts.
          inversion H6; sigT_eq; simpl in *; cleanup.
          eexists; split.
          eauto.
          simpl in *.
          repeat split; eauto.
          intuition (cleanup; eauto).
          eapply_fresh rep_eq in H2; eauto;
            cleanup; eauto.
          
        * (* Finished *)
          eapply (read_ok a) in H3; cleanup.
          split_ors; cleanup.
          --
            destruct_lifts.
            inversion H6; sigT_eq; simpl in *; cleanup.
            eexists; split.
            eauto.
            simpl in *.
            repeat split; eauto.

            intuition (cleanup; eauto).
            apply star_split in H2; cleanup.
            unfold rep in *.
            destruct_lift H7.          
            erewrite H11; eauto; simpl.
            apply nth_overflow; simpl.
            destruct (value_to_bits dummy); simpl.
            unfold valid_bitlist in *; cleanup; eauto.
          
            intros; cleanup.
            eapply_fresh rep_eq in H2; eauto;
              cleanup; eauto.
          --
            destruct_lifts.
            exfalso; eauto.
    }
    { (* Write *) 
      admit.
    }
    { (* Alloc *)
      admit.
    }
    { (* Free *)
      admit.
    }
    { (* Ret *)
      admit.
    }
    { (* Bind *)
      unfold compilation_of in *; simpl in *; cleanup.
      split; intros.
      - (* Low to High *)
        invert_exec.
        + (* Finished *)
          split_ors; cleanup.
          * (* XXX: If Finished with o, then cannot crash with o++o' *)
            admit.
          *            
            eapply_fresh layer1_exec_finished_then_oracle_length_eq in H8; eauto.
            apply app_split_length_eq in H6; eauto; cleanup.
            eapply_fresh layer1_exec_deterministic in H8; eauto; cleanup.
            eapply_fresh layer1_exec_deterministic in H9; eauto; cleanup.
          
            edestruct IHp2; eauto.
            unfold compiles_to_valid;
            eexists; split; eauto.
            edestruct H5; eauto; simpl in *; cleanup; try tauto.
            clear H5 H6.
            simpl in *.
            destruct H14; eauto; cleanup.
            
            edestruct H; try reflexivity; eauto.
            unfold compiles_to_valid;
            eexists; split; eauto.
            edestruct H5; eauto; simpl in *; cleanup; try tauto.
            clear H5 H6.
            simpl in *.
            destruct H18; eauto; cleanup.
            
            eexists; split.
            econstructor; eauto.
            
            simpl in *.
            intuition eauto.
        + (* Crashed *)
          destruct H5; cleanup.
          * (* First Crashed *)
            split_ors; cleanup.
            --
              edestruct IHp2; eauto.
              unfold compiles_to_valid;
              eexists; split; eauto.
              edestruct H8; eauto; simpl in *; cleanup; try tauto.
              clear H8 H9.
              simpl in *.
              
              eexists; split.
              eapply ExecBindCrash; eauto.
              simpl in *; intuition eauto.
            -- (* XXX: If Finished with o, then cannot crash with o++o' *)
              admit.
          * (* Second Crashed *)
             split_ors; cleanup.
             -- (* XXX: If Finished with o, then cannot crash with o++o' *)
              admit.
             --
               eapply_fresh layer1_exec_finished_then_oracle_length_eq in H8; eauto.
               apply app_split_length_eq in H6; eauto; cleanup.
               eapply_fresh layer1_exec_deterministic in H8; eauto; cleanup.
               eapply_fresh layer1_exec_deterministic in H9; eauto; cleanup.
               
               edestruct IHp2; eauto.
               unfold compiles_to_valid;
               eexists; split; eauto.
               edestruct H5; eauto; simpl in *; cleanup; try tauto.
               clear H5 H6.
               simpl in *.
               destruct H14; eauto; cleanup.
            
               edestruct H; try reflexivity; eauto.
               unfold compiles_to_valid;
               eexists; split; eauto.
               edestruct H5; eauto; simpl in *; cleanup; try tauto.
               clear H5 H6.
               simpl in *.
               
               eexists; split.
               econstructor; eauto.
               
               simpl in *.
               intuition eauto.
        + (* Failed *)
          destruct H5; cleanup.
          * (* First Failed *)
            split_ors; cleanup.
            --
              eapply layer1_exec_deterministic in H6;
              eauto; inversion H6.
            -- (* XXX: If Finished with o, then cannot crash with o++o' *)
              admit.
          * (* Second Failed *)
            split_ors; cleanup.
            -- (* XXX: If Finished with o, then cannot crash with o++o' *)
              admit.
            --
              eapply_fresh layer1_exec_finished_then_oracle_length_eq in H8; eauto.
              apply app_split_length_eq in H6; eauto; cleanup.
              eapply_fresh layer1_exec_deterministic in H8; eauto; cleanup.
              eapply_fresh layer1_exec_deterministic in H9; eauto; cleanup.

            edestruct IHp2; eauto.
            unfold compiles_to_valid;
            eexists; split; eauto.
            edestruct H5; eauto; simpl in *; cleanup; try tauto.
            clear H5 H6.
            simpl in *.
            destruct H14; eauto; cleanup.
            
            edestruct H; try reflexivity; eauto.
            unfold compiles_to_valid;
            eexists; split; eauto.
            edestruct H5; eauto; simpl in *; cleanup; try tauto.
            clear H5 H6.
            simpl in *.
            
            eexists; split.
            econstructor; eauto.
            
            simpl in *.
            intuition eauto.
            
      - (* High to Low *)
        unfold compiles_to_valid in H1; cleanup.
        inversion H5; sigT_eq; clear H5.
        + (* Finished *)
          split_ors; cleanup.
          (* XXX: HERE *)
  Admitted.

  Theorem sbs_general:
    forall valid_h valid_prog_h,
      StrongBisimulation
        low high
        (refines_to_valid refines_to valid_h)
        (compiles_to_valid valid_prog_h compilation_of)
        valid_h
        valid_prog_h
        compilation_of refines_to
        oracle_refines_to.  
  Proof.
    intros.
    eapply bisimulation_weaken_valid_prog; [|apply sbs].
    intuition.
  Qed.
    
End Layer1to2Refinement.
Require Import Framework Mem FSParameters FileDiskLayer.

Require Import File FileDiskRefinement.
Require AuthenticatedDiskLayer.
Require TransactionalDiskLayer TransactionalDiskRefinement.
Require TransactionCacheLayer.
Require LoggedDiskLayer LoggedDiskRefinement.
Require StorageLayer.
Require CryptoDiskLayer CachedDiskLayer.

Notation "'FileDiskOp'" := (FileDiskOperation inode_count). 
Notation "'FileDisk'" := (FileDiskLang inode_count) (at level 0).
Notation "'FileDisk.refinement'" := FileDiskRefinement.


Definition same_for_user_except (u: user) (exclude: option addr) (d1 d2: FileDisk.(state)) :=
  addrs_match_exactly d1 d2 /\
  (forall inum file1 file2,
     exclude <> Some inum ->
     d1 inum = Some file1 ->
     d2 inum = Some file2 ->
     (file1.(owner) = u \/
      file2.(owner) = u) ->
     file1 = file2) /\
  (forall inum file1 file2,
     d1 inum = Some file1 ->
     d2 inum = Some file2 ->
     file1.(owner) = file2.(owner) /\ 
     length file1.(blocks) = length file2.(blocks)).

(*
Theorem Invariant_for_file_disk_read:
  SelfSimulation FileDisk (fun _ => True) (fun T p => match p with
                                             | Op _ o =>
                                               match o with
                                               | Read _ _ => True
                                               |_ => False
                                               end
                                             | _ => False
                                             end) same_for_user.
Proof.
  econstructor.
  intros; destruct p; simpl in *; try tauto.  
  destruct p; try tauto; cleanup.
 
  invert_exec; cleanup.
  { (* Read Worked *)
    invert_exec; cleanup.
    { (* Read successful *)
      exists (Finished s2 (Some v)).
      simpl; intuition eauto.
      unfold same_for_user in *; cleanup.
      specialize (H1 a).
      destruct_fresh (snd s2 a); eauto; try congruence.
      specialize (H2 a file f H9 D).
      setoid_rewrite H0 in H10.        
      rewrite H2 in *; eauto.
      repeat (econstructor; eauto; simpl).
      destruct H1.
      exfalso; apply H1; eauto; setoid_rewrite H9; congruence.
    }          
    { (* Read Failed *)
      exists (Finished s2 None);        
      simpl; split; [| intuition eauto].
      econstructor; simpl.
      repeat split_ors; cleanup;
      try solve [eapply ExecReadFail; eauto].
      
      -
        destruct_fresh (snd s2 a); eauto.
        unfold same_for_user in *; cleanup.
        specialize (H2 a); destruct H2.
        exfalso; eapply H5; try congruence; eauto.
        eapply ExecReadFail; eauto.
      
      - unfold same_for_user in *; cleanup.
        specialize (H3 a).
        destruct_fresh (snd s2 a); eauto; try congruence.
        specialize (H4 a file f H0 D).
        specialize (H5 a file f H0 D); cleanup.
        eapply ExecReadFail; eauto.
        right; right; intuition eauto.
        left; intuition; cleanup; eauto.
        right; apply nth_error_None.
        rewrite <- H6; apply nth_error_None; eauto.        
        destruct H3; exfalso; eapply H3; eauto;
        setoid_rewrite H0; congruence.
    }
  }
  { (* Read Crashed *)
    exists (Crashed s2).
    intuition eauto;
    simpl; repeat invert_exec; cleanup; eauto.
    { (* Crashed Before *)
      repeat econstructor; eauto.
    }
  }
  Unshelve.
  all: eauto.
Qed.
 *)

Fixpoint horizontally_compose_valid_prog1 {O1 O2} (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2)) {T} (p1: prog L1 T) :=
         match p1 with
         | @Op _ T' p => Op (HorizontalComposition O1 O2) (P1 p)
         | @Ret _ T' t => Ret t
         | @Bind _ T1 T2 p1 p2 =>
           Bind (horizontally_compose_valid_prog1 L1 L2 LL p1)
           (fun r => horizontally_compose_valid_prog1 L1 L2 LL (p2 r))
         end.

(*
Fixpoint horizontally_compose_valid_prog2 {O1 O2} (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2)) C T (p2: prog L2 T) :=
         match p2 with
         | @Op _ T' p => (Op (HorizontalComposition O1 O2) (P2 p))
         | @Ret _ T' t => (Ret t)
         | @Bind _ T1 T2 p1 p2 =>
           horizontally_compose_valid_prog2 L1 L2 LL C T1 p1 /\
           (forall r, horizontally_compose_valid_prog2 L1 L2 LL C T2 (p2 r))
         end.
*)
(*
Lemma ss_hc_rev_p1:
  forall O1 O2 (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2))
    u R C V T l_grs1 l_grs2 (p1 p2: L1.(prog) T) rec,
    @SelfSimulation _ LL u _ (horizontally_compose_valid_prog1 L1 L2 LL p1)
    (horizontally_compose_valid_prog1 L1 L2 LL p2)
    (horizontally_compose_valid_prog1 L1 L2 LL rec) R V  C l_grs2 ->
    forall s2,
      SelfSimulation u p1 p2 rec
        (fun s1 => R (s1, s2))
        (fun s1 s1' =>  V (s1, s2) (s1', s2))
        C
        l_grs1.
Proof.
  unfold SelfSimulation;  
  induction l_grs1; intros; cleanup.
  - (* Op *)
    repeat invert_exec; simpl in *.
    + (* P1 Finished *)
      edestruct H.
      4: eauto.
      all: eauto.

      solve [repeat econstructor; eauto].
      cleanup; simpl in *.
      repeat invert_exec; simpl in *; cleanup; intuition.
      exists (Finished s3 r0); intuition eauto.
      
    + (* P1 Crashed *)
      edestruct H, self_simulation_correct.
      apply H0.
      apply H1.
      all: simpl in *; eauto.      
      solve [repeat econstructor; eauto].
      cleanup; simpl in *.
      repeat invert_exec; simpl in *; cleanup; intuition.
      exists (Crashed s3); intuition eauto.
      repeat econstructor; eauto.

  - (* Ret *)
    invert_exec; cleanup;
    eexists; simpl; intuition eauto; try solve [econstructor; eauto]; eauto.

  - (* Bind *)
    simpl in *; cleanup.
    invert_exec; cleanup.
    + (* Finished *)
      edestruct IHp.
      apply H1.
      apply H2.
      all: eauto.
      cleanup; simpl in *.
      destruct x3; simpl in *; intuition; cleanup.

      edestruct H0.
      apply H12.
      apply H13.
      all: eauto.
      cleanup; simpl in *.
      destruct x2; simpl in *; intuition; cleanup.

      exists (Finished s4 t1); simpl; intuition eauto.
      econstructor; eauto.

    + split_ors; cleanup.
      * (* p1 Crashed *)
        edestruct IHp.
        apply H1.
        apply H2.
        all: eauto.
        cleanup; simpl in *.
        destruct x1; simpl in *; intuition; cleanup.
        exists (Crashed s3); simpl; intuition eauto.
        solve [ econstructor; eauto].

      * (* p2 crashed *)
        edestruct IHp.
        apply H1.
        apply H2.
        all: eauto.
        cleanup; simpl in *.
        destruct x3; simpl in *; intuition; cleanup.

        edestruct H0.
        apply H12.
        apply H13.
        all: eauto.
        cleanup; simpl in *.
        destruct x2; simpl in *; intuition; cleanup.
        
        exists (Crashed s4); simpl; intuition eauto.
        econstructor; eauto.
Qed.
 

Lemma ss_hc_rev_p2:
  forall O1 O2 (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2))
    R C V,
    SelfSimulation LL R C V ->
    forall s1,
      SelfSimulation L2
        (fun s2 => R (s1, s2))
        (horizontally_compose_valid_prog2 L1 L2 LL C)
        (fun s2 s2' =>  V (s1, s2) (s1, s2')).
Proof.
  intros.
  constructor.
  intros T o p.
  generalize dependent s1.
  generalize dependent o.
  induction p; intros; cleanup.
  - (* Op *)
    repeat invert_exec; simpl in *.
    + (* P2 Finished *)
      edestruct H, self_simulation_correct.
      apply H0.
      apply H1.
      all: simpl in *; eauto.
      solve [repeat econstructor; eauto].
      cleanup; simpl in *.
      repeat invert_exec; simpl in *; cleanup; intuition.
      exists (Finished s3 r0); intuition eauto.
      
    + (* P2 Crashed *)
      edestruct H, self_simulation_correct.
      apply H0.
      apply H1.
      all: simpl in *; eauto.      
      solve [repeat econstructor; eauto].
      cleanup; simpl in *.
      repeat invert_exec; simpl in *; cleanup; intuition.
      exists (Crashed s3); intuition eauto.
      repeat econstructor; eauto.

  - (* Ret *)
    invert_exec; cleanup;
    eexists; simpl; intuition eauto; try solve [econstructor; eauto]; eauto.

  - (* Bind *)
    simpl in *; cleanup.
    invert_exec; cleanup.
    + (* Finished *)
      edestruct IHp.
      apply H1.
      apply H2.
      all: eauto.
      cleanup; simpl in *.
      destruct x3; simpl in *; intuition; cleanup.

      edestruct H0.
      apply H12.
      apply H13.
      all: eauto.
      cleanup; simpl in *.
      destruct x2; simpl in *; intuition; cleanup.

      exists (Finished s4 t1); simpl; intuition eauto.
      econstructor; eauto.

    + split_ors; cleanup.
      * (* p1 Crashed *)
        edestruct IHp.
        apply H1.
        apply H2.
        all: eauto.
        cleanup; simpl in *.
        destruct x1; simpl in *; intuition; cleanup.
        exists (Crashed s3); simpl; intuition eauto.
        solve [ econstructor; eauto].

      * (* p2 crashed *)
        edestruct IHp.
        apply H1.
        apply H2.
        all: eauto.
        cleanup; simpl in *.
        destruct x3; simpl in *; intuition; cleanup.

        edestruct H0.
        apply H12.
        apply H13.
        all: eauto.
        cleanup; simpl in *.
        destruct x2; simpl in *; intuition; cleanup.
        
        exists (Crashed s4); simpl; intuition eauto.
        econstructor; eauto.
Qed.

Lemma ss_hc_rev:
  forall O1 O2 (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2))
    R C V,
    SelfSimulation LL R C V ->
    (forall s2,
      SelfSimulation L1
        (fun s1 => R (s1, s2))
        (horizontally_compose_valid_prog1 L1 L2 LL C)
        (fun s1 s1' =>  V (s1, s2) (s1', s2))) /\
    (forall s1,
      SelfSimulation L2
        (fun s2 => R (s1, s2))
        (horizontally_compose_valid_prog2 L1 L2 LL C)
        (fun s2 s2' =>  V (s1, s2) (s1, s2'))).
Proof.
  intros; split; intros.
  eapply ss_hc_rev_p1; eauto.
  eapply ss_hc_rev_p2; eauto.
Qed.

Lemma ss_impl:
  forall O (L: Language O)
    R1 (R2: state L -> Prop) C1 (C2: forall T, prog L T -> Prop) V1 (V2: state L -> state L -> Prop),
    SelfSimulation L R1 C1 V1 ->
    (forall s, R1 s <-> R2 s) ->
    (forall T p, C1 T p <-> C2 T p) ->
    (forall s s', V1 s s' <-> V2 s s') ->
    SelfSimulation L R2 C2 V2.
Proof.
  intros; constructor; intros.
  edestruct H, self_simulation_correct.
  eapply H0; apply H3.
  eapply H0; apply H4.
  eapply H1; eauto.
  eauto.
  eapply H2; eauto.
  cleanup.
  eexists; intuition eauto.
  eapply H2; eauto.
  eapply H0; eauto.
  eapply H0; eauto.
Qed.

Lemma ss_hc:
  forall O1 O2 (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2))
  R1 R2 C1 C2 V1 V2,
  SelfSimulation L1 R1 C1 V1 ->
  SelfSimulation L2 R2 C2 V2 ->
  SelfSimulation LL
      (fun s => R1 (fst s) /\ R2 (snd s))
      (fix CH T p :=
         match p with
         | Op _ (@P1 _ _ T1 p0) => C1 T1 (Op _ p0)
         | Op _ (@P2 _ _ T1 p0) => C2 T1 (Op _ p0)
         | @Ret _ T0 t => True
         | @Bind _ T1 T2 p1 p2 => CH T1 p1 /\ (forall r, CH T2 (p2 r))
         end)
      (fun s s' => V1 (fst s) (fst s') /\ V2 (snd s) (snd s')).
Proof.
  intros.
  constructor.
  intros T o p.
  generalize dependent o.
  induction p; intros.
  - (* Op *)
    destruct p; simpl in *; cleanup;
    repeat invert_exec; simpl in *.
    + (* P1 Finished *)
      edestruct H, self_simulation_correct.
      apply H1.
      apply H2.
      eauto.      
      econstructor; eauto.
      eauto.
      cleanup; simpl in *.
      invert_exec; simpl in *; cleanup; intuition.
      exists (Finished (s', snd s2) r0); intuition eauto.
      repeat econstructor; eauto.
      
    + (* P1 Crashed *)
      edestruct H, self_simulation_correct.
      apply H1.
      apply H2.
      eauto.      
      solve [econstructor; eauto].
      eauto.
      cleanup; simpl in *.
      invert_exec; simpl in *; cleanup; intuition.
      exists (Crashed (s', snd s2)); intuition eauto.
      repeat econstructor; eauto.

    + (* P2 Finished *)
      edestruct H0, self_simulation_correct.
      apply H8.
      apply H7.
      eauto.      
      econstructor; eauto.
      eauto.
      cleanup; simpl in *.
      invert_exec; simpl in *; cleanup; intuition.
      exists (Finished (fst s2, s') r0); intuition eauto.
      repeat econstructor; eauto.

    + (* P2 Crashed *)
      edestruct H0, self_simulation_correct.
      apply H8.
      apply H7.
      eauto.      
      solve [econstructor; eauto].
      eauto.
      cleanup; simpl in *.
      invert_exec; simpl in *; cleanup; intuition.
      exists (Crashed (fst s2, s')); intuition eauto.
      repeat econstructor; eauto.

  - (* Ret *)
    invert_exec; cleanup;
    eexists; simpl; intuition eauto; try solve [econstructor; eauto]; eauto.

  - (* Bind *)
    invert_exec; cleanup.
    + (* Finished *)
      edestruct IHp.
      split; [apply H2 | apply H12].
      split; [apply H3 | apply H11].
      eauto.
      eauto.
      eauto.
      cleanup; simpl in *.
      destruct x3; simpl in *; intuition; cleanup.

      edestruct H1.
      split; [apply H16 | apply H19].
      split; [apply H17 | apply H18].
      eapply H10.
      eauto.
      eauto.
      cleanup; simpl in *.
      destruct x2; simpl in *; intuition; cleanup.

      exists (Finished s3 t1); simpl; intuition eauto.
      econstructor; eauto.

    + split_ors; cleanup.
      * (* p1 Crashed *)
        edestruct IHp.
        split; [apply H2 | apply H11].
        split; [apply H3 | apply H10].
        eauto.
        eauto.
        eauto.
        cleanup; simpl in *.
        destruct x1; simpl in *; intuition; cleanup.
        exists (Crashed s0); simpl; intuition eauto.
        solve [ econstructor; eauto].

      * (* p2 crashed *)
        edestruct IHp.
        split; [apply H2 | apply H11].
        split; [apply H3 | apply H10].
        eauto.
        eauto.
        eauto.
        cleanup; simpl in *.
        destruct x3; simpl in *; intuition; cleanup.
        
        edestruct H1.
        split; [apply H16 | apply H19].
        split; [apply H17 | apply H18].
        eapply H9.
        eauto.
        eauto.
        cleanup; simpl in *.
        destruct x2; simpl in *; intuition; cleanup.
        
        exists (Crashed s3); simpl; intuition eauto.
        econstructor; eauto.
Qed.
*)
(** Relation Definitions *)

(** Top Layer *)
(* File Disk *)
Definition FD_valid_state := fun (s: state FileDisk) => True.
Definition FD_related_states u ex := same_for_user_except u ex.

Theorem ss_FD_Recover:
  forall n u u' ex,
    SelfSimulation u (FileDiskOp.(Op) Recover) (FileDiskOp.(Op) Recover) (FileDiskOp.(Op) Recover)(fun _ => True) (FD_related_states u' ex) (eq u') (repeat (fun s => s) n).
Proof.
  unfold SelfSimulation; induction n; simpl; intros.
  {
    repeat invert_exec.
    simpl in *.
    invert_exec'' H9; cleanup.
    invert_exec.
    exists (RFinished s2 tt); intuition eauto.
    solve [repeat econstructor; eauto].
  }
  {
    destruct lo; simpl in *;
    repeat invert_exec.
    invert_exec'' H12; invert_exec.
    eapply IHn in H14; eauto; cleanup.
    exists (Recovered (extract_state_r x)); simpl; intuition eauto.
    repeat econstructor; eauto.
  }
Qed.

Theorem ss_FD_read:
  forall n inum off u u',
    SelfSimulation u (FileDiskOp.(Op) (Read inum off)) (FileDiskOp.(Op) (Read inum off)) (FileDiskOp.(Op) Recover) (fun _ => True) (FD_related_states u' None) (eq u') (repeat (fun s => s) n).
Proof.
  unfold SelfSimulation; intros.
  repeat invert_exec.
  {
    destruct n; simpl in *; cleanup.
    invert_exec'' H11.
    inversion H7.
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in *.
      destruct_fresh (s2 inum).
      logic_clean.
      rewrite H3 in *.
      eapply_fresh H14 in H10; eauto.
      logic_clean.
      assert_fresh (off < length (blocks f)). {
        eapply nth_error_Some.
        intros Hx.
        apply nth_error_None in Hx.
        rewrite <- H16 in Hx.
        apply nth_error_None in Hx.
        congruence.
      }
      
      apply nth_error_Some in A.
      destruct_fresh (nth_error (blocks f) off); try congruence.
      
      exists (RFinished s2 (Some v0)); simpl; intuition eauto.
      repeat econstructor; eauto.
      cleanup; eauto.
      cleanup; eauto.
      eapply H13 in H10; eauto.
      cleanup; eauto.
      congruence.
      cleanup.
      destruct (H2 inum).
      exfalso; apply H; congruence.
    }
    {
      exists (RFinished s2 None); simpl.
      split.
      repeat split_ors; subst;
      try solve [repeat econstructor; eauto].
      {
        do 3 econstructor; eauto.
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        destruct (i inum).
        exfalso; apply H1; congruence.
      }
      {
        cleanup.        
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        eapply H4 in H; eauto; try congruence; cleanup.
        do 3 econstructor; intuition eauto.
        apply nth_error_None in H6.
        rewrite H5 in H6; apply nth_error_None in H6.
        eauto.

        cleanup; eauto.
        destruct (H2 inum).
        exfalso; apply H5; congruence.
      }
      {
        cleanup.
        intuition eauto.
      }
    }
    congruence.
  }
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H10.
    invert_exec.
    edestruct ss_FD_Recover; eauto.
    cleanup.
    exists (Recovered (extract_state_r x)).
    intuition eauto.
    repeat econstructor; eauto.
  }
  Unshelve.
  all: repeat econstructor; eauto.
Qed.

Theorem ss_FD_write:
  forall n inum off v u u',
    SelfSimulation u (FileDiskOp.(Op) (Write inum off v)) 
    (FileDiskOp.(Op) (Write inum off v)) (FileDiskOp.(Op) Recover) (fun _ => True) 
    (FD_related_states u' None) (eq u') (repeat (fun s => s) n).
Proof.
  unfold SelfSimulation; intros.
  repeat invert_exec.
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H11.
    inversion H7; subst.
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in *.
      destruct_fresh (s2 inum).
      logic_clean.
      subst.
      eapply_fresh H2 in H11; eauto.
      logic_clean; subst.
      
      exists (RFinished (upd s2 inum (Build_File (owner f) (updn (blocks f) off v))) (Some tt)); simpl; intuition eauto.
      repeat econstructor; eauto.
      rewrite <- H4; eauto.
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H8; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H8; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H11; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H11; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
          repeat rewrite updn_length; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup; eauto.
      }
      {
        cleanup.
        destruct (H inum).
        exfalso; apply H3; eauto; congruence.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      repeat split_ors;
      try solve [ repeat econstructor; eauto].
      {
        do 3 econstructor; eauto.
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        destruct (i inum).
        exfalso; apply H2; congruence.
      }
      {
        cleanup.        
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        eapply H4 in H; eauto; try congruence; cleanup.
        do 3 econstructor; intuition eauto.
        cleanup; eauto.
        destruct (H2 inum).
        exfalso; apply H5; congruence.
      }
      {
        cleanup.
        intuition eauto.
      }
    }
    {(** Txn Full **)
      invert_exec; cleanup.
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      {
        
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        eapply H2 in H11; eauto; cleanup.
        do 3 econstructor; eauto.
        cleanup.
        edestruct H.
        exfalso; apply H3; eauto; congruence.
      }
    }
  }
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H10.
    invert_exec.
    {
      edestruct ss_FD_Recover; eauto.
      cleanup.
      exists (Recovered (extract_state_r x)).
      intuition eauto.
      repeat econstructor; eauto.
    }
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in H2.
      destruct_fresh (s2 inum); eauto.
      cleanup; eauto.
      eapply_fresh H2 in H10; eauto; try congruence; cleanup.
      
      edestruct ss_FD_Recover; eauto.
      instantiate (1:= upd s2 inum (Build_File (owner f) (updn (blocks f) off v))).
      instantiate (2:= u').
      instantiate (1:= None).
      {
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly.
        intuition eauto.
        {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H7; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H7; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H10; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H10; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H6; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
          repeat rewrite updn_length; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H6; eauto; try congruence.
          cleanup; eauto.
        }
      }
      }
      cleanup.
      exists (Recovered (extract_state_r x)); simpl.
      intuition eauto.
      repeat econstructor; eauto.

      cleanup.
      destruct (H inum).
      exfalso; apply H3; congruence.
    }
  }
  Unshelve.
  all: repeat econstructor; eauto.
Qed.



Theorem ss_FD_extend:
  forall n inum v u u',
    SelfSimulation u (FileDiskOp.(Op) (Extend inum v)) (FileDiskOp.(Op) (Extend inum v)) (FileDiskOp.(Op) Recover) (fun _ => True) (FD_related_states u' None) (eq u') (repeat (fun s => s) n).
Proof.
  unfold SelfSimulation; intros.
  repeat invert_exec.
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H11.
    inversion H7; subst.
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in *.
      destruct_fresh (s2 inum).
      logic_clean.
      subst.
      eapply_fresh H2 in H10; eauto.
      logic_clean; subst.
      
      exists (RFinished (upd s2 inum (Build_File (owner f) ((blocks f) ++ [v]))) (Some tt));
      simpl; intuition eauto.
      repeat econstructor; eauto.
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H8; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H8; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H10; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H10; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
          repeat rewrite app_length; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup; eauto.
      }
      {
        cleanup.
        destruct (H inum).
        exfalso; apply H3; eauto; congruence.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      repeat split_ors;
      try solve [ repeat econstructor; eauto].
      {
        do 3 econstructor; eauto.
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        destruct (i inum).
        exfalso; apply H2; congruence.
      }
      {
        cleanup.        
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        eapply H4 in H; eauto; try congruence; cleanup.
        do 3 econstructor; intuition eauto.
        cleanup; eauto.
        destruct (H2 inum).
        exfalso; apply H5; congruence.
      }
      {
        cleanup.
        intuition eauto.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in *.
      destruct_fresh (s2 inum); eauto.
      cleanup; eauto.
      eapply H2 in H10; eauto; try congruence; cleanup.      
      repeat (split; eauto).
      do 3 econstructor; eauto.

      cleanup; eauto.
      destruct (H inum).
      exfalso; apply H3; congruence.
    }
  }
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H10.
    invert_exec.
    {
      edestruct ss_FD_Recover; eauto.
      cleanup.
      exists (Recovered (extract_state_r x)).
      intuition eauto.
      repeat econstructor; eauto.
    }
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in H2.
      destruct_fresh (s2 inum); eauto.
      cleanup; eauto.
      eapply_fresh H2 in H9; eauto; try congruence; cleanup.
      
      edestruct ss_FD_Recover; eauto.
      instantiate (1:= upd s2 inum (Build_File (owner f) ((blocks f) ++ [v]))).
      instantiate (1:= None).
      instantiate (1:= u').
      {
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly.
        intuition eauto.
        {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H7; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H7; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H9; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H9; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H6; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
          repeat rewrite app_length; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H6; eauto; try congruence.
          cleanup; eauto.
        }
      }
      }
      cleanup.
      exists (Recovered (extract_state_r x)); simpl.
      intuition eauto.
      repeat econstructor; eauto.

      cleanup.
      destruct (H inum).
      exfalso; apply H3; congruence.
    }
  }
  Unshelve.
  all: repeat econstructor; eauto.
Qed.



Theorem ss_FD_change_owner:
  forall n inum u u' u'',
    SelfSimulation u (FileDiskOp.(Op) (ChangeOwner inum u'')) (FileDiskOp.(Op) (ChangeOwner inum u'')) (FileDiskOp.(Op) Recover) (fun _ => True) (FD_related_states u' (Some inum)) (eq u') (repeat (fun s => s) n).
Proof.
  unfold SelfSimulation; intros.
  repeat invert_exec.
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H11.
    inversion H7; subst.
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in *.
      destruct_fresh (s2 inum).
      logic_clean.
      subst.
      eapply_fresh H2 in H10; eauto.
      logic_clean; subst.
             
      exists (RFinished (upd s2 inum (Build_File u'' (blocks f))) (Some tt));
      simpl; intuition eauto.
      repeat econstructor; eauto.
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H8; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H8; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H10; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H10; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup; eauto.
      }
      {
        cleanup.
        destruct (H inum).
        exfalso; apply H3; eauto; congruence.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      repeat split_ors;
      try solve [ repeat econstructor; eauto].
      {
        do 3 econstructor; eauto.
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        destruct (i inum).
        exfalso; apply H2; congruence.
      }
      {
        cleanup.        
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        eapply H4 in H; eauto; try congruence; cleanup.
        do 3 econstructor; intuition eauto.
        cleanup; eauto.
        destruct (H2 inum).
        exfalso; apply H5; congruence.
      }
      {
        cleanup.
        intuition eauto.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
      eapply H2 in H10; eauto; cleanup.
      repeat split_ors;
      try solve [ repeat econstructor; eauto].

      cleanup.
      edestruct H; exfalso.
      eapply H3; eauto; congruence.
      {
        cleanup.
        intuition eauto.
      }
    }
  }
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H10.
    invert_exec.
    {
      edestruct ss_FD_Recover; eauto.
      cleanup.
      exists (Recovered (extract_state_r x)).
      intuition eauto.
      repeat econstructor; eauto.
    }
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in H2.
      destruct_fresh (s2 inum); eauto.
      cleanup; eauto.
      eapply_fresh H2 in H9; eauto; try congruence; cleanup.
      
      edestruct ss_FD_Recover; eauto.
      instantiate (1:= upd s2 inum (Build_File u'' (blocks f))).
      instantiate (1:= Some inum).
      instantiate (1:= u').
      {
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly.
        intuition eauto.
        {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H7; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H7; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H9; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H9; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H7; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H7; eauto; try congruence.
          cleanup; eauto.
        }
      }
      }
      {
        cleanup.
        exists (Recovered (extract_state_r x)); simpl.
        intuition eauto.
        repeat econstructor; eauto.
      }
      {
        cleanup.
        destruct (H inum).
        exfalso; apply H3; congruence.
      }
    }
  }
  Unshelve.
  all: repeat econstructor; eauto.
Qed.


Theorem ss_FD_create:
  forall n u u' u'',
    SelfSimulation u (FileDiskOp.(Op) (Create u'')) (FileDiskOp.(Op) (Create u'')) (FileDiskOp.(Op) Recover) (fun _ => True) (FD_related_states u' None) (eq u') (repeat (fun s => s) n).
Proof.
  unfold SelfSimulation; intros.
  repeat invert_exec.
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H11.
    inversion H7; subst.
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in *.
      destruct_fresh (s2 inum).
      logic_clean.
      edestruct (H inum).
      exfalso; apply H5; eauto; congruence.
             
      exists (RFinished (upd s2 inum (Build_File u'' [])) (Some inum));
      simpl; intuition eauto.
      repeat econstructor; eauto.
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H5; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H5; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H5; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H5; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H4 in H5; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H4 in H5; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup; eauto.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      {
        do 3 econstructor; eauto.
        intros.
        apply H8 in H.
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        cleanup; eauto.
        apply H1; eauto.
      }
      {
        cleanup.
        intuition eauto.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      invert_exec.
      try solve [ repeat econstructor; eauto].
      {
        cleanup.
        intuition eauto.
      }
    }
  }
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H10.
    invert_exec.
    {
      edestruct ss_FD_Recover; eauto.
      cleanup.
      exists (Recovered (extract_state_r x)).
      intuition eauto.
      repeat econstructor; eauto.
    }
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in H2.
      destruct_fresh (s2 inum); eauto.
      {
        cleanup.
        destruct (H inum).
        exfalso; apply H5; congruence.
      }
      
      cleanup; eauto.
      
      edestruct ss_FD_Recover; eauto.
      instantiate (1:= upd s2 inum (Build_File u'' [])).
      instantiate (1:= None).
      instantiate (1:= u').
      {
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly.
        intuition eauto.
        {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H5; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H5; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H5; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H5; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H4; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H4; eauto; try congruence.
          cleanup; eauto.
        }
      }
      }
      {
        cleanup.
        exists (Recovered (extract_state_r x)); simpl.
        intuition eauto.
        repeat econstructor; eauto.
      }
      
    }
  }
Qed.


Theorem ss_FD_delete:
  forall n inum u u',
    SelfSimulation u (FileDiskOp.(Op) (Delete inum)) (FileDiskOp.(Op) (Delete inum)) (FileDiskOp.(Op) Recover) (fun _ => True) (FD_related_states u' None) (eq u') (repeat (fun s => s) n).
Proof.
  unfold SelfSimulation; intros.
  repeat invert_exec.
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H11.
    inversion H7; subst.
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in *.
      destruct_fresh (s2 inum).
      logic_clean.
      subst.
      eapply_fresh H2 in H9; eauto.
      logic_clean; subst.
             
      exists (RFinished (Mem.delete s2 inum) (Some tt));
      simpl; intuition eauto.
      repeat (econstructor; eauto).
      {
        destruct (addr_dec a inum); subst.
        rewrite delete_eq in H8; eauto; congruence.
        rewrite delete_ne in *; eauto.
        apply H in H10; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite delete_eq in H8; eauto; congruence.
        rewrite delete_ne in *; eauto.
        apply H in H10; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite delete_eq in *; eauto.
          cleanup.
        }
        {
          rewrite delete_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite delete_eq in *; eauto.
          cleanup.
        }
        {
          rewrite delete_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite delete_eq in *; eauto.
          cleanup.
        }
        {
          rewrite delete_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite delete_eq in *; eauto.
          cleanup.
        }
        {
          rewrite delete_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup; eauto.
      }
      {
        cleanup.
        destruct (H inum).
        exfalso; apply H3; eauto; congruence.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      repeat split_ors;
      try solve [ repeat econstructor; eauto].
      {
        do 3 econstructor; eauto.
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        destruct (i inum).
        exfalso; apply H2; congruence.
      }
      {
        cleanup.        
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        eapply H4 in H; eauto; try congruence; cleanup.
        do 3 econstructor; intuition eauto.
        cleanup; eauto.
        destruct (H2 inum).
        exfalso; apply H5; congruence.
      }
      {
        cleanup.
        intuition eauto.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
      eapply H2 in H9; eauto; cleanup.
      repeat split_ors;
      try solve [ repeat econstructor; eauto].

      cleanup.
      edestruct H; exfalso.
      eapply H3; eauto; congruence.
      {
        cleanup.
        intuition eauto.
      }
    }
  }
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H10.
    invert_exec.
    {
      edestruct ss_FD_Recover; eauto.
      cleanup.
      exists (Recovered (extract_state_r x)).
      intuition eauto.
      repeat econstructor; eauto.
    }
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in H2.
      destruct_fresh (s2 inum); eauto.
      cleanup; eauto.
      eapply_fresh H2 in H4; eauto; try congruence; cleanup.
      
      edestruct ss_FD_Recover; eauto.
      instantiate (1:= Mem.delete s2 inum).
      instantiate (1:= None).
      instantiate (1:= u').
      {
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly.
        intuition eauto.
        {
        destruct (addr_dec a inum); subst.
        rewrite delete_eq in H7; eauto; congruence.
        rewrite delete_ne in *; eauto.
        apply H in H7; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite delete_eq in H7; eauto; congruence.
        rewrite delete_ne in *; eauto.
        apply H in H7; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite delete_eq in *; eauto.
          cleanup.
        }
        {
          rewrite delete_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite delete_eq in *; eauto.
          cleanup.
        }
        {
          rewrite delete_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite delete_eq in *; eauto.
          cleanup.
        }
        {
          rewrite delete_ne in *; eauto.
          eapply H2 in H7; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite delete_eq in *; eauto.
          cleanup.
        }
        {
          rewrite delete_ne in *; eauto.
          eapply H2 in H7; eauto; try congruence.
          cleanup; eauto.
        }
      }
      }
      {
        cleanup.
        exists (Recovered (extract_state_r x)); simpl.
        intuition eauto.
        repeat econstructor; eauto.
      }
      {
        cleanup.
        destruct (H inum).
        exfalso; apply H5; congruence.
      }
    }
  }
  Unshelve.
  all: repeat econstructor; eauto.
Qed.



Theorem ss_FD_write_input:
  forall n inum off v1 v2 u u',
    SelfSimulation u (FileDiskOp.(Op) (Write inum off v1)) (FileDiskOp.(Op) (Write inum off v2)) (FileDiskOp.(Op) Recover) (fun _ => True) (FD_related_states u' (Some inum)) (eq u') (repeat (fun s => s) n).
Proof.
  unfold SelfSimulation; intros.
  repeat invert_exec.
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H11.
    inversion H7; subst.
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in *.
      destruct_fresh (s2 inum).
      logic_clean.
      subst.
      eapply_fresh H2 in H11; eauto.
      logic_clean; subst.
      
      exists (RFinished (upd s2 inum (Build_File (owner f) (updn (blocks f) off v2))) (Some tt)); simpl; intuition eauto.
      repeat econstructor; eauto.
      rewrite <- H4; eauto.
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H8; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H8; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H11; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H11; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
          repeat rewrite updn_length; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup; eauto.
      }
      {
        cleanup.
        destruct (H inum).
        exfalso; apply H3; eauto; congruence.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      repeat split_ors;
      try solve [ repeat econstructor; eauto].
      {
        do 3 econstructor; eauto.
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        destruct (i inum).
        exfalso; apply H2; congruence.
      }
      {
        cleanup.        
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        eapply H4 in H; eauto; try congruence; cleanup.
        do 3 econstructor; intuition eauto.
        cleanup; eauto.
        destruct (H2 inum).
        exfalso; apply H5; congruence.
      }
      {
        cleanup.
        intuition eauto.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
      eapply H2 in H11; eauto; cleanup.
      repeat split_ors;
      try solve [ repeat econstructor; eauto].

      cleanup.
      edestruct H; exfalso.
      eapply H3; eauto; congruence.
      {
        cleanup.
        intuition eauto.
      }
    }
  }
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H10.
    invert_exec.
    {
      edestruct ss_FD_Recover; eauto.
      cleanup.
      exists (Recovered (extract_state_r x)).
      intuition eauto.
      repeat econstructor; eauto.
    }
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in H2.
      destruct_fresh (s2 inum); eauto.
      cleanup; eauto.
      eapply_fresh H2 in H10; eauto; try congruence; cleanup.
      
      edestruct ss_FD_Recover; eauto.
      instantiate (1:= upd s2 inum (Build_File (owner f) (updn (blocks f) off v2))).
      instantiate (2:= u').
      instantiate (1:= Some inum).
      {
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly.
        intuition eauto.
        {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H7; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H7; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H10; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H10; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H6; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
          repeat rewrite updn_length; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H6; eauto; try congruence.
          cleanup; eauto.
        }
      }
      }
      cleanup.
      exists (Recovered (extract_state_r x)); simpl.
      intuition eauto.
      repeat econstructor; eauto.

      cleanup.
      destruct (H inum).
      exfalso; apply H3; congruence.
    }
  }
  Unshelve.
  all: repeat econstructor; eauto.
Qed.



Theorem ss_FD_extend_input:
  forall n inum v1 v2 u u',
    SelfSimulation u (FileDiskOp.(Op) (Extend inum v1)) (FileDiskOp.(Op) (Extend inum v2)) (FileDiskOp.(Op) Recover) (fun _ => True) (FD_related_states u' (Some inum)) (eq u') (repeat (fun s => s) n).
Proof.
  unfold SelfSimulation; intros.
  repeat invert_exec.
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H11.
    inversion H7; subst.
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in *.
      destruct_fresh (s2 inum).
      logic_clean.
      subst.
      eapply_fresh H2 in H10; eauto.
      logic_clean; subst.
      
      exists (RFinished (upd s2 inum (Build_File (owner f) ((blocks f) ++ [v2]))) (Some tt));
      simpl; intuition eauto.
      repeat econstructor; eauto.
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H8; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H8; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H10; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H10; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
          repeat rewrite app_length; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H8; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup; eauto.
      }
      {
        cleanup.
        destruct (H inum).
        exfalso; apply H3; eauto; congruence.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      repeat (split; eauto).
      repeat split_ors;
      try solve [ repeat econstructor; eauto].
      {
        do 3 econstructor; eauto.
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        destruct (i inum).
        exfalso; apply H2; congruence.
      }
      {
        cleanup.        
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly in *.
        destruct_fresh (s2 inum); eauto.
        cleanup; eauto.
        eapply H4 in H; eauto; try congruence; cleanup.
        do 3 econstructor; intuition eauto.
        cleanup; eauto.
        destruct (H2 inum).
        exfalso; apply H5; congruence.
      }
      {
        cleanup.
        intuition eauto.
      }
    }
    {
      exists (RFinished s2 None); simpl.
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in *.
      destruct_fresh (s2 inum); eauto.
      cleanup; eauto.
      eapply H2 in H10; eauto; try congruence; cleanup.      
      repeat (split; eauto).
      do 3 econstructor; eauto.

      cleanup; eauto.
      destruct (H inum).
      exfalso; apply H3; congruence.
    }
  }
  {
    destruct n; simpl in *; cleanup; try congruence.
    invert_exec'' H10.
    invert_exec.
    {
      edestruct ss_FD_Recover; eauto.
      cleanup.
      exists (Recovered (extract_state_r x)).
      intuition eauto.
      repeat econstructor; eauto.
    }
    {
      unfold FD_related_states, same_for_user_except,
      addrs_match_exactly in H2.
      destruct_fresh (s2 inum); eauto.
      cleanup; eauto.
      eapply_fresh H2 in H9; eauto; try congruence; cleanup.
      
      edestruct ss_FD_Recover; eauto.
      instantiate (1:= upd s2 inum (Build_File (owner f) ((blocks f) ++ [v2]))).
      instantiate (1:= Some inum).
      instantiate (1:= u').
      {
        unfold FD_related_states, same_for_user_except,
        addrs_match_exactly.
        intuition eauto.
        {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H7; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        destruct (addr_dec a inum); subst.
        rewrite upd_eq in H7; eauto; congruence.
        rewrite upd_ne in *; eauto.
        apply H in H6; congruence.
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H9; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *.
          eapply H1 in H9; eauto; try congruence.
        }
        {
          rewrite upd_ne in *; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H6; eauto; try congruence.
          cleanup; eauto.
        }
      }
      {
        cleanup.
        destruct (addr_dec inum inum0); subst.
        {
          rewrite upd_eq in *; eauto.
          cleanup.
          simpl in *; eauto.
          repeat rewrite app_length; eauto.
        }
        {
          rewrite upd_ne in *; eauto.
          eapply H2 in H6; eauto; try congruence.
          cleanup; eauto.
        }
      }
      }
      cleanup.
      exists (Recovered (extract_state_r x)); simpl.
      intuition eauto.
      repeat econstructor; eauto.

      cleanup.
      destruct (H inum).
      exfalso; apply H3; congruence.
    }
  }
  Unshelve.
  all: repeat econstructor; eauto.
Qed.

Definition not_change_owner {T} (o : FileDiskOp.(operation) T) :=
  match o with
  | ChangeOwner _ _ => False
  | _ => True
  end.

Theorem ss_FD_not_change_owner:
  forall T (o : FileDiskOp.(operation) T) n u u',
    not_change_owner o ->
    SelfSimulation u (FileDiskOp.(Op) o) (FileDiskOp.(Op) o) (FileDiskOp.(Op) Recover) (fun _ => True) (FD_related_states u' None) (eq u') (repeat (fun s => s) n).
Proof.
  intros; destruct o; eauto.
  apply ss_FD_read.
  apply ss_FD_write.
  apply ss_FD_extend.
  simpl in *; intuition.
  apply ss_FD_create.
  apply ss_FD_delete.
  apply ss_FD_Recover.
Qed.

Theorem two_user_exec:
  forall T1 T2 (o1: FileDiskOp.(operation) T1) (o2: FileDiskOp.(operation) T2)
    s1 ret1 s2 ret2 l_o1 n l_o2 m user adversary,
    not_change_owner o1 ->
    not_change_owner o2 ->
    FD_related_states adversary None s1 s2 ->
    recovery_exec FileDisk user l_o1 s1 (repeat (fun s => s) n) (FileDiskOp.(Op) o1) (FileDiskOp.(Op) Recover) ret1 ->
    recovery_exec FileDisk adversary l_o2 (extract_state_r ret1) (repeat (fun s => s) m) (FileDiskOp.(Op) o2) (FileDiskOp.(Op) Recover) ret2 ->
    exists ret1' ret2',
      recovery_exec FileDisk user l_o1 s2 (repeat (fun s => s) n) (FileDiskOp.(Op) o1) (FileDiskOp.(Op) Recover) ret1' /\
      recovery_exec FileDisk adversary l_o2 (extract_state_r ret1') (repeat (fun s => s) m) (FileDiskOp.(Op) o2) (FileDiskOp.(Op) Recover)ret2' /\
      FD_related_states adversary None (extract_state_r ret2) (extract_state_r ret2') /\
      extract_ret_r ret2 = extract_ret_r ret2'.
Proof.
  intros.
  eapply ss_FD_not_change_owner in H1; try apply H; eauto.
  cleanup.
  eapply ss_FD_not_change_owner in H4; eauto.
  cleanup.
  do 2 eexists; intuition eauto.
Qed.
    

(** Intermediate Layers *)
Import AuthenticatedDiskLayer.
Notation "'AuthenticatedDisk'" := AuthenticatedDiskLang (at level 0).

(* Authenticated Disk *)
Definition AD_valid_state := refines_valid FileDiskRefinement FD_valid_state.
Definition AD_related_states u exc := refines_related FileDiskRefinement (FD_related_states u exc).

(* Transactional Disk *)
Definition TD_valid_state s1 := fun s2 => AD_valid_state (s1, s2).
Definition TD_related_states u exc s1 := fun s2 s2' => AD_related_states u exc (s1, s2) (s1, s2').

Import TransactionCacheLayer TransactionalDiskLayer TransactionalDiskRefinement.
Notation "'TransactionCache'" := TransactionCacheLang (at level 0).

Notation "'TransactionalDisk'" := (TransactionalDiskLang data_length) (at level 0).
Notation "'TransactionalDisk.refinement'" := TransactionalDiskRefinement.

(* Transaction Cache *)
Definition TC_valid_state s1 := refines_valid TransactionalDisk.refinement (TD_valid_state s1).
Definition TC_related_states u exc s1 := refines_related TransactionalDisk.refinement (TD_related_states u exc s1).

(* Logged Disk *)
Definition LD_valid_state s := fun s2 => TC_valid_state (fst s) (snd s, s2).
Definition LD_related_states u exc s := fun s2 s2' => TC_related_states u exc (fst s) (snd s, s2) (snd s, s2').

Import CachedDiskLayer LoggedDiskLayer CryptoDiskLayer LoggedDiskRefinement.

Notation "'LoggedDisk'" := LoggedDiskLang (at level 0).
Notation "'LoggedDisk.refinement'" := LoggedDiskRefinement.

Notation "'CachedDisk'" := CachedDiskLang (at level 0).
Notation "'CryptoDisk'" := CryptoDiskLang (at level 0).

(* Cached Disk *)
Definition CD_valid_state s1 := refines_valid LoggedDisk.refinement (LD_valid_state s1).
Definition CD_related_states u exc s1 := refines_related LoggedDisk.refinement (LD_related_states u exc s1).

(* Crypto Disk *)
Definition CrD_valid_state s := fun s2 => CD_valid_state (fst s) (snd s, s2).
Definition CrD_related_states u exc s := fun s2 s2' => CD_related_states u exc (fst s) (snd s, s2) (snd s, s2').

(** Bottom Layers *)
(* Authentication Layer *)
Definition AL_valid_state s2 := fun s1 => AD_valid_state (s1, s2).
Definition AL_related_states u exc s2 := fun s1 s1' => AD_related_states u exc (s1, s2) (s1', s2).

(* Storage Layer *)
Definition SL_valid_state s := fun s1 => TC_valid_state (fst s) (s1, snd s).
Definition SL_related_states u exc s := fun s1 s1' => TC_related_states u exc (fst s) (s1, snd s) (s1', snd s).

(* Cache Layer *)
Definition CL_valid_state s := fun s1 => CD_valid_state (fst s) (s1, snd s).
Definition CL_related_states u exc s := fun s1 s1' => CD_related_states u exc (fst s) (s1, snd s) (s1', snd s).

(* Crypto Layer *)
Definition CrL_valid_state s := fun s1 => CrD_valid_state (fst s) (s1, snd s).
Definition CrL_related_states u exc s := fun s1 s1' =>  CrD_related_states u exc (fst s) (s1, snd s) (s1', snd s).

(* Disk Layer *)
Definition DL_valid_state s := fun s2 => CrD_valid_state (fst s) (snd s, s2).
Definition DL_related_states u exc s := fun s2 s2' => CrD_related_states u exc (fst s) (snd s, s2) (snd s, s2').
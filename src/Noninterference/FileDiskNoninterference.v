Require Import Framework FSParameters File FileDiskLayer FileDiskRefinement.
Require Import AuthenticatedDiskLayer.
Require Import TransactionalDiskLayer TransactionalDiskRefinement.
Require Import TransactionCacheLayer.
Require Import LoggedDiskLayer LoggedDiskRefinement.
Require Import StorageLayer.
Require Import CryptoDiskLayer CachedDiskLayer.

Notation "'CryptoDisk'" := CryptoDiskLang (at level 0).

Notation "'CachedDisk'" := CachedDiskLang (at level 0).

Notation "'LoggedDisk'" := LoggedDiskLang (at level 0).
Notation "'LoggedDisk.refinement'" := LoggedDiskRefinement.

Notation "'TransactionCache'" := TransactionCacheLang (at level 0).

Notation "'TransactionalDisk'" := (TransactionalDiskLang data_length) (at level 0).
Notation "'TransactionalDisk.refinement'" := TransactionalDiskRefinement.

Notation "'AuthenticatedDisk'" := AuthenticatedDiskLang (at level 0).

Notation "'FileDisk'" := (FileDiskLang inode_count) (at level 0).
Notation "'FileDisk.refinement'" := FileDiskRefinement.

Definition same_for_user (s1 s2: FileDisk.(state)) :=
  let u1 := fst s1 in
  let u2 := fst s2 in
  let d1 := snd s1 in
  let d2 := snd s2 in
  u1 = u2 /\
  addrs_match_exactly d1 d2 /\
  (forall inum file1 file2,
     d1 inum = Some file1 ->
     d2 inum = Some file2 ->
     (file1.(owner) = u1 \/
      file2.(owner) = u1) ->
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

Fixpoint horizontally_compose_valid_prog1 {O1 O2} (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2)) C T (p1: prog L1 T) :=
         match p1 with
         | @Op _ T' p => C T' (Op (HorizontalComposition O1 O2) (P1 p))
         | @Ret _ T' t => C T' (Ret t)
         | @Bind _ T1 T2 p1 p2 =>
           horizontally_compose_valid_prog1 L1 L2 LL C T1 p1 /\
           (forall r, horizontally_compose_valid_prog1 L1 L2 LL C T2 (p2 r))
         end.

Fixpoint horizontally_compose_valid_prog2 {O1 O2} (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2)) C T (p2: prog L2 T) :=
         match p2 with
         | @Op _ T' p => C T' (Op (HorizontalComposition O1 O2) (P2 p))
         | @Ret _ T' t => C T' (Ret t)
         | @Bind _ T1 T2 p1 p2 =>
           horizontally_compose_valid_prog2 L1 L2 LL C T1 p1 /\
           (forall r, horizontally_compose_valid_prog2 L1 L2 LL C T2 (p2 r))
         end.


Lemma ss_hc_rev_p1:
  forall O1 O2 (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2))
    R C V,
    SelfSimulation LL R C V ->
    forall s2,
      SelfSimulation L1
        (fun s1 => R (s1, s2))
        (horizontally_compose_valid_prog1 L1 L2 LL C)
        (fun s1 s1' =>  V (s1, s2) (s1', s2)).
Proof.
  intros.
  constructor.
  intros T o p.
  generalize dependent s2.
  generalize dependent o.
  induction p; intros; cleanup.
  - (* Op *)
    repeat invert_exec; simpl in *.
    + (* P1 Finished *)
      edestruct H, self_simulation_correct.
      apply H0.
      apply H1.
      all: simpl in *; eauto.
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

(** Relation Definitions *)

(** Top Layer *)
(* File Disk *)
Definition FD_valid_state := fun (s: state FileDisk) => exists fmap, files_rep fmap (snd s).
Definition FD_valid_prog  := fun T (p: prog FileDisk T) => True.
Definition FD_related_states := same_for_user.

(** Intermediate Layers *)
(* Authenticated Disk *)
Definition AD_valid_state := refines_to_valid FileDisk.refinement FD_valid_state.
Definition AD_valid_prog  := compiles_to_valid FileDisk.refinement FD_valid_prog.
Definition AD_related_states := refines_to_related FileDisk.refinement FD_related_states.

(* Transactional Disk *)
Definition TD_valid_state s1 := fun s2 => AD_valid_state (s1, s2).
Definition TD_valid_prog  := horizontally_compose_valid_prog2 AuthenticationLang TransactionalDisk AuthenticatedDisk AD_valid_prog.
Definition TD_related_states s1 := fun s2 s2' => AD_related_states (s1, s2) (s1, s2').

(* Transaction Cache *)
Definition TC_valid_state s1 := refines_to_valid TransactionalDisk.refinement (TD_valid_state s1).
Definition TC_valid_prog  := compiles_to_valid TransactionalDisk.refinement TD_valid_prog.
Definition TC_related_states s1 := refines_to_related TransactionalDisk.refinement (TD_related_states s1).

(* Logged Disk *)
Definition LD_valid_state s := fun s2 => TC_valid_state (fst s) (snd s, s2).
Definition LD_valid_prog  := horizontally_compose_valid_prog2 (StorageLang (list (addr * value))) LoggedDisk TransactionCache TC_valid_prog.
Definition LD_related_states s := fun s2 s2' => TC_related_states (fst s) (snd s, s2) (snd s, s2').

(* Cached Disk *)
Definition CD_valid_state s1 := refines_to_valid LoggedDisk.refinement (LD_valid_state s1).
Definition CD_valid_prog  := compiles_to_valid LoggedDisk.refinement LD_valid_prog.
Definition CD_related_states s1 := refines_to_related LoggedDisk.refinement (LD_related_states s1).

(* Crypto Disk *)
Definition CrD_valid_state s := fun s2 => CD_valid_state (fst s) (snd s, s2).
Definition CrD_valid_prog  := horizontally_compose_valid_prog2 (CacheLang addr_dec value) CryptoDisk CachedDisk CD_valid_prog.
Definition CrD_related_states s := fun s2 s2' => CD_related_states (fst s) (snd s, s2) (snd s, s2').

(** Bottom Layers *)
(* Authentication Layer *)
Definition AL_valid_state s2 := fun s1 => AD_valid_state (s1, s2).
Definition AL_valid_prog  := horizontally_compose_valid_prog1 AuthenticationLang TransactionalDisk AuthenticatedDisk AD_valid_prog.
Definition AL_related_states s2 := fun s1 s1' => AD_related_states (s1, s2) (s1', s2).

(* Storage Layer *)
Definition SL_valid_state s := fun s1 => TC_valid_state (fst s) (s1, snd s).
Definition SL_valid_prog  := horizontally_compose_valid_prog1 (StorageLang (list (addr * value))) LoggedDisk TransactionCache TC_valid_prog.
Definition SL_related_states s := fun s1 s1' => TC_related_states (fst s) (s1, snd s) (s1', snd s).

(* Cache Layer *)
Definition CL_valid_state s := fun s1 => CD_valid_state (fst s) (s1, snd s).
Definition CL_valid_prog  := horizontally_compose_valid_prog1 (CacheLang addr_dec value) CryptoDisk CachedDisk CD_valid_prog.
Definition CL_related_states s := fun s1 s1' => CD_related_states (fst s) (s1, snd s) (s1', snd s).

(* Crypto Layer *)
Definition CrL_valid_state s := fun s1 => CrD_valid_state (fst s) (s1, snd s).
Definition CrL_valid_prog  := horizontally_compose_valid_prog1 CryptoLang (DiskLang addr_dec value) CryptoDisk CrD_valid_prog.
Definition CrL_related_states s := fun s1 s1' =>  CrD_related_states (fst s) (s1, snd s) (s1', snd s).

(* Disk Layer *)
Definition DL_valid_state s := fun s2 => CrD_valid_state (fst s) (snd s, s2).
Definition DL_valid_prog  := horizontally_compose_valid_prog2 CryptoLang (DiskLang addr_dec value) CryptoDisk CrD_valid_prog.
Definition DL_related_states s := fun s2 s2' => CrD_related_states (fst s) (snd s, s2) (snd s, s2').



(** NI Theorems *)
(** Top Layer *)
Theorem ss_FD:
  SelfSimulation FileDisk FD_valid_state FD_valid_prog FD_related_states.
Proof. Admitted.

(** Intermediate Layers *)
Theorem ss_AD:
  SelfSimulation AuthenticatedDisk AD_valid_state AD_valid_prog AD_related_states.
Proof.
  intros.
  unfold AD_valid_state, AD_valid_prog, AD_related_states; simpl.   
  (* Theorem from file disk refinement here *)
Admitted.

Theorem ss_TD:
  forall s, SelfSimulation TransactionalDisk (TD_valid_state s) TD_valid_prog (TD_related_states s).
Proof.
  intros.
  unfold TD_valid_state, TD_valid_prog, TD_related_states; simpl.  
  eapply ss_hc_rev_p2 with (R:= AD_valid_state) (V:= AD_related_states).
  apply ss_AD.
Qed.

Theorem ss_TC:
  forall s, SelfSimulation TransactionCache (TC_valid_state s) TC_valid_prog (TC_related_states s).
Proof.
  intros.
  unfold TC_valid_state, TC_valid_prog, TC_related_states; simpl.
  (* Theorem from transactional disk refinement here *)
Admitted.

Theorem ss_LD:
  forall s, SelfSimulation LoggedDisk (LD_valid_state s) LD_valid_prog (LD_related_states s).
Proof.
  intros.
  unfold LD_valid_state, LD_valid_prog, LD_related_states; simpl.
  eapply ss_hc_rev_p2 with (R:= TC_valid_state (fst s)) (V:= TC_related_states (fst s)).
  eapply ss_TC.
Qed.

Theorem ss_CD:
  forall s, SelfSimulation CachedDisk (CD_valid_state s) CD_valid_prog (CD_related_states s).
Proof.
  intros.
  unfold CD_valid_state, CD_valid_prog, CD_related_states; simpl.
  (* Need theorem from logged disk refinement here *)
Admitted.

Theorem ss_CrD:
  forall s, SelfSimulation CryptoDisk (CrD_valid_state s) CrD_valid_prog (CrD_related_states s).
Proof.
  intros.
  unfold CrD_valid_state, CrD_valid_prog, CrD_related_states; simpl.
  eapply ss_hc_rev_p2 with (R:= CD_valid_state (fst s)) (V:= CD_related_states (fst s)).
  eapply ss_CD.
Qed.

(** Bottom Layers *)
Theorem ss_AL:
  forall s, SelfSimulation (AuthenticationLang) (AL_valid_state s) AL_valid_prog (AL_related_states s).
Proof.
  intros.
  unfold AL_valid_state, AL_valid_prog, AL_related_states; simpl.  
  eapply ss_hc_rev_p1 with (R:= AD_valid_state) (V:= AD_related_states).
  apply ss_AD.
Qed.

Theorem ss_SL:
  forall s, SelfSimulation (StorageLang (list (addr * value))) (SL_valid_state s) SL_valid_prog (SL_related_states s).
Proof.
  intros.
  unfold SL_valid_state, SL_valid_prog, SL_related_states; simpl.
  eapply ss_hc_rev_p1 with (R:= TC_valid_state (fst s)) (V:= TC_related_states (fst s)).
  eapply ss_TC.
Qed.


Theorem ss_CL:
  forall s, SelfSimulation (CacheLang addr_dec value) (CL_valid_state s) CL_valid_prog (CL_related_states s).
Proof.
  intros.
  unfold CL_valid_state, CL_valid_prog, CL_related_states; simpl.
  eapply ss_hc_rev_p1 with (R:= CD_valid_state (fst s)) (V:= CD_related_states (fst s)).
  eapply ss_CD.
Qed.

Theorem ss_DL:
  forall s, SelfSimulation (DiskLang addr_dec value) (DL_valid_state s) DL_valid_prog (DL_related_states s).
Proof.
  intros.
  unfold DL_valid_state, DL_valid_prog, DL_related_states; simpl.  
  eapply ss_hc_rev_p2 with (R:= CrD_valid_state (fst s)) (V:= CrD_related_states (fst s)).
  eapply ss_CrD.
Qed.

Theorem ss_CrL:
  forall s, SelfSimulation CryptoLang (CrL_valid_state s) CrL_valid_prog (CrL_related_states s).
Proof.
  intros.  
  unfold CrL_valid_state, CrL_valid_prog, CrL_related_states; simpl.  
  eapply ss_hc_rev_p1 with (R:= CrD_valid_state (fst s)) (V:= CrD_related_states (fst s)).
  eapply ss_CrD.
Qed.


(** Required theorems for transfer *)
Theorem ortsfr_FD:
  oracle_refines_to_same_from_related FileDisk.refinement FD_related_states.
Proof. Admitted.

Theorem ecpv_FD:  
exec_compiled_preserves_validity FileDisk.refinement AD_valid_state.
Proof.
  unfold AD_valid_state, FD_valid_state,
  exec_compiled_preserves_validity, refines_to_valid; intros; eauto.
Qed.


Theorem ortsfr_TD:
  forall s, oracle_refines_to_same_from_related TransactionalDisk.refinement (TD_related_states s).
Proof.
  unfold oracle_refines_to_same_from_related; simpl.
  induction p2; simpl; intros.
  cleanup.
  eexists; intuition eauto.
  
  - destruct p; simpl in *.
    { (* Start *)
      split_ors; cleanup.
      { (* Finished *)
        destruct sbs.
        edestruct wp_to_exec with (p:= Transaction.start)
      (Q:= strongest_postcondition TransactionToTransactionalDisk.Definitions.low Transaction.start
         (fun o' s' => refines_to_related TransactionalDisk.refinement (TD_related_states s) s1 s' /\ s' = s2 /\ o' = o)); eauto.
        simpl.
        do 2 eexists; intuition eauto; simpl.
        eexists; intuition eauto; simpl.
        eexists; intuition eauto; simpl.
        eexists; intuition eauto; simpl.
        eexists; intuition eauto; simpl.
        instantiate (1:= s2);
        instantiate (1:= fst s2); simpl; eauto.
        destruct s2; eauto.
        
        eapply exec_to_sp with (P:= fun o' s' => refines_to_related TransactionalDisk.refinement (TD_related_states s) s' s2 /\ s' = s1 /\ o' = o) in H0; eauto.
        simpl in *; cleanup; eauto.
      
      simpl; eauto.
      cleanup.
      simpl in H2; cleanup.
      left; do 2 eexists; intuition eauto.
      destruct x; simpl in *; cleanup; eauto.
    + split_ors; cleanup.
       edestruct wcp_to_exec with (p:= Transaction.start)
      (Q:= strongest_crash_postcondition TransactionToTransactionalDisk.Definitions.low Transaction.start
         (fun o' s' =>
            refines_to_related TransactionalDisk.refinement (TD_related_states s) s1 s' /\ s' = s2 /\ o' = o)); eauto.
       do 2 eexists; intuition eauto; simpl.

       eapply exec_to_scp with (P:= fun o' s' => refines_to_related TransactionalDisk.refinement (TD_related_states s) s' s2 /\ s' = s1 /\ o' = o) in H0; eauto.
       simpl in *; cleanup; eauto.

       split_ors; cleanup; simpl in *;
       try match goal with
       | [H: StorageLayer.strongest_crash_postcondition' _ _ _ |- _ ] =>
         inversion H; clear H; cleanup
       end.

      left.
      eexists; intuition eauto; simpl.
      eexists; intuition eauto; simpl.
      eexists; intuition eauto; simpl.
      left.
      eexists; intuition eauto; simpl.
      instantiate (1:= s2);
      simpl; eauto.
      destruct s2; eauto.

      right.
      eexists; intuition eauto; simpl.
      eexists; intuition eauto; simpl.
      repeat econstructor.
      econstructor.
      solve [repeat econstructor; eauto].
      eexists; intuition eauto; simpl.
      left.
      eexists; intuition eauto; simpl.
      instantiate (1:= s2);
      simpl; eauto.
      destruct s2; eauto.

      
      
      
      simpl; eauto.
      cleanup.
      simpl in H2; cleanup.
      left; do 2 eexists; intuition eauto.
      destruct x; simpl in *; cleanup; eauto.

      
      econstructor.


      
Admitted.

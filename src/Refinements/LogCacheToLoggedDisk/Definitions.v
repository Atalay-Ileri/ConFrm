Require Import Framework TotalMem CachedDiskLayer LoggedDiskLayer Log LogCache.
Require Import FSParameters FunctionalExtensionality Lia.
Close Scope predicate_scope.
Import ListNotations.

Local Definition impl_core := CachedDiskOperation.
Local Definition abs_core := LoggedDiskOperation data_length.
Local Definition impl := CachedDiskLang.
Local Definition abs := LoggedDiskLang data_length.

Definition compile T (p2: Core.operation abs_core T) : prog impl T.
 destruct p2.
 exact (read a).
 exact (write l l0).
 exact recover.
Defined.

Definition token_refines_to  T u (d1: state impl) (p: Core.operation abs_core T) get_reboot_state o1 o2 : Prop :=
   match p with
   | Read a =>
     (exists d1' r,
        exec impl u o1 d1 (read a) (Finished d1' r) /\
        o2 = Cont /\
        (forall merged_disk,
           cached_log_rep merged_disk d1 -> 
           cached_log_rep merged_disk d1')) \/
     (exists d1',
        exec impl u o1 d1 (read a) (Crashed d1') /\
        o2 = CrashBefore /\
        (forall merged_disk,
            cached_log_rep merged_disk d1 -> 
            cached_log_rep merged_disk d1'))
   | Write la lv =>
     (exists d1' r,
          exec impl u o1 d1 (write la lv) (Finished d1' r) /\          
          o2 = Cont /\
          (forall merged_disk,
             cached_log_rep merged_disk d1 ->
             (cached_log_rep merged_disk d1' \/
             cached_log_rep (upd_batch merged_disk la lv) d1'))) \/
     (exists d1',
        (exec impl u o1 d1 (write la lv) (Crashed d1') /\
         o2 = CrashBefore /\
         (forall merged_disk,
            cached_log_rep merged_disk d1 -> 
            cached_log_rep merged_disk d1' \/
            cached_log_crash_rep (During_Apply merged_disk) d1' \/
            cached_log_crash_rep (After_Apply merged_disk) d1') \/
        (exec impl u o1 d1 (write la lv) (Crashed d1') /\
         o2 = CrashAfter /\
         (** ???? **)
         (forall merged_disk,
            cached_log_rep merged_disk d1 ->
            cached_log_crash_rep (After_Commit (upd_batch merged_disk la lv)) d1')) \/
        (exec impl u o1 d1 (write la lv) (Crashed d1') /\
         (forall merged_disk,
            cached_log_rep merged_disk d1 ->
            cached_log_crash_rep (During_Commit merged_disk (upd_batch merged_disk la lv)) d1' /\
            ((cached_log_reboot_rep merged_disk (get_reboot_state d1') /\ o2 = CrashBefore) \/
            (cached_log_reboot_rep (upd_batch merged_disk la lv) (get_reboot_state d1') /\ o2 = CrashAfter))
            ))))
   | Recover =>
     (exists d1',
        exec impl u o1 d1 recover (Finished d1' tt) /\
        o2 = Cont /\
        (forall merged_disk,
           cached_log_reboot_rep merged_disk d1 ->
           cached_log_rep merged_disk d1')) \/
     (exists d1',
        exec impl u o1 d1 recover (Crashed d1') /\
        o2 = CrashBefore /\
        (forall merged_disk,
           cached_log_reboot_rep merged_disk d1 ->
           (cached_log_reboot_rep merged_disk d1' \/
           cached_log_crash_rep (During_Recovery merged_disk) d1' \/
           cached_log_crash_rep (After_Commit merged_disk) d1')))
   end.

  Definition refines_to (d1: state impl) (d2: state abs) :=
      cached_log_rep d2 d1.

  
  Definition refines_to_reboot (d1: state impl) (d2: state abs) :=
      cached_log_reboot_rep d2 d1 /\ (forall a vs, snd (snd d1) a = vs -> snd vs = nil).

  
  (** refinement preservation



  Set Nested Proofs Allowed.
  
  Lemma hashes_in_hashmap_subset:
    forall hl hm hm' h0,
      hashes_in_hashmap hm h0 hl ->
      subset hm hm' ->
      hashes_in_hashmap hm' h0 hl.
  Proof.
    induction hl; simpl; intros; cleanup; eauto.
    split; eauto.
    edestruct H0; eauto.
  Qed.
  
  Lemma exec_compiled_preserves_refinement_finished_core:
    forall T (p2: abs_core.(Core.operation) T) o1 s1 s1' r,
        (exists s2, refines_to s1 s2) ->
        impl.(exec) o1 s1 (compile T p2) (Finished s1' r)->
        (exists s2', refines_to s1' s2').
  Proof.
    intros; destruct p2; simpl in *; cleanup.
    {
      unfold read in *; repeat (invert_exec; simpl in *; cleanup);
      try solve [inversion H5; cleanup;
                 try inversion H7; cleanup;
                 eexists; intuition eauto ].
    }
    
    {
      unfold refines_to in *; cleanup.
      eapply write_finished in H0; eauto.
      simpl in *.
      split_ors; do 2 eexists; eauto.
    }
    admit.
  Admitted.

  Lemma exec_compiled_preserves_refinement_crashed_core:
    forall T (p2: abs_core.(Core.operation) T) o1 s1 s1',
        (exists s2, refines_to s1 s2) ->
        impl.(exec) o1 s1 (compile T p2) (Crashed s1') ->
        (exists s2', refines_to_crash s1' s2').
  Proof. Admitted.

  Lemma refines_to_then_refiines_to_crash_core:
    forall s1,
        (exists s2, refines_to s1 s2) ->
        (exists s2, refines_to_crash s1 s2).
  Proof.
    unfold refines_to, refines_to_crash,
    cached_log_rep, cached_log_crash_rep,
    log_rep, log_crash_rep; intros; cleanup.
    repeat (eexists; intuition eauto).
  Qed.
*)

  Definition LoggedDiskCoreRefinement := Build_CoreRefinement compile refines_to token_refines_to.
  Definition LoggedDiskRefinement := LiftRefinement (LoggedDiskLang data_length) LoggedDiskCoreRefinement.

  Notation "| p |" := (Op (LoggedDiskOperation data_length) p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op (LoggedDiskOperation data_length) p1) (fun x => p2))(right associativity, at level 60).

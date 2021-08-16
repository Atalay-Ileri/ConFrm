Require Import Framework TotalMem CachedDiskLayer LoggedDiskLayer Log RepImplications LogCache.
Require Import FSParameters FunctionalExtensionality Lia.
Close Scope predicate_scope.
Import ListNotations.

Local Definition impl_core := CachedDiskOperation.
Local Definition abs_core := LoggedDiskOperation log_length data_length.
Local Definition impl := CachedDiskLang.
Local Definition abs := LoggedDiskLang log_length data_length.

Definition compile T (p2: Core.operation abs_core T) : prog impl T.
 destruct p2.
 exact (read a).
 exact (write l l0).
 exact recover.
 exact (init l).
Defined.

Definition token_refines  T u (d1: state impl) (p: Core.operation abs_core T) get_reboot_state o1 o2 : Prop :=
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

   | Init l_av =>
     let l_a := map fst l_av in
     let l_v := map snd l_av in
     (exists d1',
        exec impl u o1 d1 (init l_av) (Finished d1' tt) /\
        o2 = Cont /\
        length l_a = length l_v /\
        cached_log_rep (total_mem_map fst (shift (Nat.add data_start) (upd_batch_set (snd (snd d1)) l_a l_v))) d1') \/
     (exists d1',
        exec impl u o1 d1 (init l_av) (Crashed d1') /\
        o2 = CrashBefore)
   end.

  Definition refines (d1: state impl) (d2: state abs) :=
      cached_log_rep d2 d1.
  
  Definition refines_reboot (d1: state impl) (d2: state abs) :=
      cached_log_reboot_rep d2 d1 /\ (forall a vs, snd (snd d1) a = vs -> snd vs = nil).

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
    forall T (p2: abs_core.(Core.operation) T) o1 s1 s1' r u,
        (exists s2, refines s1 s2) ->
        impl.(exec) u o1 s1 (compile T p2) (Finished s1' r)->
        (exists s2', refines s1' s2').
  Proof.
    intros; destruct p2; simpl in *; cleanup.
    {
      eapply read_finished in H0; eauto; cleanup; eauto.
    }
    {
      unfold refines in *; cleanup.
      eapply write_finished in H0; eauto.
      split_ors; cleanup; eauto.
    }
    {
      unfold refines, cached_log_rep in *; cleanup.
      eapply recover_finished in H0; eauto.
      unfold cached_log_reboot_rep;
      eexists; intuition eauto.      
      eapply log_rep_to_reboot_rep_same; eauto.
    }
    {
      eapply init_finished in H0; eauto.
    }
  Qed.

  Definition LoggedDiskCoreRefinement := Build_CoreRefinement compile refines refines_reboot token_refines exec_compiled_preserves_refinement_finished_core.
  Definition LoggedDiskRefinement := LiftRefinement (LoggedDiskLang log_length data_length) LoggedDiskCoreRefinement.

  Notation "| p |" := (Op (LoggedDiskOperation log_length data_length) p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op (LoggedDiskOperation log_length data_length) p1) (fun x => p2))(right associativity, at level 60).

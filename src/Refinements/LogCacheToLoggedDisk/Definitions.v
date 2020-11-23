Require Import Framework CachedDiskLayer LoggedDiskLayer Log LogCache.
Require Import FSParameters FunctionalExtensionality Lia.
Close Scope predicate_scope.
Import ListNotations.

Local Definition impl_core := CachedDiskOperation.
Local Definition abs_core := LoggedDiskOperation.
Local Definition impl := CachedDiskLang.
Local Definition abs := LoggedDiskLang.

Definition compile T (p2: Core.operation abs_core T) : prog impl T.
 destruct p2.
 exact (read a).
 exact (write l l0).
 exact recover.
Defined.

Definition token_refines_to T (d1: state impl) (p: Core.operation abs_core T) o1 o2 : Prop :=
   match p with
   | Read a =>
     (exists d1' r,
        exec impl o1 d1 (read a) (Finished d1' r) /\
        o2 = Cont /\
        d1' = d1) \/
     (exists d1',
        exec impl o1 d1 (read a) (Crashed d1') /\
        o2 = CrashBefore /\
        d1 = d1')
         
   | Write la lv =>
     (exists d1' r,
          exec impl o1 d1 (write la lv) (Finished d1' r) /\          
          o2 = Cont /\
          (exists s,
             cached_log_rep s d1 \/
             cached_log_rep (upd_batch_set s la lv) d1')
       ) \/
     (exists d1',
        (exec impl o1 d1 (write la lv) (Crashed d1') /\
         o2 = CrashBefore /\
         d1' = d1) \/
        (exec impl o1 d1 (write la lv) (Crashed d1') /\
         o2 = CrashAfter /\
         d1' <> d1)
     )
   | Recover =>
     (exists d1',
        exec impl o1 d1 recover (Finished d1' tt) /\
        o2 = Cont /\
        d1' = d1) \/
     (exists d1',
        exec impl o1 d1 recover (Crashed d1') /\
        o2 = CrashBefore /\
        d1 = d1')
   end.

  Definition refines_to (d1: state impl) (d2: state abs) :=
    exists d2',
      cached_log_rep d2' d1 /\
      d2 = mem_map fst d2'.

  
  Definition refines_to_reboot (d1: state impl) (d2: state abs) :=
    exists d2',
      cached_log_reboot_rep d2' d1 /\
      d2 = mem_map fst d2'.

  
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
  Definition LoggedDiskRefinement := LiftRefinement LoggedDiskLang LoggedDiskCoreRefinement.

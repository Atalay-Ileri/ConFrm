Require Import Framework CachedDiskLayer LoggedDiskLayer Log LogCache.
Require Import FSParameters FunctionalExtensionality Lia.
Close Scope predicate_scope.
Import ListNotations.

Local Definition low_op := CachedDiskOperation.
Local Definition high_op := LoggedDiskOperation.
Local Definition low := CachedDiskLang.
Local Definition high := LoggedDiskLang.

Definition compile T (p2: Operation.prog high_op T) : prog low T.
 destruct p2.
 exact (read a).
 exact (write l l0).
 exact recover.
Defined.

Definition oracle_refines_to T (d1: state low) (p: Operation.prog high_op T) o1 o2 : Prop :=
   match p with
   | Read a =>
     (exists d1' r,
        exec low o1 d1 (read a) (Finished d1' r) /\
        o2 = [Cont] /\
        d1' = d1) \/
     (exists d1',
        exec low o1 d1 (read a) (Crashed d1') /\
        o2 = [CrashBefore] /\
        d1 = d1')
         
   | Write la lv =>
     (exists d1' r,
          exec low o1 d1 (write la lv) (Finished d1' r) /\          
          o2 = [Cont] /\
          (forall s,
             (exists log_state, cached_log_rep s log_state d1) ->
             (exists log_state, cached_log_rep (write_all s la lv) log_state d1'))
       ) \/
     (exists d1',
        (exec low o1 d1 (write la lv) (Crashed d1') /\
         o2 = [CrashBefore] /\
         d1' = d1) \/
        (exec low o1 d1 (write la lv) (Crashed d1') /\
         o2 = [CrashAfter] /\
         d1' <> d1)
     )
   | Recover =>
     (exists d1',
        exec low o1 d1 recover (Finished d1' tt) /\
        o2 = [Cont] /\
        d1' = d1) \/
     (exists d1',
        exec low o1 d1 recover (Crashed d1') /\
        o2 = [CrashBefore] /\
        d1 = d1')
   end.

  Definition refines_to (d1: state low) (d2: state high) :=
    exists d2' log_state,
      cached_log_rep d2' log_state d1 /\
      d2 = mem_map fst d2'.


  (** refinement preservation **)
    Lemma nil_or_app:
    forall T (l: list T),
      l = [] \/ exists t l', l = l'++[t].
    intros.
    eapply rev_ind with (P:= fun l => l = [] \/ (exists (t : T) (l' : list T), l = l' ++ [t])); simpl; eauto.
  Qed.

  Lemma upd_batch_app:
    forall A AEQ V l1 l2 l3 l4 (m: @mem A AEQ V),
      length l1 = length l3 ->
      upd_batch m (l1++l2) (l3++l4) = upd_batch (upd_batch m l1 l3) l2 l4.
  Proof.
    induction l1; simpl; intros; eauto;
    destruct l3; simpl in *; try lia; eauto.
  Qed.

  Lemma mem_map_upd_comm:
    forall A AEQ V1 V2 (m: @mem A AEQ V1) a v (f: V1 -> V2),
      mem_map f (upd m a v) = upd (mem_map f m) a (f v).
  Proof.
    intros. unfold mem_map.
    extensionality x.
    destruct (AEQ a x); subst;
    [ repeat rewrite upd_eq; eauto
    | repeat rewrite upd_ne; eauto].
  Qed.

  Definition sumbool_agree {A B C D} (eq1: {A}+{B})(eq2: {C}+{D}):=
    if eq1 then
      if eq2 then
        True
      else
        False
    else
      if eq2 then
        False
      else
        True.

  Lemma upd_shift_comm:
    forall A AEQ V (m: @mem A AEQ V) (f: A -> A) a v,
      (forall x y, sumbool_agree (AEQ x y) (AEQ (f x) (f y))) ->
      upd (shift f m) a v = shift f (upd m (f a) v).
  Proof.
    unfold sumbool_agree; intros; simpl.
    extensionality x; simpl.
    specialize (H a x).
    unfold shift.
    destruct (AEQ a x);
    destruct (AEQ (f a) (f x)); subst; intuition;
    [ repeat rewrite upd_eq
    | repeat rewrite upd_ne]; eauto.
  Qed.

  Lemma upd_merge_set_cons_comm:
    forall A AEQ V (m1: @mem A AEQ V) m2 a v0 v1 vl,
      upd (merge_set m1 m2) a (v0, v1::vl) = merge_set (upd m1 a v0) (upd m2 a (v1, vl)).
  Proof.
    unfold merge_set; intros.
    extensionality x; simpl.
    destruct (AEQ a x); subst; intuition;
    [ repeat rewrite upd_eq
    | repeat rewrite upd_ne]; eauto.
  Qed.

  Lemma upd_batch_write_all_mem_map:
    forall V l l0 (m: @mem addr addr_dec (V * list V)),
      (forall a, In a l -> m a <> None) ->
      upd_batch (mem_map fst m) l l0 = mem_map fst (write_all m l l0).
  Proof.
    induction l; simpl; intros; eauto.
    destruct l0; simpl; eauto.
    specialize (H a) as Hx.
    destruct (m a); simpl in *; eauto.
    erewrite <- IHl.
    rewrite mem_map_upd_comm; simpl; eauto.
    intros.
    destruct (addr_dec a a0);
    [ rewrite upd_eq
    | rewrite upd_ne ]; eauto; congruence.

    exfalso; apply Hx; eauto.
  Qed.    

  Lemma write_all_shift_comm:
    forall V l l0 (m: @mem _ _ (V * list V)) f,
      (forall x y, sumbool_agree (addr_dec x y) (addr_dec (f x) (f y))) ->
      write_all (shift f m) l l0 =
      shift f (write_all m (map f l) l0).
  Proof.
    induction l; simpl; intros; eauto.
    destruct l0; eauto.
    unfold shift at 1.
    destruct (m (f a)); eauto.
    rewrite <- IHl; eauto.
    rewrite upd_shift_comm; eauto.
  Qed.

  Lemma write_all_app:
    forall V l1 l2 l3 l4 (m: @mem _ _ (set V)),
      length l1 = length l3 ->
      (forall a, In a l1 -> m a <> None) ->
      write_all m (l1++l2) (l3++l4) = write_all (write_all m l1 l3) l2 l4.
  Proof.
    induction l1; simpl; intros; cleanup; eauto.
    destruct l3; simpl in *; try lia. 
    destruct_fresh (m a); simpl; eauto.
    rewrite IHl1; eauto.
    intros.
    destruct (addr_dec a a0);
    [ repeat rewrite upd_eq in *
    | repeat rewrite upd_ne in *]; eauto; congruence.
    exfalso; eapply H0; intuition cleanup.
  Qed.

  
  Lemma merge_set_some_l:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a v,
      m1 a = Some v ->
      m2 a <> None ->
      exists vs, merge_set m1 m2 a = Some vs /\
            fst vs = v.
  Proof.
    unfold merge_set; simpl; intros.
    cleanup.
    destruct (m2 a); try congruence; eauto.    
  Qed.
  
  Lemma merge_set_some_r:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a,
      m1 a = None ->
      merge_set m1 m2 a = m2 a.
  Proof.
    unfold merge_set; simpl; intros.
    cleanup; eauto.
  Qed.

  
  Lemma cached_log_rep_cache_read :
    forall s2 s1 a v log_state,
      cached_log_rep s2 log_state s1 ->
      fst s1 (data_start + a) = Some v ->
      Disk.read s2 a = Some v.
  Proof.
    unfold cached_log_rep, Disk.read; intros.
    cleanup; unfold shift; simpl in *.
    eapply merge_set_some_l in H0; eauto; cleanup.
    rewrite H0; eauto.
    eapply H1.
    congruence.
  Qed.
  
  Lemma cached_log_rep_disk_read :
    forall s2 s1 a log_state,
      cached_log_rep s2 log_state s1 ->
      fst s1 (data_start + a) = None ->
      Disk.read s2 a = Disk.read (snd (snd s1)) (data_start + a).
  Proof.
    unfold cached_log_rep, Disk.read; intros.
    unfold shift in *; simpl; cleanup.
    erewrite merge_set_some_r; eauto.
  Qed.

  Lemma mem_map_fst_some_elim:
      forall A AEQ V1 V2 (m: @mem A AEQ (V1 * V2)) a v vs,
        m a = Some (v, vs) ->
        mem_map fst m a = Some v.
  Proof.
    intros.
    unfold mem_map; simpl; cleanup; eauto.
  Qed.

  Lemma mem_map_fst_some_exists:
      forall A AEQ V1 V2 (m: @mem A AEQ (V1 * V2)) a v,
        mem_map fst m a = Some v ->
        exists vs, m a = Some (v, vs).
  Proof.
    intros.
    unfold mem_map in *; simpl; cleanup; eauto.
    destruct p; simpl in *; eauto.
  Qed.


  Lemma upd_batch_not_in_none:
    forall A AEQ V l l' (m: @mem A AEQ V) a,
      m a = None ->
      ~ In a l ->
      length l = length l' ->
      upd_batch m l l' a = None.
  Proof.
    induction l; simpl; intros; eauto.
    destruct l'; simpl in *; cleanup; try lia.
    destruct (AEQ a a0); subst.
    exfalso; apply H0; intuition.
    apply IHl.
    rewrite upd_ne; eauto.
    intros Hx; apply H0; eauto.
    lia.
  Qed.
  
  Lemma write_all_merge_set:
    forall V l l0 (m: @mem _ _ (set V)),
      NoDup l ->
      length l = length l0 ->
      (forall a : addr, In a l -> m a <> None) ->
      write_all m l l0 =
      merge_set (upd_batch empty_mem l l0) m.
  Proof.
    intros V l.
    apply rev_ind with
        (P:= fun l => forall (l0 : list V) (m : mem),
                     NoDup l ->
                     length l = length l0 ->
                     (forall a : addr, In a l -> m a <> None) ->
                     write_all m l l0 = merge_set (upd_batch empty_mem l l0) m).
    - simpl; intros; eauto.

    - simpl; intros.
      destruct (nil_or_app _ l1); subst; simpl.
      destruct (l0 ++ [x]); simpl; eauto.
      cleanup; subst.
      repeat rewrite app_length in H1; simpl in *.
      apply NoDup_app_l in H0 as Hx.
      rewrite upd_batch_app; simpl; try lia.
      rewrite write_all_app; try lia.
      rewrite H; eauto; try lia.
      simpl.
      destruct_fresh (merge_set (upd_batch empty_mem l0 x1) m x).
      setoid_rewrite upd_merge_set_cons_comm.
      setoid_rewrite upd_nop at 2; eauto.
      destruct p; simpl.
      rewrite merge_set_some_r in D; eauto.      
      eapply upd_batch_not_in_none; eauto.
      apply NoDup_app_comm in H0; simpl in *.
      inversion H0; eauto.
      lia.
      rewrite merge_set_some_r in D; eauto.
      exfalso; eapply H2; eauto.
      apply in_app_iff; simpl; eauto.

      eapply upd_batch_not_in_none; eauto.
      apply NoDup_app_comm in H0; simpl in *.
      inversion H0; eauto.
      lia.
      intros; eapply H2; eauto.
  Qed.

  Lemma refines_to_upd_batch:
    forall l l0 s1 s2,
      NoDup l ->
      length l = length l0 ->
      refines_to s1 s2 ->
      exists s1', refines_to s1' (upd_batch s2 l l0).
  Proof.
    intros.
    unfold refines_to in *; cleanup.
    eexists; exists (write_all x l l0).
    exists x0.
    rewrite upd_batch_write_all_mem_map.
    split; eauto.
  Abort.

  (*
    Lemma cached_log_rep_upd_cons:
      forall l l0 F d s log_state,
        cached_log_rep F d s log_state ->
        NoDup l ->
        length l = length l0 ->
        exists s', cached_log_rep F (write_all d l l0) s' log_state.
    Proof.
      intros. 
      unfold cached_log_rep in H; cleanup.
      rewrite <- H in *.
      unfold cached_log_rep; simpl.
      destruct s, s0; simpl in *.
      do 3 eexists.
      repeat split.
      
      5: rewrite write_all_shift_comm, write_all_merge_set.
      instantiate (2:= (upd_batch s (map (Init.Nat.add data_start) l) l0, (s0, s1))).
      all: simpl; eauto.
      
      
      eauto.
      
      cleanup; eauto.
      
      unfold merge_set at 1.
      destruct_fresh (m1 a).
      destruct_fresh (m2 a); simpl.
      unfold upd_disk.
      setoid_rewrite upd_merge_set_cons_comm.
      rewrite IHl.
      Search merge_set.
      destruct (m (f a)); eauto.
      rewrite <- IHl; eauto.
      unfold upd_disk;
      rewrite upd_shift_comm; eauto.
    Qed.
    
    rewrite write_all_merge_set.
    
    intros.
    unfold sumbool_agree.
    Print Log.txn.
    exists ({ record : Log.txn_record;  addr_blocks : list value;  data_blocks : list value }++x0).
    unfold 
      do 4 eexists.        
    repeat split.
    4: eauto.

    
    eauto.

  Abort.


  
  eapply rev_ind with (P:= fun l =>
                             forall (l0 : list value) (s1 : state Definitions.low) (s2 : state Definitions.high),
                               length l = length l0 ->
                               refines_to s1 s2 -> exists s1' : state Definitions.low, refines_to s1' (upd_batch s2 l l0)); simpl;
  unfold refines_to; intros; eauto.
  destruct (nil_or_app _ l1); subst;
  simpl in *; eauto; cleanup.
  do 4 eexists; intuition eauto.
  repeat rewrite app_length in *; simpl in *.
  
  rewrite upd_batch_app by lia.
  edestruct H; eauto; cleanup.
  instantiate (1:=x1); lia.
  rewrite H3 in *; clear H3.
  simpl.
  destruct_fresh (x7 x).
  {
    eexists.
    exists x6, (upd x7 x (x0, fst p::snd p)).
    eexists.
    setoid_rewrite mem_map_upd_comm; split; eauto.
  Abort.
  

  Lemma sp_write_batch_to_cache_ok:
    forall l l0 t s' F log_state hdr txns m,
      NoDup l ->
      length l = length l0 ->
      
      strongest_postcondition CachedDiskLang (LogCache.write_batch_to_cache l l0)
        (fun o s =>
           m = fst s /\
           (forall a, In a l -> snd (snd s) a <> None ) /\
           addrs_match (fst s) (snd (snd s)) /\
           (Log.log_rep log_state hdr txns (fst (snd s)) * F)%predicate (snd (snd s))) t s' ->
      
      fst s' = upd_batch m l l0 /\
      addrs_match (fst s') (snd (snd s')) /\
      (Log.log_rep log_state hdr txns (fst (snd s')) * F)%predicate (snd (snd s')).
  Proof.
    induction l; simpl; intros;
    cleanup; simpl in *; eauto; try lia.

    cleanup.
    inversion H; cleanup.
    apply sp_exists_extract in H1; cleanup.
    edestruct IHl; eauto; try lia.
    
    eapply sp_impl; eauto.
    simpl; intros; cleanup; intuition eauto.
    destruct s; simpl in *; cleanup.
    unfold addrs_match; intros.
    destruct (addr_dec a a0); subst;
    [ rewrite upd_eq in H2
    | rewrite upd_ne in H2 ]; eauto.
  Qed.

  Lemma and_exists:
    forall T (P: T -> Prop) (Q: Prop),
      (exists t, P t) /\ Q -> (exists t, P t /\ Q).
  Proof.
    firstorder.
  Qed.
  *)

  Set Nested Proofs Allowed.
   

  Lemma refines_to_subset_crypto:
    forall cached_crypto_disk cached_crypto_disk' logged_disk,
      let cache := fst cached_crypto_disk in
      let crypto_disk := snd cached_crypto_disk in
      let keylist := fst (fst (fst crypto_disk)) in
      let encmap := snd (fst (fst crypto_disk)) in
      let hashmap := snd (fst crypto_disk) in
      let disk := snd crypto_disk in
      
      let cache' := fst cached_crypto_disk' in
      let crypto_disk' := snd cached_crypto_disk' in
      let keylist' := fst (fst (fst crypto_disk')) in
      let encmap' := snd (fst (fst crypto_disk')) in
      let hashmap' := snd (fst crypto_disk') in
      let disk' := snd crypto_disk' in
      
      refines_to cached_crypto_disk logged_disk ->
      cache = cache' ->
      disk = disk' ->
      incl keylist keylist' ->
      subset encmap encmap' ->
      subset hashmap hashmap' ->
      refines_to cached_crypto_disk' logged_disk.
  Proof.
    unfold refines_to, cached_log_rep; intros;
    simpl in *; cleanup.
    do 3 eexists; intuition eauto.
    setoid_rewrite <- H0;
    setoid_rewrite <- H1;
    setoid_rewrite H; eauto.
    unfold log_rep, log_rep_inner in *; cleanup_no_match.
    
    do 2 eexists; intuition eauto.
    setoid_rewrite <- H1; eauto.

    do 2 eexists; intuition eauto.
    setoid_rewrite <- e; eauto.

    (** Weird rewrite errors here **)
    admit.
    admit.

    (** TODO: prove a lemma for this **)
    admit.
    admit.
    
    setoid_rewrite <- H1; eauto.
  Admitted.
  
  Lemma exec_compiled_preserves_refinement:
    forall T (p2: high_op.(Operation.prog) T) o1 s1 ret,
        (exists s2, refines_to s1 s2) ->
        low.(exec) o1 s1 (compile T p2) ret ->
        (exists s2', refines_to (extract_state ret) s2').
  Proof.
    intros; destruct p2; simpl in *; cleanup.
    {
      destruct ret.
      {
        unfold read in *; repeat (invert_exec; simpl in *; cleanup);
        try solve [inversion H5; cleanup;
                   try inversion H7; cleanup;
                   eexists; intuition eauto ].
      }
      {
        unfold read in *;
        repeat (try split_ors; cleanup;
                invert_exec;
                simpl in *; cleanup);
        try solve [
              inversion H5; cleanup;
              try inversion H6; cleanup;
              eexists; intuition eauto].
      }
    }
    {
      destruct ret.
      {
        {
          unfold write in *; simpl in *.
          (** TODO: Speed this up **)
          repeat (cleanup; invert_exec;
                  simpl in *; cleanup; intuition).
          repeat
            match goal with
            |[H: DiskLayer.exec' _ _ _ _ |- _ ] =>
             inversion H; clear H; cleanup
            end.

          repeat
            match goal with
            | [H: context [ fst ?x ] |- _ ] =>
              destruct x; simpl in *
            | [H: context [ snd ?x ] |- _ ] =>
              destruct x; simpl in *
            end; cleanup_no_match.

          repeat
            match goal with
            | [H: exec _ _ _ (BatchOperations.hash_all _ _) _ |- _ ] =>
              eapply BatchOperations.hash_all_finished in H
            | [H: exec _ _ _ (BatchOperations.read_consecutive _ _) _ |- _ ] =>
              eapply BatchOperations.read_consecutive_finished in H
            | [H: exec _ _ _ (BatchOperations.write_consecutive _ _) _ |- _ ] =>
              unfold BatchOperations.write_consecutive in H;
              eapply BatchOperations.write_batch_finished in H
            | [H: exec _ _ _ (BatchOperations.encrypt_all _ _) _ |- _ ] =>
              eapply BatchOperations.encrypt_all_finished in H
            end.
          
          repeat
            match goal with
            | [H: exec _ _ _ (BatchOperations.hash_all _ _) _ |- _ ] =>
              eapply BatchOperations.hash_all_finished in H
            | [H: exec _ _ _ (BatchOperations.read_consecutive _ _) _ |- _ ] =>
              eapply BatchOperations.read_consecutive_finished in H
            | [H: exec _ _ _ (BatchOperations.write_consecutive _ _) _ |- _ ] =>
              unfold BatchOperations.write_consecutive in H;
              eapply BatchOperations.write_batch_finished in H
            | [H: exec _ _ _ (BatchOperations.encrypt_all _ _) _ |- _ ] =>
              eapply BatchOperations.encrypt_all_finished in H
            end.
          
          match goal with
          | [H: exec _ _ _ (LogCache.write_batch_to_cache _ _) _ |- _ ] =>
            eapply LogCache.write_batch_to_cache_finished in H
          end; try logic_clean.

          match goal with
          | [H: exec _ _ _ (Log.apply_txns _ _) _ |- _ ] =>
            eapply Log.apply_txns_finished in H
          end; try logic_clean.

          inversion H19; clear H19; subst; sigT_eq.

          repeat
            match goal with
            | [H: context [ fst ?x ] |- _ ] =>
              destruct x; simpl in *
            | [H: context [ snd ?x ] |- _ ] =>
              destruct x; simpl in *
            end; cleanup_no_match.

          eapply refines_to_subset_crypto with (cached_crypto_disk' := (s1, (x17 :: fst (fst s),
      upd_batch (snd (fst s)) (map (encrypt x17) (addr_list_to_blocks (map (Nat.add data_start) l) ++ l0))
        (map (fun v2 : value => (x17, v2)) (addr_list_to_blocks (map (Nat.add data_start) l) ++ l0)),
      upd_batch (snd s)
        (rolling_hash_list (cur_hash (decode_header v0))
           (map (encrypt x17) (addr_list_to_blocks (map (Nat.add data_start) l) ++ l0)))
        match map (encrypt x17) (addr_list_to_blocks (map (Nat.add data_start) l) ++ l0) with
        | [] => []
        | y :: tl' =>
            (cur_hash (decode_header v0), y)
            :: combine
                 (rolling_hash_list (cur_hash (decode_header v0))
                    (map (encrypt x17) (addr_list_to_blocks (map (Nat.add data_start) l) ++ l0))) tl'
        end, s17))) in H; simpl; try reflexivity.

          XXX HERE
              
          all: admit.
        }
      }
      { admit. }
    }
    {
      destruct ret.
      {
        unfold recover in *; repeat (invert_exec; simpl in *; cleanup).

           repeat
            match goal with
            |[H: DiskLayer.exec' _ _ _ _ |- _ ] =>
             inversion H; clear H; cleanup
            end.

           repeat
            match goal with
            | [H: exec _ _ _ (BatchOperations.hash_all _ _) _ |- _ ] =>
              eapply BatchOperations.hash_all_finished in H
            | [H: exec _ _ _ (BatchOperations.read_consecutive _ _) _ |- _ ] =>
              eapply BatchOperations.read_consecutive_finished in H
            | [H: exec _ _ _ (BatchOperations.write_consecutive _ _) _ |- _ ] =>
              unfold BatchOperations.write_consecutive in H;
              eapply BatchOperations.write_batch_finished in H
            | [H: exec _ _ _ (BatchOperations.encrypt_all _ _) _ |- _ ] =>
              eapply BatchOperations.encrypt_all_finished in H
            end.

        repeat
          match goal with
          | [H: context [ fst ?x ] |- _ ] =>
            destruct x; simpl in *
          | [H: context [ snd ?x ] |- _ ] =>
            destruct x; simpl in *
          end; cleanup_no_match.

        

        XXX

        subst.
        intuition subst.

        repeat
          match goal with
          |[H: DiskLayer.exec' _ _ _ _ |- _ ] =>
           inversion H; clear H; cleanup
          end.
          
        try solve [inversion H5; cleanup;
                   try inversion H7; cleanup;
                   eexists; intuition eauto ].
      }
      {
        unfold read in *;
        repeat (try split_ors; cleanup;
                invert_exec;
                simpl in *; cleanup);
        try solve [
              inversion H5; cleanup;
              try inversion H6; cleanup;
              eexists; intuition eauto].
      }
    }
    
          
          Search exec.
          
          XXX HERE XXX
          try solve [inversion H5; cleanup;
                   try inversion H7; cleanup;
                   eexists; intuition eauto ].
      }
      {
        unfold read in *;
        repeat (try split_ors; cleanup;
                invert_exec;
                simpl in *; cleanup);
        try solve [
              inversion H5; cleanup;
              try inversion H6; cleanup;
              eexists; intuition eauto].
      }
        eapply exec_to_sp with (P := fun o s => refines_to s x /\ s = s1 /\ o = o1) in H0; eauto.
        unfold write in *; simpl in *;
        repeat (cleanup; simpl in *).

                
                
                 repeat (match goal with
                        | [H: strongest_postcondition _ _ _ _ _ |- _ ] =>
                          eapply sp_to_exec in H; cleanup
                        end).
                 simpl in *.

                 repeat invert_exec.
                 Search exec.
                 
                2: {
                  intuition eauto.
                  apply H1.

   Set Nested Proofs Allowed. 
   eapply sp_bind in H0.
                
                eauto;
                do 4 eexists; intuition eauto.
                
      eapply exec_to_scp with (P := fun o s' => refines_to s' x /\ s' = s1 /\ o = o1) in H0; eauto.
      simpl in *; repeat (try split_ors; cleanup; simpl in *); eauto;
      inversion H0; cleanup; eauto;
      do 4 eexists; intuition eauto.
    
                         {

        Lemma sp_write_ok:
          forall l l0 t s',
            strongest_postcondition CachedDiskLang (write l l0) (fun o s => exists s2, refines_to s s2) t s' ->
            exists s2' : state', refines_to s' s2'.
        Proof.
          unfold write; intros.
          repeat cleanup;
          try solve [ simpl in *; cleanup; eauto].
          unfold refines_to, cached_log_rep in *.
          repeat (apply sp_exists_extract in H; cleanup).
          eapply sp_impl in H; [|simpl; intros o s Hx; eapply and_exists in Hx; apply Hx].
          repeat (apply sp_exists_extract in H; cleanup).
          eapply sp_impl in H; [|simpl; intros o s Hx; eapply and_exists in Hx; apply Hx].
          repeat (apply sp_exists_extract in H; cleanup).
          
          Opaque Log.commit.
          simpl in *;
          cleanup; simpl in *.
          apply sp_lift2 in H.
          simpl in H.
          
          eapply sp_impl in H.
          eapply sp_write_batch_to_cache_ok in H; eauto.
          cleanup.

          
          
             
            rewrite upd_batch_upd_comm.
            eapply IHl; eauto; try lia.
            eapply sp_impl; eauto.
            simpl; intros; cleanup; eauto.
            destruct s; simpl in *; cleanup.

              Lemma cached_log_rep_cache_upd:
                forall d a v p x1 s0 F log_state,
                d a = Some p ->
                cached_log_rep F d (x1, s0) log_state -> 
                cached_log_rep F (upd d a (v, fst p :: snd p)) (upd x1 a v, s0) log_state.
              Proof.
                unfold cached_log_rep; simpl; intros; cleanup.
                repeat split; eauto.

            Lemma refines_to_upd:
              forall s s0 s2 a v,
              refines_to (s, s0) s2 ->
              exists s2', refines_to (upd s a v, s0) s2'.
            Proof.
              unfold refines_to in *; simpl; intros; cleanup.
              unfold cached_log_rep in *; simpl in *; cleanup.
              do 4 eexists; repeat split.
              do 2 eexists; repeat split.
              instantiate {1:= }
            simpl in *; cleanup; try lia.
            
          Search LogCache.write_batch_to_cache.
          2: {
            
        
        eapply A.
        eapply exec_to_sp; eauto.
        
        assume (A:(forall s',
                     strongest_crash_postcondition CachedDiskLang (write l l0) (fun o s => exists s2, refines_to s s2) s' ->
                     exists s2' : state', refines_to s' s2')).
        eapply A.
        eapply exec_to_scp; eauto.
      }
    }

    {
      destruct ret.
      eapply exec_to_sp with (P := fun o s => refines_to s x /\ s = s1) in H0; unfold refines_to in *; eauto.
      simpl in *; cleanup; simpl; eauto; do 4 eexists; intuition eauto.
      eapply exec_to_scp with (P := fun o s => refines_to s x /\ s = s1) in H0; unfold refines_to in *; eauto.
      simpl in *; cleanup; simpl; eauto; do 4 eexists; intuition eauto.
    }
    
    {
      invert_exec; eauto.
      split_ors; cleanup; eauto.
      eapply IHp2 in H1; eauto.
    }
Admitted.

(*                          
Lemma exec_preserves_refinement:
  exec_preserves_refinement refinement.
Proof.
  unfold exec_preserves_refinement; induction p; simpl; intros.
  destruct ret.
  {
    eapply exec_to_sp with (P := fun o s => exists x, refines_to x s) in H0; eauto.
    destruct p; simpl in *; cleanup; eauto.
    split_ors; cleanup; eauto.
    admit. (* Doable *)
  }
  {
    eapply exec_to_scp with (P := fun o s => exists x, refines_to x s) in H0; eauto.
    destruct p; simpl in *; cleanup; eauto.
    split_ors; cleanup; eauto.
    admit. (* Doable *)
  }
  
  destruct ret.
  {
    eapply exec_to_sp with (P := fun o s => exists x, refines_to x s) in H0; eauto.
    simpl in *; cleanup; eauto.
  }
  {
    eapply exec_to_scp with (P := fun o s => exists x, refines_to x s) in H0; eauto.
  }
  
  invert_exec.
  eapply IHp in H1; eauto; simpl in *.
  split_ors; cleanup; eauto.
  eapply IHp in H1; eauto; simpl in *.
Admitted.
*)

  Definition LoggedDiskOperationRefinement := Build_OperationRefinement compile refines_to oracle_refines_to.
  Definition LoggedDiskRefinement := LiftRefinement LoggedDiskLang LoggedDiskOperationRefinement.

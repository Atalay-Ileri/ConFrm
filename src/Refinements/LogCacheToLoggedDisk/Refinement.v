Require Import Framework FSParameters CachedDiskLayer.
Require Import LogCache LoggedDiskLayer LogCacheToLoggedDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Omega.

Set Nested Proofs Allowed.

Notation "'low'" := CachedDiskLang.
Notation "'high'" := LoggedDiskLang.
Notation "'refinement'" := LoggedDiskRefinement.

Axiom excluded_middle_dec: forall P: Prop, {P}+{~P}.

Section LoggedDiskBisimulation.

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
    destruct l3; simpl in *; try omega; eauto.
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
    unfold upd_disk.
    rewrite mem_map_upd_comm; simpl; eauto.
    intros.
    unfold upd_disk;
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
    unfold upd_disk;
    rewrite upd_shift_comm; eauto.
  Qed.

  Lemma write_all_app:
    forall V l1 l2 l3 l4 (m: @mem _ _ (set V)),
      length l1 = length l3 ->
      (forall a, In a l1 -> m a <> None) ->
      write_all m (l1++l2) (l3++l4) = write_all (write_all m l1 l3) l2 l4.
  Proof.
    induction l1; simpl; intros; cleanup; eauto.
    destruct l3; simpl in *; try omega. 
    destruct_fresh (m a); simpl; eauto.
    rewrite IHl1; eauto.
    intros.
    unfold upd_disk.
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
    forall F s2 s1 a v log_state,
      cached_log_rep F s2 s1 log_state ->
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
    forall F s2 s1 a log_state,
      cached_log_rep F s2 s1 log_state ->
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
    destruct l'; simpl in *; cleanup; try omega.
    destruct (AEQ a a0); subst.
    exfalso; apply H0; intuition.
    apply IHl.
    rewrite upd_ne; eauto.
    intros Hx; apply H0; eauto.
    omega.
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
      rewrite upd_batch_app; simpl; try omega.
      rewrite write_all_app; try omega.
      rewrite H; eauto; try omega.
      simpl.
      destruct_fresh (merge_set (upd_batch empty_mem l0 x1) m x).
      unfold upd_disk; setoid_rewrite upd_merge_set_cons_comm.
      setoid_rewrite upd_nop at 2; eauto.
      destruct p; simpl.
      rewrite merge_set_some_r in D; eauto.      
      eapply upd_batch_not_in_none; eauto.
      apply NoDup_app_comm in H0; simpl in *.
      inversion H0; eauto.
      omega.
      rewrite merge_set_some_r in D; eauto.
      exfalso; eapply H2; eauto.
      apply in_app_iff; simpl; eauto.

      eapply upd_batch_not_in_none; eauto.
      apply NoDup_app_comm in H0; simpl in *.
      inversion H0; eauto.
      omega.
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
    eexists; exists x, (write_all x0 l l0).
    exists x1.
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
  
  rewrite upd_batch_app by omega.
  edestruct H; eauto; cleanup.
  instantiate (1:=x1); omega.
  rewrite H3 in *; clear H3.
  simpl.
  destruct_fresh (x7 x).
  {
    eexists.
    exists x6, (upd x7 x (x0, fst p::snd p)).
    eexists.
    setoid_rewrite mem_map_upd_comm; split; eauto.
  Abort.
  *)

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
    cleanup; simpl in *; eauto; try omega.

    cleanup.
    inversion H; cleanup.
    apply sp_exists_extract in H1; cleanup.
    edestruct IHl; eauto; try omega.
    
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
  
  Lemma exec_compiled_preserves_refinement:
    exec_compiled_preserves_refinement refinement.
  Proof.
    unfold exec_compiled_preserves_refinement.
    induction p2; simpl in *; intros; cleanup.
    {
      destruct p; simpl in *.
      {
        destruct ret.
        eapply exec_to_sp with (P := fun o s => refines_to s x /\ s = s1) in H0; unfold refines_to in *; eauto.
        simpl in *;
        repeat (cleanup; simpl in *); eauto;
                do 4 eexists; intuition eauto.
                
        eapply exec_to_scp with (P := fun o s' => refines_to s' x /\ s' = s1) in H0; unfold refines_to in *; eauto.
        simpl in *; repeat (try split_ors; cleanup; simpl in *); eauto;
        inversion H0; cleanup; eauto;
        do 4 eexists; intuition eauto.
      }
      {
        destruct ret.

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
            eapply IHl; eauto; try omega.
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
            simpl in *; cleanup; tryomega.
            
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

Lemma wp_low_to_high_read :
  forall a,
    wp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
Proof.
  unfold wp_low_to_high_prog', refines_to; simpl; intros; cleanup.
  unfold refines_to in *; simpl; intros; cleanup.
  split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
  eexists; intuition eauto.
  eapply exec_to_sp with (P := fun o s => refines_to s (mem_map fst x2) /\ s = s1) in H2; unfold refines_to in *; eauto.
  simpl in *.
  cleanup.
  {        
    cleanup; simpl in *; cleanup; eauto;
    eexists; intuition eauto.
    simpl in *.
    eapply cached_log_rep_cache_read; eauto.
  }

  cleanup; simpl in *.
  {
    cleanup.
    do 4 eexists; split; eauto; simpl in *.
  }
  {
    unfold refines_to in *; cleanup.
    split_ors; cleanup;
    eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eexists; intuition eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s (mem_map fst x2) /\ s = s1) in H2; unfold refines_to in *; eauto;
    try solve [do 3 eexists; eauto].
    simpl in *.
    cleanup.
    destruct x; simpl in *; cleanup; eauto; intuition eauto.
    eexists; intuition eauto.
    eapply cached_log_rep_disk_read in D; eauto.
    unfold Disk.read in *; cleanup; eauto.
    destruct p; simpl in *; cleanup; eauto.
    eapply mem_map_fst_some_elim; eauto.
    setoid_rewrite H6 in D1; congruence.
  }
Qed.

Lemma wp_high_to_low_read :
  forall a,
    wp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
Proof.
  unfold wp_high_to_low_prog'; intros; cleanup.
  simpl in H; cleanup.
  simpl in H1; cleanup; split_ors; cleanup.
  repeat invert_exec.
  eapply exec_to_wp; eauto.

  eapply exec_to_sp with (P := fun o s => refines_to s s2' /\ s = s1) in H; eauto.

  unfold read in *; simpl in *.
  cleanup; simpl in *.
  
  destruct x; simpl in *; split; eauto.
  -  unfold refines_to in *; cleanup.
    eapply mem_map_fst_some_exists in H4; cleanup.
    eapply cached_log_rep_cache_read in H; eauto; cleanup.
    unfold Disk.read in *; cleanup; simpl in *.
    congruence.

   - cleanup.
    unfold refines_to in *; cleanup.
    rewrite <- H1 in H4.
    eapply mem_map_fst_some_exists in H4; cleanup.
    eapply cached_log_rep_disk_read in H0; eauto; cleanup.
    unfold Disk.read in *; simpl in *; cleanup; eauto.
Qed.


Lemma wcp_low_to_high_read :
  forall a,
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
Proof.
  unfold wcp_low_to_high_prog'; simpl; intros; cleanup.
  split_ors; cleanup. eapply exec_deterministic_wrt_oracle in H2; eauto; cleanup.
  eapply exec_deterministic_wrt_oracle in H; eauto; cleanup.
  eexists; repeat split; eauto.
Qed.
          
Lemma wcp_high_to_low_read :
  forall a,
    wcp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
Proof.
  unfold wcp_high_to_low_prog'; intros; cleanup.
  simpl in H, H1; intros; cleanup.
  split_ors; cleanup.
  repeat invert_exec.
  eapply exec_to_wcp; eauto.
Qed.

Lemma wp_low_to_high_write :
  forall a vl,
    wp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
Proof.
  unfold wp_low_to_high_prog'; intros; cleanup.
  simpl in H1; intros; cleanup.
  split_ors; cleanup; simpl in *.
  {
    eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H2; eauto.
    unfold write in H2.
    destruct x1.
    cleanup; eexists; intuition eauto.
    unfold refines_to in *; cleanup; eauto.
    left; intuition eauto.
    edestruct H4; eauto; cleanup.
    do 3 eexists; intuition eauto.
    apply upd_batch_write_all_mem_map; eauto.
    admit. (** TODO: Check this **)
  }
  {
    split_ors; cleanup; simpl in *;
    eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
  }
Admitted.

Lemma wp_high_to_low_write :
  forall a vl,
    wp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
Proof.
  unfold wp_high_to_low_prog'; intros; cleanup.
  repeat invert_exec.
  simpl in H1; cleanup.
  repeat (split_ors; cleanup).
  destruct x0.
  eapply exec_to_wp; eauto.
  simpl in H0; unfold refines_to in H0; cleanup.
  edestruct H3; eauto; cleanup.
  simpl; split;
  eauto; unfold refines_to.
  do 3 eexists; split; eauto.
  apply upd_batch_write_all_mem_map; eauto.
  admit. (** TODO: Check this **)

  simpl in H1; cleanup.
  simpl in *;
  repeat (split_ors; cleanup); intuition;
  destruct x1;
  eapply exec_to_wp; eauto;
  unfold write in *; cleanup; intuition;
  try invert_exec; eauto.
Admitted.

Lemma wcp_low_to_high_write :
  forall a vl,
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
Proof.
  unfold wcp_low_to_high_prog'; intros; cleanup.
  simpl in H1; intros; cleanup.
  simpl in *; split_ors; cleanup;
  try eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
  simpl; split_ors; cleanup;
  try eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup;
  eexists; intuition eauto.
  eapply exec_to_scp with (P := fun o s => refines_to s s2 /\ s = s1) in H2.
  2: unfold refines_to; eauto.
  simpl in *.
  unfold write in H2; cleanup;
  try solve [simpl in *; cleanup; intuition].
  right; intuition eauto.  
  admit. (** TODO: Prove this *)
Admitted.

Lemma wcp_high_to_low_write :
  forall a vl,
    wcp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
Proof.
  unfold wcp_high_to_low_prog'; intros; cleanup.
  simpl in H1; intros; cleanup.
  repeat split_ors; cleanup; repeat invert_exec;
  eapply exec_to_wcp; eauto;
  split_ors; cleanup; eauto.
  simpl.
  admit. (** TODO: Prove this **)
Admitted.


Theorem sbs_read :
  forall a,
    StrongBisimulationForProgram LoggedDiskRefinement (|Read a|).              
Proof.
  intros.
  eapply bisimulation_from_wp_prog; eauto.
  exact exec_preserves_refinement.
  exact exec_compiled_preserves_refinement.
  eapply Build_WP_Bisimulation_prog.
  apply wp_low_to_high_read.
  apply wp_high_to_low_read.    
  apply wcp_low_to_high_read.
  apply wcp_high_to_low_read.
Qed.

Theorem sbs_write :
  forall a lv,
    StrongBisimulationForProgram LoggedDiskRefinement (|Write a lv|).              
Proof.
  intros.
  eapply bisimulation_from_wp_prog; eauto.
  exact exec_preserves_refinement.
  exact exec_compiled_preserves_refinement.
  eapply Build_WP_Bisimulation_prog.
  apply wp_low_to_high_write.
  apply wp_high_to_low_write.
  apply wcp_low_to_high_write.
  apply wcp_high_to_low_write.
Qed.


Hint Resolve sbs_read sbs_write : core.

Theorem sbs :
  StrongBisimulation LoggedDiskRefinement.              
Proof.
  apply bisimulation_restrict_prog.
  induction p; eauto.
  destruct p; eauto.
  apply sbs_ret.
  apply sbs_bind; eauto.
Qed.

Hint Resolve sbs : core.

Theorem sbs_general:
  forall valid_state_h valid_prog_h,
    exec_compiled_preserves_validity LoggedDiskRefinement
                                     (refines_to_valid LoggedDiskRefinement valid_state_h) ->
    
    exec_preserves_validity LoggedDiskLang valid_state_h ->
    
    StrongBisimulationForValidStates LoggedDiskRefinement
                                     (refines_to_valid LoggedDiskRefinement valid_state_h)
                                     valid_state_h      
                                     valid_prog_h.  
Proof.
  intros.
  eapply bisimulation_restrict_state; eauto.
Qed.
End LoggedDiskBisimulation.

Section TransferToCachedDisk.
  
  Lemma high_oracle_exists_ok:
    high_oracle_exists LoggedDiskRefinement. 
  Proof.
    unfold high_oracle_exists, refines_to;
    induction p2; simpl; intros; cleanup.
    {
      destruct p; simpl in *.
      - (* Read *)
        destruct s1'; do 2 eexists; intuition eauto.        
        left; do 2 eexists; intuition eauto.
        unfold read in *.
        repeat invert_exec; simpl in *;
        inversion H0; sigT_eq;
        repeat invert_exec; simpl in *;
        destruct s1, s0; eauto.

        right; do 2 eexists; intuition eauto;
        unfold read in *;
        repeat (invert_exec; simpl in *; split_ors; cleanup);        
        try (inversion H0; sigT_eq);
        repeat invert_exec; simpl in *;
        destruct s1, s0; eauto.
        simpl in *; cleanup; invert_exec; eauto.

        repeat (simpl in *; split_ors; cleanup);        
        try (inversion H0; sigT_eq);
        repeat invert_exec; simpl in *;
        destruct s1, s0; eauto.
        simpl in *; cleanup; invert_exec; eauto.

        repeat (simpl in *; split_ors; cleanup);        
        try (inversion H0; sigT_eq);
        repeat invert_exec; simpl in *;
        destruct s1, s0; eauto.
        
      - (* Write *)
        destruct s1'.
        + do 2 eexists; intuition eauto;
          left; eauto.
          eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
          do 2 eexists; intuition eauto.
          admit. (* Doable *)
          
        + destruct (excluded_middle_dec (s = s1));
          do 2 eexists; intuition eauto;
          left; eauto.        
    }
    - (* Ret *)
      destruct s1'; eexists; eauto.
    - (* Bind *)
      invert_exec.
      + (* Finished *)
        edestruct IHp2; eauto.
        eapply_fresh exec_compiled_preserves_refinement in H1; simpl in *; eauto.
        cleanup; simpl in *; eauto.
        edestruct H; eauto.
        do 5 eexists; repeat (split; eauto).
        right; eauto.
        do 3 eexists; repeat (split; eauto).        

      + (* Crashed *)
        split_ors; cleanup.
        * (* p1 crashed *)
          edestruct IHp2; eauto.
          do 5 eexists; repeat (split; eauto).
        * (* p2 Crashed *)
          edestruct IHp2; eauto.
          eapply_fresh exec_compiled_preserves_refinement in H1; simpl in *; eauto.
          cleanup; simpl in *; eauto.
          edestruct H; eauto.
          do 5 eexists; repeat (split; eauto).
          right; eauto.
          do 3 eexists; repeat (split; eauto).
          
          Unshelve.
          eauto.
  Admitted.


  Theorem transfer_to_CachedDisk:
    forall related_states_h
      valid_state_h
      valid_prog_h,
      
      SelfSimulation
        LoggedDiskLang
        valid_state_h
        valid_prog_h
        related_states_h ->
      
      oracle_refines_to_same_from_related LoggedDiskRefinement related_states_h ->
      
      exec_compiled_preserves_validity LoggedDiskRefinement                           
                                       (refines_to_valid LoggedDiskRefinement valid_state_h) ->
      
      SelfSimulation
        CachedDiskLang
        (refines_to_valid LoggedDiskRefinement valid_state_h)
        (compiles_to_valid LoggedDiskRefinement valid_prog_h)
        (refines_to_related LoggedDiskRefinement related_states_h).
  Proof.
    intros; eapply transfer_high_to_low; eauto.
    apply sbs.
    apply high_oracle_exists_ok.
  Qed.

End TransferToCachedDisk.

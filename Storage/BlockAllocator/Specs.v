Require Import Primitives Layer2 Layer1 Omega.
Require Import BlockAllocator.
Require Import L1To2Refinement.Definitions.

Arguments oracle_ok T p o s : simpl never.
Arguments oracle_refines_to T d1 p o1 o2 : simpl never.
Arguments rep dh : simpl never.

Theorem alloc_ok:
  forall o d dh v,
  << o, d >>
   (rep dh)
   (alloc v)
  << r >>
   (exists dh',
    rep dh' *
     [[(r = None /\ dh' = dh) \/
       (exists a, r = Some a /\ dh a = None /\ dh' = upd dh a v)%type]])
   (exists dh',
    rep dh' *
     [[(dh' = dh) \/
       (exists a, dh a = None /\ dh' = upd dh a v)%type]])
   (exists dh',
    rep dh' *
     [[(r = None /\ dh' = dh /\ oracle_refines_to _ d (Alloc v) o (DiskFull::nil)) \/
       (exists a, r = Some a /\ dh a = None /\ dh' = upd dh a v /\
             oracle_refines_to _ d (Alloc v) o (BlockNum a::nil))%type]])%pred
   (exists dh',
    rep dh' *
     [[(dh' = dh /\ oracle_refines_to _ d (Alloc v) o (Crash1::nil)) \/
       (exists a, dh a = None /\ dh' = upd dh a v /\
             oracle_refines_to _ d (Alloc v) o (CrashAlloc a::nil) )%type]])%pred.
Proof.
  unfold alloc, exec; intros.
  apply remember_oracle_ok; intros.
  eapply pre_strengthen_aug.
  2: eapply rep_extract_bitmap.
  apply extract_exists_aug.
  intro v0.
  eapply bind_ok_aug.
  intros.
  eapply add_frame.
  apply read_ok.
  all: try solve [ simpl; intros; try apply pimpl_refl; cancel].
  all: try solve [ simpl; intros; try setoid_rewrite rep_merge; cancel].

  intros; destruct_lifts.
  destruct (lt_dec (get_first_zero (bits (value_to_bits v0_cur))) block_size); simpl in *.
  {
    eapply pre_strengthen_aug.
    2: erewrite rep_extract_block_size_double with (a:= get_first_zero (bits (value_to_bits v0_cur))); eauto.
    eapply pre_strengthen_aug; [|apply pimpl_exists_l_star_r].
    apply extract_exists_aug.
    intro v0.
    eapply bind_ok_aug.
    intros; eapply add_frame.
    apply write_ok.

    all: try solve [ simpl; intros; apply pimpl_refl; cancel].
    cancel.
    intros; cancel.
    rewrite septract_double_split.
    rewrite sep_star_assoc.
    setoid_rewrite sep_star_comm at 2.
    rewrite septract_sep_star_merge.
    rewrite sep_star_comm, rep_merge; eauto.
    apply ptsto_complete.
        
    simpl; intros; destruct_lifts.
    intros.
    eapply bind_ok_aug.
    intros; eapply add_frame.
    eapply write_ok.
    all: try solve [ simpl; intros; try apply pimpl_refl; cancel].
    intros; simpl; cancel.
    (* we need folding magic here *)
    shelve.
   
    simpl; intros; destruct_lifts.
    apply remove_augcons.
    eapply pre_strengthen.
    eapply crash_weaken.
    eapply post_weaken.
    eapply add_frame.
    apply ret_ok.
    all: unfold exec in *.
    - (* post *)
      simpl; intros.
      cancel.
      right; eexists; intuition eauto.
      shelve.
    - cancel.
      right; eexists; intuition eauto.
      shelve.
    - (* Again, folding magic *)
      shelve.
      
    - (* Finished oracle refinement *)
      simpl; intros; destruct_lifts; cleanup.
      invert_exec.
      unfold addr in *; sigT_eq.
      split_ors; cleanup; try congruence.
      pred_apply; cancel.
      
      right; eexists; intuition eauto.
      unfold oracle_refines_to; simpl.
      intuition eauto.
      destruct (in_dec Layer1.token_dec Layer1.Crash (o1 ++ o0 ++ o2 ++ [Layer1.Cont])).
      repeat invert_exec; simpl in *.
      intuition congruence.
      
      unfold Disk.read.
      erewrite ptsto_valid; [| pred_apply; cancel].
      simpl.
      destruct (lt_dec (get_first_zero (bits (value_to_bits v0_cur))) block_size); try omega; eauto.

    - simpl; intros; destruct_lifts; cleanup.
      intuition; cleanup; pred_apply; cancel.

      + left; intuition.
        unfold oracle_refines_to; simpl.
        intuition eauto.
        unfold alloc in *.
        repeat invert_exec; cleanup.
        simpl; intuition.
        repeat invert_exec; cleanup.
        repeat (try split_ors; invert_exec; simpl in *; cleanup; try congruence).
        unfold Disk.read, Disk.write, upd_disk in *; cleanup.
        rewrite upd_eq'; split; intros; eauto.
        admit. (* solvable by H11 *)
        congruence.
        congruence.
      
      + right.
        unfold oracle_refines_to; simpl.
        repeat invert_exec; cleanup.
        unfold Disk.read, Disk.write, upd_disk in *; cleanup.
        simpl; intuition.
        assume (A : (x = get_first_zero (bits (value_to_bits (fst s))))); cleanup.
        eexists; intuition eauto.
        unfold alloc in *.
        repeat invert_exec; cleanup.
        repeat (try split_ors; invert_exec; simpl in *; cleanup; try congruence).
        unfold Disk.read, Disk.write, upd_disk in *; cleanup.
        rewrite upd_eq'; split; intros; eauto.
        admit.
        congruence.
        congruence.
        congruence.
        congruence.

    - simpl; intros; destruct_lifts; cleanup.
      pred_apply; cancel.
      rewrite septract_double_split.
      setoid_rewrite sep_star_comm at 2.
      rewrite septract_sep_star_merge.
      eassign dh. admit.
      apply ptsto_complete.
      
      left; intuition.
      unfold oracle_refines_to; simpl.
      repeat invert_exec; cleanup.
      unfold Disk.read, Disk.write, upd_disk in *; cleanup.
      simpl; intuition.
      unfold alloc in *.
      repeat invert_exec; cleanup.
      repeat (try split_ors; invert_exec; simpl in *; cleanup; try congruence).
      unfold Disk.read, Disk.write, upd_disk in *; cleanup.
      rewrite upd_ne; eauto.
      cleanup.
      split; intros; eauto.
      congruence.
      congruence.
      congruence.

    - simpl; intros; destruct_lifts; cleanup.
      pred_apply; cancel.
      rewrite septract_double_split.
      rewrite sep_star_assoc.
      setoid_rewrite sep_star_comm at 2.
      rewrite septract_sep_star_merge.
      rewrite sep_star_comm, rep_merge; eauto.
      apply ptsto_complete.
      
      left; intuition.
      unfold oracle_refines_to; simpl.
      repeat invert_exec; cleanup.
      unfold Disk.read, Disk.write, upd_disk in *; cleanup.
      simpl; intuition.
      unfold alloc in *.
      repeat invert_exec; cleanup.
      repeat (try split_ors; invert_exec; simpl in *; cleanup; try congruence).
      unfold Disk.read, Disk.write, upd_disk in *; cleanup.
      split; intros; eauto.
      congruence.
      split; intros; eauto.
      congruence.
  }
  {
    apply remove_augcons.
    eapply pre_strengthen.
    eapply crash_weaken.
    eapply post_weaken.
    eapply add_frame.
    apply ret_ok.
    all: try solve [ simpl; intros; try setoid_rewrite rep_merge; cancel].
    rewrite sep_star_comm, rep_merge; cancel.
    all: unfold exec in *.
    - simpl; intros; destruct_lifts; cleanup.
      invert_exec; unfold addr in *; sigT_eq.
      split_ors; cleanup; try congruence.
      pred_apply; cancel.
      left; eexists; intuition eauto.
      unfold oracle_refines_to; simpl.
      repeat invert_exec; simpl in *.
      intuition eauto.
      cleanup.
      destruct (lt_dec (get_first_zero (bits (value_to_bits v0_cur))) block_size); try omega; eauto.

    - simpl; intros; destruct_lifts; cleanup.
      intuition; cleanup; pred_apply; cancel.

      + left; intuition.
        unfold oracle_refines_to; simpl.
        intuition eauto.
        unfold alloc in *.
        repeat invert_exec; cleanup.
        simpl; intuition.
        repeat invert_exec; cleanup.
        repeat (try split_ors; invert_exec; simpl in *; cleanup; try congruence).
        unfold Disk.read, Disk.write, upd_disk in *; cleanup.
        split; intros; eauto.
        congruence.
      
      + right.
        unfold oracle_refines_to; simpl.
        repeat invert_exec; cleanup.
        admit.
  }
  {
    unfold exec in *.
    simpl; intros; destruct_lifts; cleanup.
    invert_exec.
    pred_apply; cancel.
    rewrite sep_star_comm, rep_merge; eauto.
    
    left; intuition eauto.
    unfold oracle_refines_to; simpl.
    intuition eauto.
    unfold alloc in *.
    repeat invert_exec; cleanup.
    simpl; intuition.
    repeat invert_exec; cleanup.
    unfold Disk.read, Disk.write, upd_disk in *; cleanup.
    erewrite ptsto_valid; [| pred_apply; cancel].
    split; intros; eauto; congruence.
    
    cleanup; repeat invert_exec; simpl in *; cleanup.
  }
Admitted.

Theorem read_ok:
  forall o d a dh,
  << o, d >>
   (rep dh)
   (read a)
  << r >>
  (rep dh *
   [[(r = None /\ (dh a = None \/ a >= block_size)) \/
     (exists v, r = Some v /\ dh a = Some v)%type]])
   (rep dh)
  (rep dh * [[ oracle_refines_to _ d (Layer2.Read a) o (Layer2.Cont::nil) ]] *
   [[(r = None /\ (dh a = None \/ a >= block_size)) \/
     (exists v, r = Some v /\ dh a = Some v)%type]])
   (rep dh * [[ oracle_refines_to _ d (Layer2.Read a) o (Crash1::nil) ]]).
Proof. Admitted. (*
  intros.
  unfold read; simpl.

  unfold rep.
  repeat (apply hoare_triple_pre_ex; intros).
  
  eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
  eapply hoare_triple_strengthen_pre;
    [apply read_okay | intros; simpl; cancel].

  simpl. destruct (addr_dec a 1); subst.
  {
    intros; simpl.
    destruct (addr_dec (value_to_nat r) 1); simpl.
    {
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply read_okay | intros; simpl; cancel].

    {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0; cleanup;
          cancel; eauto.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0; cleanup;
          cancel; eauto.

      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        cleanup;
          cancel; eauto.
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H0; cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

    destruct (addr_dec (value_to_nat r) 3); simpl.
    {
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply read_okay | intros; simpl; cancel].

    {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0; cleanup;
          cancel; eauto.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0; cleanup;
          cancel; eauto.

      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        cleanup;
          cancel; eauto.
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H0; cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

      {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.

      eassign (F * rep dh * ⟦⟦ r = v ⟧⟧).
      destruct_lift H;
        cleanup.
      intros; simpl in *; unfold rep; cancel.
      
      unfold rep; intros; simpl in *.
      destruct_lift H; cleanup.
      norm; [cancel| intuition (eauto; try omega)].
      

      intros; simpl in *.
      unfold rep;
      destruct_lift H; cleanup;
      norm; [cancel| intuition (eauto; try omega)].
      
      left; split; eauto.
      left.
      destruct (addr_dec (value_to_nat v) 0).
      destruct H8; eauto.
      destruct (addr_dec (value_to_nat v) 2);
        destruct H6; eauto.
      omega.
    }
  }
  

  destruct (addr_dec a 2); subst.
  {
    intros; simpl.
    destruct (addr_dec (value_to_nat r) 2); simpl.
    {
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply read_okay | intros; simpl; cancel].

    {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0; cleanup;
          cancel; eauto.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0; cleanup;
          cancel; eauto.

      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        cleanup;
          cancel; eauto.
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H0; cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

    destruct (addr_dec (value_to_nat r) 3); simpl.
    {
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply read_okay | intros; simpl; cancel].

    {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0; cleanup;
          cancel; eauto.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0; cleanup;
          cancel; eauto.

      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        cleanup;
          cancel; eauto.
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H0; cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

      {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.

      eassign (F * rep dh * ⟦⟦ r = v ⟧⟧).
      destruct_lift H;
        cleanup.
      intros; simpl in *; unfold rep; cancel.
      
      unfold rep; intros; simpl in *.
      destruct_lift H;
        cleanup.
      norm; [cancel| intuition (eauto; try omega)].      

      intros; simpl in *.
      unfold rep;
      destruct_lift H;
        destruct_lift H0;
        cleanup;
      norm; [cancel| intuition (eauto; try omega)].
      
      left; split; eauto.
      left.
      destruct (addr_dec (value_to_nat v) 0).
      destruct H8; eauto.
      destruct (addr_dec (value_to_nat v) 1).
      destruct H7; eauto.
      omega.
    }
  }

  {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.
      intros; simpl; rewrite emp_star_r; eauto.
      destruct_lift H; cancel.
      destruct_lift H; cancel.
      left; intuition.      
      right; omega.
  }

  intros; simpl.
  destruct_lift H; cancel.
Qed.

Lemma exis_lift_absorb:
  forall A AEQ V T (P: T -> @pred A AEQ V) Q,
    (exists x, P x) * [[ Q ]] =p=> exists x, (P x * [[Q]]).
Proof.
  intros; cancel.
Qed.
*)

Theorem write_ok:
  forall o d dh a v,
  << o, d >>
   (rep dh)
   (write a v)
  << r >>
   (exists dh',
    rep dh' * 
     [[(r = None /\ dh' = dh /\ dh a = None) \/
       (r = Some tt /\ dh a <> None /\ dh' = upd dh a v)%type]])
   (exists dh',
    rep dh' *
    [[((dh' = dh) \/
       (dh a <> None /\ dh' = upd dh a v))%type]])
   (exists dh',
    rep dh' * [[ oracle_refines_to _ d (Layer2.Write a v) o (Layer2.Cont::nil) ]] *
     [[(r = None /\ dh' = dh /\ dh a = None) \/
       (r = Some tt /\ dh a <> None /\ dh' = upd dh a v)%type]])
   (exists dh',
      rep dh' *
      [[((dh' = dh /\ oracle_refines_to _ d (Layer2.Write a v) o (Crash1::nil)) \/
       (dh a <> None /\ dh' = upd dh a v /\ oracle_refines_to _ d (Layer2.Write a v) o (Crash2::nil)))%type]]).
Proof. Admitted. (*
  intros.
  unfold write; simpl.

  repeat (apply hoare_triple_pre_ex; intros).
    eapply hoare_triple_pimpl;
      try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
      [apply read_okay | intros; simpl; cancel].
    
  intros; simpl; destruct (addr_dec a 1); subst.
  {
    intros; simpl.
    destruct (addr_dec (value_to_nat r) 1); simpl.
    {
      eapply hoare_triple_pimpl;
        try solve [intros; simpl in *; eauto].
      eapply hoare_triple_strengthen_pre;
        [apply write_okay | intros; simpl; cancel].
      
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply ret_okay.
        
        intros; simpl in *.
        rewrite <- emp_star_r; eauto.
        
        intros; unfold rep; simpl in *.
        norm; [cancel|].
        eassign (upd dh 1 v).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
        right; intuition eauto.
        cleanup.

        intros; unfold rep; simpl in *.
        norm; [cancel|].
        eassign (upd dh 1 v).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
        right; intuition eauto.
        cleanup.
      }        
      intros; unfold rep; simpl in *.
      destruct_lift H;
          destruct_lift H0;
          cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

    destruct (addr_dec (value_to_nat r) 3); simpl.
    {
      eapply hoare_triple_pimpl;
        try solve [intros; simpl in *; eauto].
      eapply hoare_triple_strengthen_pre;
        [apply write_okay | intros; simpl; cancel].
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply ret_okay.
        
        intros; simpl in *.
        rewrite <- emp_star_r; eauto.
        
        intros; unfold rep; simpl in *.
        norm; [cancel|].
        eassign (upd dh 1 v).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
        right; intuition eauto.
        cleanup.

        intros; unfold rep; simpl in *.
        norm; [cancel|].
        eassign (upd dh 1 v).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
        right; intuition eauto.
        cleanup.
      }        
      intros; unfold rep; simpl in *.
      destruct_lift H;
          destruct_lift H0;
          cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

      {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.

      eassign (F * rep dh).
      destruct_lift H;
        cleanup.
      intros; simpl in *; unfold rep; cancel.

      cancel.
      cancel.
    }
  }
  

  destruct (addr_dec a 2); subst.
   {
    intros; simpl.
    destruct (addr_dec (value_to_nat r) 2); simpl.
    {
      eapply hoare_triple_pimpl;
        try solve [intros; simpl in *; eauto].
      eapply hoare_triple_strengthen_pre;
        [apply write_okay | intros; simpl; cancel].
      destruct_lift H; cleanup.
      
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply ret_okay.

        intros; simpl in *.
        rewrite <- emp_star_r; eauto.
        
        intros; unfold rep; simpl in *.
        norm; [cancel|].
        eassign (upd dh 2 v).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
        right; intuition eauto.
        cleanup.

        intros; unfold rep; simpl in *.
        norm; [cancel|].
        eassign (upd dh 2 v).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
        right; intuition eauto.
        cleanup.
      }        
      intros; unfold rep; simpl in *.
      destruct_lift H;
          destruct_lift H0;
          cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

    destruct (addr_dec (value_to_nat r) 3); simpl.
    {
      eapply hoare_triple_pimpl;
        try solve [intros; simpl in *; eauto].
      eapply hoare_triple_strengthen_pre;
        [apply write_okay | intros; simpl; cancel].
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply ret_okay.
        
        intros; simpl in *.
        rewrite <- emp_star_r; eauto.
        
        intros; unfold rep; simpl in *.
        norm; [cancel|].
        eassign (upd dh 2 v).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
        right; intuition eauto.
        cleanup.

        intros; unfold rep; simpl in *.
        norm; [cancel|].
        eassign (upd dh 2 v).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
        right; intuition eauto.
        cleanup.
      }        
      intros; unfold rep; simpl in *.
      destruct_lift H;
          destruct_lift H0;
          cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

      {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.

      eassign (F * rep dh).
      destruct_lift H;
        cleanup.
      intros; simpl in *; unfold rep; cancel.

      cancel.
      cancel.

      }
   }

   {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.

      eassign (F * rep dh).
      destruct_lift H;
        cleanup.
      intros; simpl in *; unfold rep; cancel.
      
      all: cancel.
   }
   intros; simpl in *;
     destruct_lift H; cleanup.
   cancel; unfold rep; cancel.
Qed.
*)



Theorem free_ok:
  forall o d dh a,
  << o, d >>
   (rep dh)
   (free a)
  << r >>
   (rep (delete dh a))
   (exists dh',
       rep dh' *
       [[ (dh' = dh) \/
          (dh' = (delete dh a))]])
   (rep (delete dh a) *
    [[ oracle_refines_to _ d (Free a) o (Layer2.Cont::nil) ]])
   (exists dh',
      rep dh' *
      [[ (dh' = dh /\ oracle_refines_to _ d (Free a) o (Crash1::nil)) \/
         (dh' = (delete dh a) /\ oracle_refines_to _ d (Free a) o (Crash2::nil))]]).
Proof. Admitted. (*
  intros.
  unfold free; simpl.

  destruct (addr_dec a 1); subst.
  {
    

    intros; simpl.
    eapply hoare_triple_pimpl;
      try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
      [apply unseal_okay | intros; simpl; cancel].
    apply upd_eq; eauto.
    simpl; apply can_access_public.

    intros; simpl.
    destruct (addr_dec (value_to_nat r0) 1); simpl.
    {
      eapply hoare_triple_pimpl;
        try solve [intros; simpl in *; eauto].
      eapply hoare_triple_strengthen_pre;
        [apply seal_okay | intros; simpl; cancel].
    
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply write_okay.
        
        intros; simpl in *.
        cancel.
        apply upd_eq'.
        
        intros; simpl in *.
        norm; [cancel|].
        eassign dh.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).

        intros; simpl in *.
        norm; [cancel|].
        rewrite delete_eq.
        repeat rewrite delete_ne; eauto.
        rewrite nat_to_value_to_nat.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite delete_ne; eauto; omega.
      }        
      intros; simpl in *.
      destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

    destruct (addr_dec (value_to_nat r0) 3); simpl.
    {
      eapply hoare_triple_pimpl;
        try solve [intros; simpl in *; eauto].
      eapply hoare_triple_strengthen_pre;
        [apply seal_okay | intros; simpl; cancel].
    
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply write_okay.
        
        intros; simpl in *.
        cancel.
        apply upd_eq'.
        
        intros; simpl in *.
        norm; [cancel|].
        eassign dh.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).

        intros; simpl in *.
        norm; [cancel|].
        rewrite delete_eq.
        repeat rewrite delete_ne; eauto.
        rewrite nat_to_value_to_nat.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite delete_ne; eauto; omega.
      }        
      intros; simpl in *.
      destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

    {
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply ret_okay.
        
        intros; simpl in *.
        eassign (((((0 |-> (Public, v, v0) ✶ F) ✶ 1 |-> v1) ✶ 2 |-> v2) ✶ (⟦⟦ r0 = v ⟧⟧))).
        cancel.
        
        intros; simpl in *.
        norm; [cancel|].
        eassign dh.
        destruct_lift H;
          destruct_lift H0;
          cleanup;
          intuition (eauto; try omega).

        intros; simpl in *.
        norm; [cancel|].
        rewrite delete_eq.
        repeat rewrite delete_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite delete_ne; eauto; omega.
      }
    }
    
      intros; simpl in *;
      destruct_lift H;
          destruct_lift H0;
          cleanup;
          norm; [cancel| intuition (eauto; try omega)].
    intros; simpl in *;
      destruct_lift H;
          cleanup;
        norm; [cancel| intuition (eauto; try omega)].
  }

  destruct (addr_dec a 2); subst.
  {
    unfold rep.
    repeat (apply hoare_triple_pre_ex; intros).
    eapply hoare_triple_pimpl;
      try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
      [apply read_okay | intros; simpl; cancel].

    intros; simpl.
    eapply hoare_triple_pimpl;
      try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
      [apply unseal_okay | intros; simpl; cancel].
    apply upd_eq; eauto.
    simpl; apply can_access_public.

    intros; simpl.
    destruct (addr_dec (value_to_nat r0) 2); simpl.
    {
      eapply hoare_triple_pimpl;
        try solve [intros; simpl in *; eauto].
      eapply hoare_triple_strengthen_pre;
        [apply seal_okay | intros; simpl; cancel].
    
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply write_okay.
        
        intros; simpl in *.
        cancel.
        apply upd_eq'.
        
        intros; simpl in *.
        norm; [cancel|].
        eassign dh.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).

        intros; simpl in *.
        norm; [cancel|].
        rewrite delete_eq.
        repeat rewrite delete_ne; eauto.
        rewrite nat_to_value_to_nat.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite delete_ne; eauto; omega.
      }        
      intros; simpl in *.
      destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

    destruct (addr_dec (value_to_nat r0) 3); simpl.
    {
      eapply hoare_triple_pimpl;
        try solve [intros; simpl in *; eauto].
      eapply hoare_triple_strengthen_pre;
        [apply seal_okay | intros; simpl; cancel].
    
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply write_okay.
        
        intros; simpl in *.
        cancel.
        apply upd_eq'.
        
        intros; simpl in *.
        norm; [cancel|].
        eassign dh.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).

        intros; simpl in *.
        norm; [cancel|].
        rewrite delete_eq.
        repeat rewrite delete_ne; eauto.
        rewrite nat_to_value_to_nat.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite delete_ne; eauto; omega.
      }        
      intros; simpl in *.
      destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

    {
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply ret_okay.
        
        intros; simpl in *.
        eassign (((((0 |-> (Public, v, v0) ✶ F) ✶ 1 |-> v1) ✶ 2 |-> v2) ✶ (⟦⟦ r0 = v ⟧⟧))).
        cancel.
        
        intros; simpl in *.
        norm; [cancel|].
        eassign dh.
        destruct_lift H;
          destruct_lift H0;
          cleanup;
          intuition (eauto; try omega).

        intros; simpl in *.
        norm; [cancel|].
        rewrite delete_eq.
        repeat rewrite delete_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite delete_ne; eauto; omega.
      }
    }
    
      intros; simpl in *;
      destruct_lift H;
          destruct_lift H0;
          cleanup;
          norm; [cancel| intuition (eauto; try omega)].
    intros; simpl in *;
      destruct_lift H;
          cleanup;
        norm; [cancel| intuition (eauto; try omega)].
  }


  {
    intros; simpl.
    eapply hoare_triple_weaken_post_weak.
    eapply hoare_triple_weaken_crash_strong.
    eapply hoare_triple_strengthen_pre.
    apply ret_okay.

    all: cancel.
    cancel.
    unfold rep.
    destruct a.
    unfold delete at 1.
    destruct (addr_dec 0 0); intuition.
    repeat rewrite delete_ne; eauto.
    cancel.
    rewrite delete_ne; eauto.
    omega.

    repeat rewrite delete_ne; eauto.
    cancel.
    destruct (addr_dec (S a) n1); subst.
    apply delete_eq.
    rewrite delete_ne; eauto.
  }
Qed.
 *)

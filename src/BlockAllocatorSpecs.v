Require Import Primitives Omega Disk.
Require Import BlockAllocatorDefinitions BlockAllocatorFacts.
Require Import Layer2 Layer1to2RefinementDefinitions.

Arguments oracle_ok T p o s : simpl never.


Theorem alloc_ok:
  forall dh v,
  << o >>
   (rep dh)
   (alloc v)
  << d, r >>
   (exists dh',
    rep dh' *
     [[(r = None /\ dh' = dh /\ oracle_refines_to _ d (Alloc v) o (DiskFull::nil)) \/
       (exists a, r = Some a /\ dh a = None /\ dh' = upd dh a v /\ oracle_refines_to _ d (Alloc v) o (BlockNum a::nil))%type]])
   (exists dh',
    rep dh' *
     [[(dh' = dh /\ oracle_refines_to _ d (Alloc v) o (Crash1::nil)) \/
       (exists a, dh a = None /\ dh' = upd dh a v /\ oracle_refines_to _ d (Alloc v) o (CrashAlloc a::nil) )%type]]).
Proof. Admitted. (*
  unfold alloc; intros dh v.
  unfold rep.
  repeat (apply extract_exists; intros).
  eapply crash_weaken.
  eapply bind_ok.  
  eapply pre_strengthen.
  eapply add_frame.
  apply read_ok.
  eassign (ptsto_bits dh (bits (value_to_bits v0)) *
           [[ forall i : nat, i >= block_size -> dh i = None ]]).
  cancel.
  simpl; intros; cancel.
 
  intros; destruct_lifts.
  destruct (lt_dec (get_first_zero (bits (value_to_bits v0))) block_size); simpl in *.
  {
    eapply hoare_triple_strengthen_pre.
    2: {
      unfold ptsto_bits.
      intros.
      
      instantiate (1:= (fun o0 => (fun d0 => ( F2 * (exists vs, (S (get_first_zero (bits (value_to_bits v0)))|-> vs) * 0 |-> (v0, v1) * ((S (get_first_zero (bits (value_to_bits v0)))|-> vs) --* ptsto_bits' dh (bits (value_to_bits v0)) 0))
    ✶ ⟦⟦ oracle_ok
           (_ <- Write (S (get_first_zero (bits (value_to_bits v0)))) v;
            _ <-
            Write 0
              (bits_to_value
                 {|
                 bits := ListUtils.updN (bits (value_to_bits v0)) (get_first_zero (bits (value_to_bits v0))) 1;
                 valid := upd_valid_one (get_first_zero (bits (value_to_bits v0))) (bits (value_to_bits v0))
                            (valid (value_to_bits v0)) |}); Ret (Some (get_first_zero (bits (value_to_bits v0)))))
           o0 d0 ⟧⟧) d0)%pred)).
      simpl.
      intros m Hm; simpl in *;
        pred_apply; clear Hm.
      erewrite (ptsto_bits'_extract (bits (value_to_bits v0))) at 1.
      norml.
      cancel.
      eauto.
      rewrite Nat.add_0_r.
      destruct (value_to_bits v0); simpl in *.
      destruct valid.
      rewrite H2; eauto.
      omega.
    }    
    repeat (apply extract_exists; intros).
    destruct v2.
    eapply crash_weaken.    
    eapply pre_strengthen.
    eapply bind_ok.
    eapply add_frame.
    apply write_ok.

    simpl; intros; eauto.

    simpl; intros.
    eapply hoare_triple_strengthen_pre.
    eapply crash_weaken.
    eapply bind_ok.
    eapply add_frame.
    eapply write_ok.

    simpl; intros; eauto.

    simpl in *; intros.
    eapply hoare_triple_strengthen_pre.
    eapply crash_weaken.
    eapply post_weaken.
    eapply add_frame.
    apply ret_ok.

    - (* post *)
      simpl; intros.
      shelve.
    - eauto.
    - simpl; intros.
      cancel.
      intros m Hm; simpl in *;
        pred_apply; clear Hm.
      shelve.
    - eauto.
    - simpl; intros; cancel.
      intros m Hm; simpl in *;
        pred_apply; clear Hm.
      cancel.
      shelve.
    - cancel.
    - instantiate (1:= 
        (exists dh',
            rep dh' *
            [[(dh' = dh) \/
              (exists h, dh' = upd dh h v)%type]])).
      unfold rep.
      unfold ptsto_bits.
      shelve.
  }
  {
    simpl in *; intros.
    eapply hoare_triple_strengthen_pre.
    eapply crash_weaken.
    eapply post_weaken.
    eapply add_frame.
    apply ret_ok.

    - destruct_lift H.
      simpl; safecancel.
      eauto.
      eauto.
    - unfold rep; simpl; cancel.
    - intros.
      intros m Hm; simpl in *;
        pred_apply; clear Hm.
      simpl; cancel.
  }
  {
    unfold rep; cancel.
    cleanup.
    right.
    do 2 eexists; eauto.
  }
  Unshelve.
  {
    safecancel.
    2: right; eauto.
    erewrite upd_ne.
    eauto.
    omega.
  }
  {
    cancel.
  }
  shelve.
  {
    rewrite bits_to_value_to_bits; simpl.
    cancel.
    unfold ptsto_bits.
    rewrite ptsto_bits'_update.
    rewrite Nat.sub_0_r; eauto.
    destruct (value_to_bits v0); simpl in *.
    destruct valid.
    rewrite e; eauto.
    omega.
    omega.
  }
  {
    safecancel; eauto.
    rewrite sep_star_comm.
    apply ptsto_bits'_merge.
        
    rewrite bits_to_value_to_bits; simpl.
    unfold ptsto_bits.
    
    admit.
    erewrite upd_ne.
    eauto.
    omega.
  }  
Admitted.
*)
Theorem read_ok:
  forall a dh,
  << o >>
   (rep dh)
   (read a)
  << d, r >>
  (rep dh * [[ oracle_refines_to _ d (Read a) o (Cont::nil) ]] *
   [[(r = None /\ (dh a = None \/ a >= block_size)) \/
     (exists v, r = Some v /\ dh a = Some v)%type]])
   (rep dh * [[ oracle_refines_to _ d (Read a) o (Crash1::nil) ]]).
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
  forall dh a v,
  << o >>
   (rep dh)
   (write a v)
  << d, r >>
   (exists dh',
    rep dh' * [[ oracle_refines_to _ d (Write a v) o (Cont::nil) ]] *
     [[(r = None /\ dh' = dh /\ dh a = None) \/
       (r = Some tt /\ dh a <> None /\ dh' = upd dh a v)%type]])
   (exists dh',
    rep dh' *
    [[((dh' = dh /\ oracle_refines_to _ d (Write a v) o (Crash1::nil)) \/
       (dh a <> None /\ dh' = upd dh a v /\ oracle_refines_to _ d (Write a v) o (Crash2::nil)))%type]]).
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
  forall dh a,
  << o >>
   (rep dh)
   (free a)
  << d, r >>
   (rep (delete dh a) *
    [[ oracle_refines_to _ d (Free a) o (Cont::nil) ]])
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
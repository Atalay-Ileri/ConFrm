Require Import Primitives Layer1 Omega.
Require Import BlockAllocator.Definitions BlockAllocator.Facts.

Arguments oracle_ok T p o s : simpl never.
Arguments rep dh : simpl never.

Theorem alloc_ok:
  forall dh v,
  << o >>
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
       (exists a, dh a = None /\ dh' = upd dh a v)%type]]).
Proof.
  unfold alloc; intros dh v.
  eapply pre_strengthen.
  2: eapply rep_extract_bitmap.
  apply extract_exists.
  intro v0.
  eapply bind_ok.  
  eapply add_frame.
  apply read_ok.
  all: try solve [ simpl; intros; try setoid_rewrite rep_merge; apply pimpl_refl].
  all: try solve [ simpl; intros; apply pimpl_refl].
  all: try solve [ simpl; intros; try setoid_rewrite rep_merge; cancel].

  intros F d d' r H H0; destruct_lifts.
  destruct (lt_dec (get_first_zero (bits (value_to_bits v0_cur))) block_size); simpl in *.
  {
    eapply pre_strengthen.
    2: erewrite rep_extract_block_size_double with (a:= get_first_zero (bits (value_to_bits v0_cur))); eauto.
    eapply pre_strengthen; [|apply pimpl_exists_l_star_r].
    apply extract_exists.
    intro v0.
    destruct v0.
    eapply bind_ok.
    eapply add_frame.
    apply write_ok.

    all: try solve [ simpl; intros; apply pimpl_refl].
    cancel.
    simpl; intros; try setoid_rewrite rep_merge; cancel.
    shelve.
    
    simpl; intros F0 d0 d'0 r H1 H2; destruct_lifts.    
    eapply bind_ok.
    eapply add_frame.
    eapply write_ok.
    all: try solve [ simpl; intros; apply pimpl_refl].
    cancel.
    intros; simpl.
    (* we need folding magic here *)
    shelve.
   
    simpl; intros F1 d1 d'1 r H3 H4; destruct_lifts.

    eapply pre_strengthen.
    eapply crash_weaken.
    eapply post_weaken.
    eapply add_frame.
    apply ret_ok.
    
    - (* post *)
      simpl; intros.
      cancel.
      right; eexists; intuition eauto.
      shelve.
    - cancel.
      right; eexists; intuition eauto.
      shelve.
    - setoid_rewrite <- rep_merge with (a:= 0) at 2.
      cancel.
      shelve.
  }
  {
    eapply pre_strengthen.
    eapply crash_weaken.
    eapply post_weaken.
    eapply add_frame.
    apply ret_ok.
    all: try solve [ simpl; intros; try setoid_rewrite rep_merge; cancel].
    rewrite sep_star_comm, rep_merge; cancel.
  }
Admitted.

Theorem read_ok:
  forall a dh,
  << o >>
   (rep dh)
   (read a)
  << r >>
  (rep dh *
   [[(r = None /\ (dh a = None \/ a >= block_size)) \/
     (exists v, r = Some v /\ dh a = Some v)%type]])
   (rep dh).
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
  << r >>
   (exists dh',
    rep dh' * 
     [[(r = None /\ dh' = dh /\ dh a = None) \/
       (r = Some tt /\ dh a <> None /\ dh' = upd dh a v)%type]])
   (exists dh',
    rep dh' *
    [[((dh' = dh) \/
       (dh a <> None /\ dh' = upd dh a v))%type]]).
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
  << r >>
   (rep (delete dh a))
   (exists dh',
       rep dh' *
       [[ (dh' = dh) \/
          (dh' = (delete dh a))]]).
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
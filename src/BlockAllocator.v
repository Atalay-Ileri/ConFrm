Require Import Primitives Omega Disk.
Close Scope pred_scope.

Axiom block_size: nat.
Axiom block_size_eq: block_size = 64.

Definition valid_bitlist l := length l = block_size /\ (forall i, In i l -> i < 2).
Record bitlist :=
  {
   bits : list nat;                
   valid : valid_bitlist bits
  }.

Fixpoint get_first_zero l :=
  match l with
  | nil => 0
  | hd::tl =>
    match hd with
    | O => 0
    | _ => S (get_first_zero tl)
    end
  end.

Definition upd {T} i l (v: T) := firstn (length l) (firstn i l ++ v::skipn (S i) l).

Theorem upd_valid_zero:
  forall i l,
    valid_bitlist l ->
    valid_bitlist (upd i l 0).
Proof. Admitted.

Theorem upd_valid_one:
  forall i l,
    valid_bitlist l ->
    valid_bitlist (upd i l 1).
Proof. Admitted.

Axiom value_to_bits: value -> bitlist.
Axiom bits_to_value: bitlist -> value.
Axiom value_to_bits_to_value : forall v, bits_to_value (value_to_bits v) = v.
Axiom bits_to_value_to_bits : forall l, value_to_bits (bits_to_value l) = l.                                                                   
Open Scope pred_scope.

Definition rep (dh: disk value) : @pred addr addr_dec (set value) :=
  fun d => (exists bitmap bl rest,
    let bits := bits (value_to_bits bitmap) in
    0 |-> (bitmap, bl) * rest *
    [[forall i, nth i bits 0 = 0 -> dh i = None]] *
    [[(forall i, nth i bits 0 = 1 -> exists vs, d (S i) = Some vs /\ dh i = Some (fst vs))%type]])%pred d.

Definition alloc (v': value) : prog (option addr) :=
  v <- Read 0;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  let index := get_first_zero bits in
  
  if lt_dec index block_size then
    _ <- Write (S index) v';
    _ <- Write 0 (bits_to_value (Build_bitlist (upd index bits 1) (upd_valid_one index bits valid)));
    Ret (Some index)
  else
    Ret None.

Definition read a : prog (option value) :=
  v <- Read 0;
  let bits := bits (value_to_bits v) in
  if lt_dec a block_size then
    if addr_dec (nth a bits 0) 1 then
      h <- Read a;
      Ret (Some h)
    else
      Ret None
  else
    Ret None.

Definition write a v' : prog (option unit) :=
  v <- Read 0;
  let bits := bits (value_to_bits v) in
  if lt_dec a block_size then
    if addr_dec (nth a bits 0) 1 then
      _ <- Write a v';
      Ret (Some tt)
    else
      Ret None
  else
    Ret None.

Definition free a : prog unit :=
  v <- Read 0;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  if lt_dec a block_size then
    if addr_dec (nth a bits 0) 1 then
      Write 0 (bits_to_value (Build_bitlist (upd a bits 0) (upd_valid_zero a bits valid)))
    else
      Ret tt
  else
    Ret tt.

(*
Theorem hoare_triple_pre_ex':
  forall T V (p: prog T) pre post crash,
  (forall (v: V), hoare_triple (fun a => pre v a) p post crash) ->
  hoare_triple (fun a => exists (v: V), pre v a) p post crash.
Proof.
  unfold hoare_triple; intros.
  destruct_lift H0; cleanup.
  eapply H; eauto.
Qed.

Theorem hoare_triple_pre_ex:
  forall T V (p: prog T) pre post crash F,
  (forall (v: V), hoare_triple (fun a => F * pre v a) p post crash) ->
  hoare_triple (fun a => F * exists (v: V), pre v a) p post crash.
Proof.
  intros.
  eapply hoare_triple_strengthen_pre.
  apply hoare_triple_pre_ex'.
  instantiate (1:= fun v a => F * pre v a).
  simpl; eauto.
  intros; cancel.
Qed.

Lemma upd_eq':
  forall (A V : Type) (AEQ : EqDec A) (m : mem) (a : A) (v : V),
    @upd _ _ AEQ m a v a = Some v.
Proof.
  intros; apply upd_eq; eauto.
Qed.


Theorem alloc_ok:
  forall dh v,
  << o >>
   (rep dh)
   (alloc v)
  << o', r >>
   (exists dh',
    rep dh' *
     [[(r = None /\ dh' = dh) \/
       (exists a, r = Some a /\ dh' = upd dh a v)%type]])
   (exists dh',
    rep dh' *
     [[(dh' = dh) \/
       (exists h, dh' = upd dh h v)%type]]).
Proof.
  intros.
  unfold alloc; simpl.
  unfold rep.
  repeat (apply hoare_triple_pre_ex; intros).

  eapply hoare_triple_pimpl;
  try solve [intros; simpl in *; eauto].
  eapply hoare_triple_strengthen_pre;
  [apply read_okay | intros; simpl; cancel].

  intros; simpl.
  destruct (addr_dec (value_to_nat r) 0); simpl.
  {
    intros; simpl. 
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
      [apply write_okay | intros; simpl; cancel].

    intros; simpl.
    destruct_pairs.
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
      [apply write_okay | intros; simpl; cancel].
    {
      intros; simpl.
      eapply hoare_triple_strengthen_pre.
      eapply hoare_triple_weaken_post_strong.
      eapply hoare_triple_weaken_crash_strong.
      apply ret_okay.  
      3: intros; simpl; cancel.
      
      intros; simpl;
        norm; [cancel|].
      eassign (upd dh 1 v).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;        
        destruct_lift H0; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.

      intros; simpl.
      norm; [cancel|].
      eassign (upd dh 1 v).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;
        destruct_lift H0; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.
    }
    
    all: intros; simpl in *;
      destruct_lift H;
      destruct_lift H0; cleanup;
        cancel; eauto.
  }
  destruct (addr_dec (value_to_nat r) 1); simpl.
  {
    intros; simpl. 
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
      [apply write_okay | intros; simpl; cancel].

    intros; simpl.
    destruct_pairs.
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply write_okay | intros; simpl; cancel].

    {
      intros; simpl.
      eapply hoare_triple_strengthen_pre.
      eapply hoare_triple_weaken_post_strong.
      eapply hoare_triple_weaken_crash_strong.
      apply ret_okay.  
      3: intros; simpl; cancel.
      
      intros; simpl;
        norm; [cancel|].
      eassign (upd dh 2 v).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;
        destruct_lift H0; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.

      intros; simpl.
      norm; [cancel|].
      eassign (upd dh 2 v).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;
        destruct_lift H0; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.
    }
    all: try solve [
      intros; simpl in *;
      destruct_lift H;
        destruct_lift H0; cleanup;
      cancel; eauto].      
  }
  destruct (addr_dec (value_to_nat r) 2); simpl.
  {
    intros; simpl. 
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply write_okay | intros; simpl; cancel].
    
    intros; simpl.
    destruct_pairs.
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply write_okay | intros; simpl; cancel].

    {
      intros; simpl.
      eapply hoare_triple_strengthen_pre.
      eapply hoare_triple_weaken_post_strong.
      eapply hoare_triple_weaken_crash_strong.
      apply ret_okay.  
      3: intros; simpl; cancel.
      
      intros; simpl;
        norm; [cancel|].
      eassign (upd dh 1 v).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;
        destruct_lift H0; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.

      intros; simpl.
      norm; [cancel|].
      eassign (upd dh 1 v).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;
        destruct_lift H0; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.
    }
    all: try solve [
      intros; simpl in *;
      destruct_lift H;
        destruct_lift H0; cleanup;
        norm; [cancel| intuition (eauto; try omega)]
      ].
  }

  {
      intros; simpl.
      eapply hoare_triple_strengthen_pre.
      eapply hoare_triple_weaken_post_strong.
      eapply hoare_triple_weaken_crash_strong.
      apply ret_okay.
      3: intros; simpl; rewrite emp_star_r; eauto.
      
      intros; simpl; destruct_lift H; cleanup.
      norm; [cancel| intuition (eauto; try omega)].

      intros; simpl; destruct_lift H; cleanup.
      norm; [cancel| intuition (eauto; try omega)].
  }

  all: try solve [
       intros; simpl; destruct_lift H; cleanup;
       norm; [cancel| intuition (eauto; try omega)]
           ].
Qed.

Theorem read_ok:
  forall a dh,
  << o >>
   (rep dh)
   (read a)
  << o', r >>
   (rep dh *
     [[(r = None /\ (dh a = None \/ a = 0 \/ a > 2)) \/
       (exists v, r = Some v /\ dh a = Some v)%type]])
   (rep dh).
Proof.
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


Theorem write_ok:
  forall dh a v,
  << o >>
   (rep dh)
   (write a v)
  << o', r >>
   (exists dh',
    rep dh' *
     [[(r = None /\ dh' = dh) \/
       (r = Some tt /\ dh a <> None /\ dh' = upd dh a v)%type]])
   (exists dh',
    rep dh' *
     [[(dh' = dh \/ (dh a <> None /\ dh' = upd dh a v))%type]]).
Proof.
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

Lemma delete_eq:
  forall A AEQ V (m: @mem A AEQ V) a,
    delete m a a = None.
Proof.
  intros; unfold delete; simpl.
  destruct (AEQ a a); intuition.
Qed.

Lemma delete_ne:
  forall A AEQ V (m: @mem A AEQ V) a a',
    a <> a' ->
    delete m a a' = m a'.
Proof.
  intros; unfold delete; simpl.
  destruct (AEQ a' a); subst; intuition.
Qed.
        

Theorem free_ok:
  forall dh a,
  << o >>
   (rep dh)
   (free a)
  << o', r >>
   (rep (delete dh a))
   (rep (delete dh a)).
Proof.
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
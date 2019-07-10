Require Import Primitives Omega.
Open Scope pred_scope.

Definition rep (dh: @mem addr addr_dec sealed_value) : @pred addr addr_dec Disk.valueset :=
  exists bitmap bl val1 val2,
    (0 |-> ((Public, bitmap), bl) *
     1 |-> val1 * 2 |-> val2 *
     [[value_to_nat bitmap < 4]] *
     [[dh 0 = None]] *
     [[value_to_nat bitmap = 0 ->
      dh 1 = None /\ dh 2 = None]] *
     [[value_to_nat bitmap = 1 ->
      dh 1 = Some (fst val1) /\ dh 2 = None]] *
     [[value_to_nat bitmap = 2 ->
      dh 1 = None /\ dh 2 = Some (fst val2)]] *
     [[value_to_nat bitmap = 3 ->
      dh 1 = Some (fst val1) /\ dh 2 = Some (fst val2)]] *
     [[forall n, n > 2 -> dh n = None]]).

Definition alloc : prog (option addr) :=
  sv <- Read 0;
  v <- Unseal sv;
  if addr_dec (value_to_nat v) 0 then
    zv <- Seal Public (nat_to_value 0);
    _ <- Write 1 zv;
    sh <- Seal Public (nat_to_value 1);
    _ <- Write 0 sh;
    Ret (Some 1)
  else if addr_dec (value_to_nat v) 1 then
    zv <- Seal Public (nat_to_value 0);
    _ <- Write 2 zv;
    sh <- Seal Public (nat_to_value 3);
    _ <- Write 0 sh;
    Ret (Some 2)
  else if addr_dec (value_to_nat v) 2 then
    zv <- Seal Public (nat_to_value 0);
    _ <- Write 1 zv;
    sh <- Seal Public (nat_to_value 3);
    _ <- Write 0 sh;
    Ret (Some 1)
  else
    Ret None.

Definition read a : prog (option handle) :=
  if addr_dec a 1 then
    sv <- Read 0;
    v <- Unseal sv;
    if addr_dec (value_to_nat v) 1 then
      h <- Read a;
      Ret (Some h)
    else if addr_dec (value_to_nat v) 3 then
      h <- Read a;
      Ret (Some h)
    else
      Ret None
  else if addr_dec a 2 then
    sv <- Read 0;
    v <- Unseal sv;
    if addr_dec (value_to_nat v) 2 then
      h <- Read a;
      Ret (Some h)
    else if addr_dec (value_to_nat v) 3 then
      h <- Read a;
      Ret (Some h)
    else
      Ret None
  else
    Ret None.

Definition write a h : prog (option unit) :=
  if addr_dec a 1 then
    sv <- Read 0;
    v <- Unseal sv;
    if addr_dec (value_to_nat v) 1 then
      _ <- Write a h;
      Ret (Some tt)
    else if addr_dec (value_to_nat v) 3 then
      h <- Write a h;
      Ret (Some tt)
    else
      Ret None
  else if addr_dec a 2 then
    sv <- Read 0;
    v <- Unseal sv;
    if addr_dec (value_to_nat v) 2 then
      h <- Write a h;
      Ret (Some tt)
    else if addr_dec (value_to_nat v) 3 then
      h <- Write a h;
      Ret (Some tt)
    else
      Ret None
  else
    Ret None.

Definition free a : prog unit :=
  if addr_dec a 1 then
    sv <- Read 0;
    v <- Unseal sv;
    if addr_dec (value_to_nat v) 1 then
      sh <- Seal Public (nat_to_value 0);
      Write 0 sh
    else if addr_dec (value_to_nat v) 3 then
      sh <- Seal Public (nat_to_value 2);
      Write 0 sh
    else
      Ret tt
  else if addr_dec a 2 then
    sv <- Read 0;
    v <- Unseal sv;
    if addr_dec (value_to_nat v) 2 then
      sh <- Seal Public (nat_to_value 0);
      Write 0 sh
    else if addr_dec (value_to_nat v) 3 then
      sh <- Seal Public (nat_to_value 1);
      Write 0 sh
    else
      Ret tt
  else
    Ret tt.


Theorem hoare_triple_pre_ex':
  forall T V (p: prog T) pre post crash,
  (forall (v: V), hoare_triple (fun a b c => pre v a b c) p post crash) ->
  hoare_triple (fun a b c => exists (v: V), pre v a b c) p post crash.
Proof.
  unfold hoare_triple; intros.
  destruct_lift H0; cleanup.
  eapply H; eauto.
Qed.

Theorem hoare_triple_pre_ex:
  forall T V (p: prog T) pre post crash F,
  (forall (v: V), hoare_triple (fun a b c => F * pre v a b c) p post crash) ->
  hoare_triple (fun a b c => F * exists (v: V), pre v a b c) p post crash.
Proof.
  intros.
  eapply hoare_triple_strengthen_pre.
  apply hoare_triple_pre_ex'.
  instantiate (1:= fun v a b c => F * pre v a b c).
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
  forall dh,
  << u, o, s >>
   (rep dh)
   (alloc)
  << o', s', r >>
   (exists dh',
    rep dh' *
     [[(r = None /\ dh' = dh) \/
       (exists h, r = Some h /\ dh' = upd dh h (Public, nat_to_value 0) /\ dh h = None)%type]])
   (exists dh',
    rep dh' *
     [[(dh' = dh) \/
       (exists h, dh' = upd dh h (Public, nat_to_value 0) /\ dh h = None)%type]]).
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
  eapply hoare_triple_pimpl;
  try solve [intros; simpl in *; eauto].
  eapply hoare_triple_strengthen_pre;
  [apply unseal_okay | intros; simpl; cancel].
  apply upd_eq; eauto.
  simpl; apply can_access_public.
  
  intros; simpl.
  destruct (addr_dec (value_to_nat r0) 0); simpl.
  {
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply seal_okay | intros; simpl; cancel].

    intros; simpl. 
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply write_okay | intros; simpl; cancel].
    apply upd_eq; eauto.

    intros; simpl.
    destruct_pairs.
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply seal_okay | intros; simpl; cancel].

    intros; simpl. 
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply write_okay | intros; simpl; cancel].
    apply upd_eq; eauto.

    {
      intros; simpl.
      eapply hoare_triple_strengthen_pre.
      eapply hoare_triple_weaken_post_strong.
      eapply hoare_triple_weaken_crash_strong.
      apply ret_okay.  
      3: intros; simpl; cancel.
      
      intros; simpl;
        norm; [cancel|].
      eassign (upd dh 1 (Public, nat_to_value 0)).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;
        destruct_lift H1; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.

      intros; simpl.
      norm; [cancel|].
      eassign (upd dh 1 (Public, nat_to_value 0)).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;
        destruct_lift H1; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.
    }
    all: try solve [
      intros; simpl in *;
      destruct_lift H;
        destruct_lift H1; cleanup;
      cancel; eauto].      
  }
  destruct (addr_dec (value_to_nat r0) 1); simpl.
  {
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply seal_okay | intros; simpl; cancel].

    intros; simpl. 
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply write_okay | intros; simpl; cancel].
    apply upd_eq; eauto.

    intros; simpl.
    destruct_pairs.
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply seal_okay | intros; simpl; cancel].

    intros; simpl. 
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply write_okay | intros; simpl; cancel].
    apply upd_eq; eauto.

    {
      intros; simpl.
      eapply hoare_triple_strengthen_pre.
      eapply hoare_triple_weaken_post_strong.
      eapply hoare_triple_weaken_crash_strong.
      apply ret_okay.  
      3: intros; simpl; cancel.
      
      intros; simpl;
        norm; [cancel|].
      eassign (upd dh 2 (Public, nat_to_value 0)).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;
        destruct_lift H1; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.

      intros; simpl.
      norm; [cancel|].
      eassign (upd dh 2 (Public, nat_to_value 0)).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;
        destruct_lift H1; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.
    }
    all: try solve [
      intros; simpl in *;
      destruct_lift H;
        destruct_lift H1; cleanup;
      cancel; eauto].      
  }
  destruct (addr_dec (value_to_nat r0) 2); simpl.
  {
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply seal_okay | intros; simpl; cancel].

    intros; simpl. 
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply write_okay | intros; simpl; cancel].
    apply upd_eq; eauto.

    intros; simpl.
    destruct_pairs.
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply seal_okay | intros; simpl; cancel].

    intros; simpl. 
    eapply hoare_triple_pimpl;
    try solve [intros; simpl in *; eauto].
    eapply hoare_triple_strengthen_pre;
    [apply write_okay | intros; simpl; cancel].
    apply upd_eq; eauto.

    {
      intros; simpl.
      eapply hoare_triple_strengthen_pre.
      eapply hoare_triple_weaken_post_strong.
      eapply hoare_triple_weaken_crash_strong.
      apply ret_okay.  
      3: intros; simpl; cancel.
      
      intros; simpl;
        norm; [cancel|].
      eassign (upd dh 1 (Public, nat_to_value 0)).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;
        destruct_lift H1; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.

      intros; simpl.
      norm; [cancel|].
      eassign (upd dh 1 (Public, nat_to_value 0)).
      rewrite nat_to_value_to_nat; eauto.
      rewrite upd_eq'.
      repeat rewrite upd_ne; eauto.
      destruct_lift H;
        destruct_lift H1; cleanup.
      intuition (eauto; try omega).
      rewrite upd_ne; eauto.
      omega.
    }
    all: try solve [
      intros; simpl in *;
      destruct_lift H;
        destruct_lift H1; cleanup;
        norm; [cancel| intuition (eauto; try omega)]
      ].
  }

  {
      intros; simpl.
      eapply hoare_triple_strengthen_pre.
      eapply hoare_triple_weaken_post_strong.
      eapply hoare_triple_weaken_crash_strong.
      apply ret_okay.
      eassign (((((0 |-> (Public, v, v0) ✶ F) ✶ 1 |-> v1) ✶ 2 |-> v2) ✶ ⟦⟦ r0 = v ⟧⟧)).
      
      intros; simpl; destruct_lift H; cleanup.
      norm; [cancel| intuition (eauto; try omega)].

      intros; simpl; destruct_lift H; cleanup.
      norm; [cancel| intuition (eauto; try omega)].

      intros; simpl; cancel.
  }

  all: try solve [
       intros; simpl; destruct_lift H; cleanup;
       norm; [cancel| intuition (eauto; try omega)]
           ].
Qed.


Theorem read_ok:
  forall a dh,
  << u, o, s >>
   (rep dh)
   (read a)
  << o', s', r >>
   (rep dh *
     [[(r = None /\ (dh a = None \/ a = 0 \/ a > 2)) \/
       (exists h v, r = Some h /\ dh a = Some v /\ s' h = Some v)%type]])
   (rep dh).
Proof.
  intros.
  unfold read; simpl.

  destruct (addr_dec a 1); subst.
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
    destruct (addr_dec (value_to_nat r0) 1); simpl.
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
        destruct_lift H1; cleanup;
          cancel; eauto.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1; cleanup;
          cancel; eauto.

      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        destruct_lift H2;
        cleanup;
          cancel; eauto.
      
      right.
      repeat eexists; intuition eauto.      
      apply upd_eq'.
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H1; cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

    destruct (addr_dec (value_to_nat r0) 3); simpl.
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
        destruct_lift H1; cleanup;
          cancel; eauto.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1; cleanup;
          cancel; eauto.

      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        destruct_lift H2;
        cleanup;
          cancel; eauto.
      
      right.
      repeat eexists; intuition eauto.      
      apply upd_eq'.
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H1; cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

      {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.

      eassign (F * rep dh * ⟦⟦ r0 = v ⟧⟧).
      destruct_lift H;
        destruct_lift H0;
        cleanup.
      intros; simpl in *; unfold rep; cancel.
      
      unfold rep; intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        cleanup.
      norm; [cancel| intuition (eauto; try omega)].
      

      intros; simpl in *.
      unfold rep;
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        cleanup;
      norm; [cancel| intuition (eauto; try omega)].
      
      left; split; eauto.
      left.
      destruct (addr_dec (value_to_nat v) 0); intuition.
      destruct (addr_dec (value_to_nat v) 2); intuition.
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H0; cleanup;
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
    [apply read_okay | intros; simpl; cancel].

    {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H1; cleanup;
          cancel; eauto.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1; cleanup;
          cancel; eauto.

      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        destruct_lift H2;
        cleanup;
          cancel; eauto.
      
      right.
      repeat eexists; intuition eauto.      
      apply upd_eq'.
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H1; cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

    destruct (addr_dec (value_to_nat r0) 3); simpl.
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
        destruct_lift H1; cleanup;
          cancel; eauto.
      
      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1; cleanup;
          cancel; eauto.

      intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        destruct_lift H2;
        cleanup;
          cancel; eauto.
      
      right.
      repeat eexists; intuition eauto.      
      apply upd_eq'.
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H1; cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    }

      {
      intros; simpl.
      eapply hoare_triple_weaken_post_weak.
      eapply hoare_triple_weaken_crash_strong.
      eapply hoare_triple_strengthen_pre.
      apply ret_okay.

      eassign (F * rep dh * ⟦⟦ r0 = v ⟧⟧).
      destruct_lift H;
        destruct_lift H0;
        cleanup.
      intros; simpl in *; unfold rep; cancel.
      
      unfold rep; intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        cleanup.
      norm; [cancel| intuition (eauto; try omega)].
      

      intros; simpl in *.
      unfold rep;
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        cleanup;
      norm; [cancel| intuition (eauto; try omega)].
      
      left; split; eauto.
      left.
      destruct (addr_dec (value_to_nat v) 0); intuition.
      destruct (addr_dec (value_to_nat v) 1); intuition.
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H0; cleanup;
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

      cancel.
      cancel.
      cancel.
      left; intuition.      
      right; omega.
  }
Qed.


Lemma exis_lift_absorb:
  forall A AEQ V T (P: T -> @pred A AEQ V) Q,
    (exists x, P x) * [[ Q ]] =p=> exists x, (P x * [[Q]]).
Proof.
  intros; cancel.
Qed.


Theorem write_ok:
  forall dh a h v,
  << u, o, s >>
   (rep dh * [[s h = Some v]])
   (write a h)
  << o', s', r >>
   (exists dh',
    rep dh' *
     [[(r = None /\ dh' = dh) \/
       (r = Some tt /\ dh' = upd dh a v)%type]])
   (exists dh',
    rep dh' *
     [[dh' = dh \/ dh' = upd dh a v]]).
Proof.
  intros.
  unfold write; simpl.

  destruct (addr_dec a 1); subst.
  {
    unfold rep.
    eapply hoare_triple_strengthen_pre.
    2: {
      intros.
      eassign (fun (u: user) (o:oracle) (s: Disk.store) => F
  ✶ ((exists (bitmap : value) (bl : list sealed_value) (val1 val2 : permission * value * list sealed_value),
        ((((((((0 |-> (Public, bitmap, bl) ✶ 1 |-> val1) ✶ 2 |-> val2) ✶ ⟦⟦ value_to_nat bitmap < 4 ⟧⟧)
             ✶ ⟦⟦ dh 0 = None ⟧⟧) ✶ ⟦⟦ value_to_nat bitmap = 0 -> dh 1 = None /\ dh 2 = None ⟧⟧)
           ✶ ⟦⟦ value_to_nat bitmap = 1 -> dh 1 = Some (fst val1) /\ dh 2 = None ⟧⟧)
          ✶ ⟦⟦ value_to_nat bitmap = 2 -> dh 1 = None /\ dh 2 = Some (fst val2) ⟧⟧)
         ✶ ⟦⟦ value_to_nat bitmap = 3 -> dh 1 = Some (fst val1) /\ dh 2 = Some (fst val2) ⟧⟧)
          ✶ ⟦⟦ forall n : nat, n > 2 -> dh n = None ⟧⟧  ✶ ⟦⟦ s h = Some v ⟧⟧))).
      simpl; cancel.
    }
    
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
    destruct (addr_dec (value_to_nat r0) 1); simpl.
    {
      eapply hoare_triple_pimpl;
        try solve [intros; simpl in *; eauto].
      eapply hoare_triple_strengthen_pre;
        [apply write_okay | intros; simpl; cancel].
      destruct_lift H; destruct_lift H0; cleanup.
      rewrite upd_ne; eauto.
      intro x; subst; cleanup.
      
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply ret_okay.
        
        intros; simpl in *.
        eassign ((((2 |-> v3 ✶ F) ✶ 0 |-> (Public, r0, v1)) ✶ ((1 |-> (v, fst v2 :: snd v2))))).
        cancel; eauto.
        
        intros; simpl in *.
        destruct v; simpl in *.
        norm; [cancel|].
        eassign (upd dh 1 (p, v)).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.

        intros; simpl in *.
        destruct v; simpl in *.
        norm; [cancel|].
        eassign (upd dh 1 (p, v)).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
      }        
      intros; simpl in *.
      destruct v; simpl in *.
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
        [apply write_okay | intros; simpl; cancel].
      destruct_lift H; destruct_lift H0; cleanup.
      rewrite upd_ne; eauto.
      intro x; subst; cleanup.
      
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply ret_okay.
        
        intros; simpl in *.
        eassign ((((2 |-> v3 ✶ F) ✶ 0 |-> (Public, r0, v1)) ✶ ((1 |-> (v, fst v2 :: snd v2))))).
        cancel; eauto.
        
        intros; simpl in *.
        destruct v; simpl in *.
        norm; [cancel|].
        eassign (upd dh 1 (p, v)).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.

        intros; simpl in *.
        destruct v; simpl in *.
        norm; [cancel|].
        eassign (upd dh 1 (p, v)).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
      }        
      intros; simpl in *.
      destruct v; simpl in *.
      destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
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
        destruct_lift H0;
        cleanup.
      intros; simpl in *; unfold rep; cancel.
      
      unfold rep; intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        cleanup.
      norm; [cancel| intuition (eauto; try omega)].
      

      intros; simpl in *.
      unfold rep;
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        cleanup;
      norm; [cancel| intuition (eauto; try omega)].
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H0; cleanup;
        norm; [cancel| intuition (eauto; try omega)].
    intros; simpl in *;
      destruct_lift H;
      cleanup;
      norm; [cancel| intuition (eauto; try omega)].
  }
  

  destruct (addr_dec a 2); subst.
   {
    unfold rep.
    eapply hoare_triple_strengthen_pre.
    2: {
      intros.
      eassign (fun (u: user) (o:oracle) (s: Disk.store) => F
  ✶ ((exists (bitmap : value) (bl : list sealed_value) (val1 val2 : permission * value * list sealed_value),
        ((((((((0 |-> (Public, bitmap, bl) ✶ 1 |-> val1) ✶ 2 |-> val2) ✶ ⟦⟦ value_to_nat bitmap < 4 ⟧⟧)
             ✶ ⟦⟦ dh 0 = None ⟧⟧) ✶ ⟦⟦ value_to_nat bitmap = 0 -> dh 1 = None /\ dh 2 = None ⟧⟧)
           ✶ ⟦⟦ value_to_nat bitmap = 1 -> dh 1 = Some (fst val1) /\ dh 2 = None ⟧⟧)
          ✶ ⟦⟦ value_to_nat bitmap = 2 -> dh 1 = None /\ dh 2 = Some (fst val2) ⟧⟧)
         ✶ ⟦⟦ value_to_nat bitmap = 3 -> dh 1 = Some (fst val1) /\ dh 2 = Some (fst val2) ⟧⟧)
          ✶ ⟦⟦ forall n : nat, n > 2 -> dh n = None ⟧⟧  ✶ ⟦⟦ s h = Some v ⟧⟧))).
      simpl; cancel.
    }
    
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
        [apply write_okay | intros; simpl; cancel].
      destruct_lift H; destruct_lift H0; cleanup.
      rewrite upd_ne; eauto.
      intro x; subst; cleanup.
      
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply ret_okay.
        
        intros; simpl in *.
        eassign ((((1 |-> v2 ✶ F) ✶ 0 |-> (Public, r0, v1)) ✶ 2 |-> (v, fst v3 :: snd v3))).
        cancel; eauto.
        
        intros; simpl in *.
        destruct v; simpl in *.
        norm; [cancel|].
        eassign (upd dh 2 (p, v)).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.

        intros; simpl in *.
        destruct v; simpl in *.
        norm; [cancel|].
        eassign (upd dh 2 (p, v)).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
      }        
      intros; simpl in *.
      destruct v; simpl in *.
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
        [apply write_okay | intros; simpl; cancel].
      destruct_lift H; destruct_lift H0; cleanup.
      rewrite upd_ne; eauto.
      intro x; subst; cleanup.
      
      {
        intros; simpl.
        eapply hoare_triple_weaken_post_weak.
        eapply hoare_triple_weaken_crash_strong.
        eapply hoare_triple_strengthen_pre.
        apply ret_okay.
        
        intros; simpl in *.
        eassign ((((1 |-> v2 ✶ F) ✶ 0 |-> (Public, r0, v1)) ✶ 2 |-> (v, fst v3 :: snd v3))).
        cancel; eauto.
        
        intros; simpl in *.
        destruct v; simpl in *.
        norm; [cancel|].
        eassign (upd dh 2 (p, v)).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.

        intros; simpl in *.
        destruct v; simpl in *.
        norm; [cancel|].
        eassign (upd dh 2 (p, v)).
        rewrite upd_eq'.
        repeat rewrite upd_ne; eauto.
        destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
          cleanup;
          intuition (eauto; try omega).
        rewrite upd_ne; eauto; omega.
      }        
      intros; simpl in *.
      destruct v; simpl in *.
      destruct_lift H;
          destruct_lift H0;
          destruct_lift H1;
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
        destruct_lift H0;
        cleanup.
      intros; simpl in *; unfold rep; cancel.
      
      unfold rep; intros; simpl in *.
      destruct_lift H;
        destruct_lift H0;
        cleanup.
      norm; [cancel| intuition (eauto; try omega)].
      

      intros; simpl in *.
      unfold rep;
      destruct_lift H;
        destruct_lift H0;
        destruct_lift H1;
        cleanup;
      norm; [cancel| intuition (eauto; try omega)].
    }
    intros; simpl in *;
      destruct_lift H;
      destruct_lift H0; cleanup;
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
      all: cancel.
   }
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
  << u, o, s >>
   (rep dh)
   (free a)
  << o', s', r >>
   (rep (delete dh a))
   (exists dh',
    rep dh' *
     [[dh' = dh \/ dh' = delete dh a]]).
Proof.
  intros.
  unfold free; simpl.

  destruct (addr_dec a 1); subst.
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
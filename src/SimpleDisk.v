Require Import Primitives Omega.
Open Scope pred_scope.

Axiom nat_to_value : nat -> value.
Axiom value_to_nat : value -> nat.
Axiom nat_to_value_to_nat:
  forall n, value_to_nat (nat_to_value n) = n.
Axiom value_to_nat_to_value:
  forall v, nat_to_value (value_to_nat v) = v.

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
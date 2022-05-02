Require Export List BaseTypes.
Require Export Disk Primitives.Automation ListUtils.
Require Export Primitives.Facts Mem TotalMem.
Export ListNotations.

Require Import  FunctionalExtensionality Lia.


Definition apply_mem {A AEQ V} (m: @mem A AEQ V) (tm: @total_mem A AEQ V):=
  fun a => match m a with
        | Some v => v
        | None => tm a
        end.


(*** LEMMAS ***)
  Lemma upd_batch_noop:
    forall A (AEQ: EqDec A) V (l_a: list A) (l_v: list V) m tm,
      Mem.upd_batch m l_a l_v = m ->
      Forall (fun a => m a = None) l_a -> 
      length l_a = length l_v ->
      upd_batch tm l_a l_v = tm.
  Proof.
    induction l_a; simpl; intros; eauto.
    destruct l_v; eauto.
    inversion H0; cleanup.
    destruct (in_dec AEQ a l_a).
    {
      rewrite Mem.upd_batch_upd_in_noop in H; eauto.
      rewrite upd_batch_upd_in_noop; eauto.
    }
    {
      rewrite Mem.upd_batch_upd in H; eauto.
      eapply equal_f with (x:= a) in H.              
      rewrite Mem.upd_eq in *; eauto; cleanup.
    }
  Qed.

  Lemma list_upd_batch_noop:
    forall A (AEQ: EqDec A) V (l_l_a: list (list A)) (l_l_v: list (list V)) m,
      Mem.list_upd_batch m l_l_a l_l_v = m ->
      Forall (Forall (fun a => m a = None)) l_l_a ->
      Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v ->
      (forall tm, list_upd_batch tm l_l_a l_l_v = tm).
  Proof.
    do 4 intro.
    eapply rev_ind with
        (P:= fun l_l_a =>
               forall (l_l_v : list (list V)) (m : mem),
                 Mem.list_upd_batch m l_l_a l_l_v = m ->
                 Forall (Forall (fun a : A => m a = None)) l_l_a ->                      
                 Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v ->
                 forall tm : total_mem, list_upd_batch tm l_l_a l_l_v = tm);
    simpl; intros; eauto.
    {
      destruct (nil_or_app l_l_v); cleanup.
      destruct (l++[x]); simpl; eauto.
      
      
      eapply_fresh forall2_length in H2.
      repeat rewrite app_length in *; simpl in *.
      eapply_fresh Forall2_app_split in H2; cleanup; eauto; try lia.
      eapply_fresh forall_app_l in H1.
      eapply_fresh forall_app_r in H1.
      rewrite Mem.list_upd_batch_app in H0; simpl in *; try lia.
      inversion Hx0; cleanup.
      rewrite list_upd_batch_app; simpl in *; try lia.
      destruct (nil_or_app x); cleanup;
      simpl in *; eauto.
      destruct (nil_or_app x0); cleanup.
      destruct (x3 ++ [x2]); simpl in *; eauto.
      inversion H4; cleanup.
      repeat rewrite app_length in *; simpl in *.
      rewrite Mem.upd_batch_app in *; simpl in *; try lia.
      apply forall_app_l in H7; inversion H7; cleanup.
      apply equal_f with (x:= x2) in H0.
      rewrite Mem.upd_eq in *; eauto; cleanup.
    }
  Qed.

  Lemma upd_batch_noop_empty_mem:
    forall A (AEQ: EqDec A) V (l_a: list A) (l_v: list V) tm,
      Mem.upd_batch empty_mem l_a l_v = empty_mem ->
      length l_a = length l_v ->
      upd_batch tm l_a l_v = tm.
  Proof.
    induction l_a; simpl; intros; eauto.
    destruct l_v; eauto.
    destruct (in_dec AEQ a l_a).
    {
      rewrite Mem.upd_batch_upd_in_noop in H; eauto.
      rewrite upd_batch_upd_in_noop; eauto.
    }
    {
      rewrite Mem.upd_batch_upd in H; eauto.
      eapply equal_f with (x:= a) in H.              
      rewrite Mem.upd_eq in *; eauto.
      unfold empty_mem in *; congruence.
    }
  Qed.
  
  Lemma upd_batch_eq_empty_mem:
    forall A (AEQ: EqDec A) V (l_a: list A) (l_v: list V) m,
      Mem.upd_batch m l_a l_v = empty_mem ->
      m = empty_mem /\
      (l_a = [] \/ l_v = []).
  Proof.
    induction l_a; simpl; intros; eauto.
    destruct l_v; eauto.
    eapply IHl_a in H.
    destruct H.
    eapply equal_f with (x:=a) in H.
    rewrite Mem.upd_eq in H; eauto.
    unfold empty_mem in *; congruence.
  Qed.

  Lemma list_upd_batch_eq_empty_mem:
    forall A (AEQ: EqDec A) V (l_l_a: list (list A)) (l_l_v: list (list V)) m,
      Mem.list_upd_batch m l_l_a l_l_v = empty_mem ->
      m = empty_mem /\
      (forall tm, list_upd_batch tm l_l_a l_l_v = tm).
  Proof.
    induction l_l_a; simpl; intros; eauto.
    destruct l_l_v; eauto.
    eapply IHl_l_a in H.
    destruct H.
    apply upd_batch_eq_empty_mem in H.
    destruct H.
    split; eauto.
    intros; rewrite H0.            
    intuition; subst; simpl; eauto.
    destruct a; eauto.
  Qed.

  Lemma skipn_eq_nil:
    forall T (l: list T) n,
      skipn n l = nil ->
      l = [] \/ n >= length l.
  Proof.
    induction l; simpl; intros; eauto.
    destruct n; simpl in *; eauto.
    apply IHl in H.
    intuition subst; simpl; try lia.
  Qed.

  Fixpoint remove_by_fst {A} {AEQ: EqDec A} {V} (a: A) (l_av: list (A * V)) :=
    match l_av with
    | nil => nil
    | av :: l_av' =>
      if (AEQ a (fst av)) then
        remove_by_fst a l_av'
      else
        av :: remove_by_fst a l_av'
    end.

  Lemma remove_by_fst_not_in:
    forall A (AEQ: EqDec A) V (l: list (A * V)) a,
      ~ In a (map fst (remove_by_fst a l)).
  Proof.
    induction l; simpl; eauto.
    intros.
    destruct (AEQ a0 (fst a)); subst; eauto.
    simpl; intuition eauto.
  Qed.

  Lemma remove_by_fst_incl:
    forall A (AEQ: EqDec A) V (l: list (A * V)) a,
      incl (remove_by_fst a l) l.
  Proof.
    unfold incl; induction l; simpl; intros; eauto.
    destruct (AEQ a0 (fst a)); subst; eauto.
    inversion H; simpl in *; intuition eauto.
  Qed.
  
  Lemma upd_batch_upd_remove_by_fst:
    forall A AEQ V l_a l_v (m: @mem A AEQ V) a v,
    let l_av := remove_by_fst a (combine l_a l_v) in
      Mem.upd (Mem.upd_batch m l_a l_v) a v =
      Mem.upd (Mem.upd_batch m (map fst l_av) (map snd l_av)) a v.
  Proof.
    unfold incl; induction l_a; simpl; intros; eauto.
    {
      destruct l_v; simpl; eauto.
      destruct (AEQ a0 a); subst.
      rewrite IHl_a.
      rewrite Mem.upd_batch_upd; eauto.
      rewrite Mem.upd_repeat; eauto.
      apply remove_by_fst_not_in.

      rewrite IHl_a; simpl; intuition eauto.
    }
  Qed.

   Lemma upd_batch_upd_remove_by_fst_total:
    forall A AEQ V l_a l_v (m: @total_mem A AEQ V) a v,
    let l_av := remove_by_fst a (combine l_a l_v) in
      upd (upd_batch m l_a l_v) a v =
      upd (upd_batch m (map fst l_av) (map snd l_av)) a v.
  Proof.
    unfold incl; induction l_a; simpl; intros; eauto.
    {
      destruct l_v; simpl; eauto.
      destruct (AEQ a0 a); subst.
      rewrite IHl_a.
      rewrite upd_batch_upd; eauto.
      rewrite upd_repeat; eauto.
      apply remove_by_fst_not_in.

      rewrite IHl_a; simpl; intuition eauto.
    }
  Qed.

  Lemma upd_batch_dedup_by_fst:
    forall A AEQ V l_a l_v (m: @mem A AEQ V),
    let l_av := dedup_by_fst AEQ (combine l_a l_v) in
    length l_a = length l_v ->
    Mem.upd_batch m l_a l_v =
    Mem.upd_batch m (map fst l_av) (map snd l_av).
  Proof.
    induction l_a; simpl; intros; eauto.
    {
      destruct l_v; simpl; eauto.
      rewrite map_fst_combine.
      destruct (in_dec AEQ a l_a); subst.
      rewrite Mem.upd_batch_upd_in_noop; eauto.
      simpl; eauto.
      simpl in *; lia.
    }
  Qed.

  Lemma upd_batch_dedup_by_fst_total:
    forall A AEQ V l_a l_v (m: @total_mem A AEQ V),
    let l_av := dedup_by_fst AEQ (combine l_a l_v) in
    length l_a = length l_v ->
    upd_batch m l_a l_v =
    upd_batch m (map fst l_av) (map snd l_av).
  Proof.
    induction l_a; simpl; intros; eauto.
    {
      destruct l_v; simpl; eauto.
      rewrite map_fst_combine.
      destruct (in_dec AEQ a l_a); subst.
      rewrite upd_batch_upd_in_noop; eauto.
      simpl; eauto.
      simpl in *; lia.
    }
  Qed.

  Fixpoint flatten {A} (l_l_a: list (list A)) :=
    match l_l_a with
    | nil => nil
    | l_a :: l_l_a' =>
      l_a ++ flatten l_l_a'
    end.

  Lemma flatten_app:
    forall A (l1 l2: list (list A)),
      flatten (l1 ++ l2) = flatten l1 ++ flatten l2.
  Proof.
    induction l1; simpl; intros; eauto.
    rewrite <- app_assoc; eauto.
    rewrite IHl1; eauto.
  Qed.

  Lemma flatten_length_eq:
    forall A V l1 l2,
      Forall2 (fun (l_a0 : list A) (l_v0 : list V) => length l_a0 = length l_v0) l1 l2 ->
      length (flatten l1) = length (flatten l2).
  Proof.
    induction l1; simpl; intros; eauto.
    apply forall2_length in H; destruct l2; simpl in *; lia.
    eapply_fresh forall2_length in H; destruct l2; simpl in *; try lia.
    inversion H; cleanup.
    repeat rewrite app_length.
    erewrite IHl1; eauto; lia.
  Qed.

  Lemma list_upd_batch_to_upd_batch:
    forall A AEQ V l_a l_v (m: @mem A AEQ V),
    Forall2 (fun l_a l_v => length l_a = length l_v) l_a l_v ->
    Mem.list_upd_batch m l_a l_v =
    Mem.upd_batch m (flatten l_a) (flatten l_v).
  Proof.
    do 4 intro.
    eapply rev_ind with
        (P:= fun l_a =>
        forall (l_v : list (list V)) (m : mem),
  Forall2 (fun (l_a0 : list A) (l_v0 : list V) => length l_a0 = length l_v0) l_a l_v ->
  Mem.list_upd_batch m l_a l_v = Mem.upd_batch m (flatten l_a) (flatten l_v));
    simpl; intros; eauto.
    {
      eapply_fresh forall2_length in H0.
      rewrite app_length in *; simpl in *.      
      destruct (nil_or_app l_v); subst; simpl in *; try lia.
      cleanup.
      rewrite app_length in *; simpl in *.
      eapply Forall2_app_split in H0; cleanup; try lia.
      rewrite Mem.list_upd_batch_app; try lia.
      simpl.
      repeat rewrite flatten_app; simpl.
      repeat rewrite app_nil_r.
      rewrite Mem.upd_batch_app.
      rewrite H; eauto; lia.
      apply flatten_length_eq; eauto.
    }
  Qed.

   Lemma list_upd_batch_to_upd_batch_total:
    forall A AEQ V l_a l_v (m: @total_mem A AEQ V),
    Forall2 (fun l_a l_v => length l_a = length l_v) l_a l_v ->
    list_upd_batch m l_a l_v =
    upd_batch m (flatten l_a) (flatten l_v).
  Proof.
    do 4 intro.
    eapply rev_ind with
        (P:= fun l_a =>
        forall (l_v : list (list V)) (m : total_mem),
  Forall2 (fun (l_a0 : list A) (l_v0 : list V) => length l_a0 = length l_v0) l_a l_v ->
  list_upd_batch m l_a l_v = upd_batch m (flatten l_a) (flatten l_v));
    simpl; intros; eauto.
    {
      eapply_fresh forall2_length in H0.
      rewrite app_length in *; simpl in *.      
      destruct (nil_or_app l_v); subst; simpl in *; try lia.
      cleanup.
      rewrite app_length in *; simpl in *.
      eapply Forall2_app_split in H0; cleanup; try lia.
      rewrite list_upd_batch_app; try lia.
      simpl.
      repeat rewrite flatten_app; simpl.
      repeat rewrite app_nil_r.
      rewrite upd_batch_app.
      rewrite H; eauto; lia.
      apply flatten_length_eq; eauto.
    }
  Qed.
  
  Lemma upd_batch_eq_upd_batch_total:
    forall A AEQ V l_av1 l_av2 (tm: @total_mem A AEQ V) m,
      let l_a1 := map fst l_av1 in
      let l_a2 := map fst l_av2 in
      let l_v1 := map snd l_av1 in
      let l_v2 := map snd l_av2 in
      
      Mem.upd_batch m l_a1 l_v1 =
      Mem.upd_batch m l_a2 l_v2 ->
      Forall (fun a => m a = None) l_a1 ->
      Forall (fun a => m a = None) l_a2 ->
      NoDup l_a1 ->
      NoDup l_a2 ->
      upd_batch tm l_a1 l_v1 =
      upd_batch tm l_a2 l_v2.
  Proof.
    induction l_av1; simpl; intros.
    { (** l_av1 = [] **)
      symmetry in H; eapply upd_batch_noop in H; eauto.
      repeat rewrite map_length; eauto.
    }
    (** l_av1 = a::l **)
    inversion H0; cleanup; clear H0.
    inversion H2; cleanup; clear H2.
    destruct l_av2; subst; simpl in *.
    {(** l_a2 = [] **)
      rewrite Mem.upd_batch_upd in *; eauto.
      eapply equal_f with (x:= fst a) in H.
      rewrite Mem.upd_eq in *; eauto; cleanup.
    }
    {(** l_a2 = a'::l' **)            
      inversion H1; cleanup; clear H1.
      inversion H3; cleanup; clear H3.
      destruct a, p; simpl in *.
      destruct (AEQ a a0); subst.
      {(** a = a0 **)
        assert_fresh (v = v0). {
          apply equal_f with (x:= a0) in H.                
          do 2 rewrite Mem.upd_batch_upd in *; eauto.
          do 2 rewrite Mem.upd_eq in *; eauto; congruence.
        }
        subst.
        eapply IHl_av1; eauto.
        {
          eapply Forall_forall; intros; intuition.
          destruct (AEQ a0 x); subst; intuition.
          rewrite Mem.upd_ne; eauto.
          eapply Forall_forall in H7; eauto.
        }
        {
          eapply Forall_forall; intros; intuition.
          destruct (AEQ a0 x); subst; intuition.
          rewrite Mem.upd_ne; eauto.
          eapply Forall_forall in H9; eauto.
        }
      }
      {(** a <> a0 **)
        destruct (in_dec AEQ a (map fst l_av2)).
        {(** In a (map fst l_av2) **)
          eapply_fresh in_map_iff in i; cleanup.
          eapply_fresh in_split in H1; eauto; cleanup.
          repeat rewrite map_app in *; simpl in *.
          rewrite Mem.upd_batch_app in H; eauto.
          rewrite upd_batch_app.
          simpl in *.
          assert_fresh (v = snd x). {
            do 2 rewrite Mem.upd_batch_upd in H; eauto.
            apply equal_f with (x:= fst x) in H.                
            do 2 rewrite Mem.upd_eq in *; eauto; congruence.
            intros Hx.
            apply NoDup_app_r in H10; inversion H10; eauto.
          }
          subst.
          rewrite <- Mem.upd_batch_upd in H; eauto.
          rewrite Mem.upd_comm in H; eauto.
          rewrite Mem.upd_to_upd_batch_singleton with (a:= a0) in H .
          do 2 rewrite <- Mem.upd_batch_app in H; eauto.
          replace ([a0] ++ map fst x0 ++ map fst x1)
            with (map fst ((a0, v0) :: x0 ++ x1)) in H.
          replace ([v0] ++ map snd x0 ++ map snd x1)
            with (map snd ((a0, v0) :: x0 ++ x1)) in H.
          eapply IHl_av1 in H; eauto.
          rewrite H.
          simpl.
          rewrite <- upd_batch_upd; eauto.
          rewrite upd_comm.
          repeat rewrite map_app;
          rewrite upd_batch_app; eauto.
          all: try solve [repeat rewrite map_length; eauto].
          all: try solve [simpl; repeat rewrite map_app; eauto].
          {
            eapply NoDup_remove_2 in H10.
            intros Hx; apply H10.
            apply in_app_iff; eauto.
          }
          {
            eapply Forall_forall; intros.
            eapply Forall_forall in H7; eauto.
            destruct (AEQ x2 (fst x)); subst; intuition.
            rewrite Mem.upd_ne; eauto.
          }
          {
            simpl.
            eapply NoDup_remove_2 in H10.
            constructor; eauto.
            rewrite Mem.upd_ne; eauto.
            rewrite map_app; simpl.
            apply Forall_forall; intros.
            destruct (AEQ x2 (fst x)); subst; intuition.
            rewrite Mem.upd_ne; eauto.
            eapply Forall_forall in H9; eauto.
            apply in_app_iff in H0.
            apply in_app_iff; simpl; intuition eauto.
          }
          {
            eapply NoDup_remove_1 in H10.
            simpl; rewrite map_app; constructor; eauto.
            
            intros Hx; apply H2.
            apply in_app_iff in Hx.
            apply in_app_iff; simpl; intuition eauto.
          }
          {
            eapply NoDup_remove_2 in H10.
            intros Hx; apply H10.
            apply in_app_iff; eauto.
          }
        }
        {(** ~In a (map fst l_av2) **)
          eapply equal_f with (x:= a) in H.
          do 2 rewrite Mem.upd_batch_ne in H; eauto.
          rewrite Mem.upd_eq in H; eauto.
          rewrite Mem.upd_ne in H; eauto; cleanup.
        }
      }
    }
  Qed.

  Lemma in_dedup_by_fst:
      forall A AEQ B (l: list (A * B)) ab,
        In ab (dedup_by_fst AEQ l) ->
        In ab l.
    Proof.
      induction l; simpl; intros; eauto.
      destruct (in_dec AEQ (fst a) (map fst l)); eauto.
      inversion H; subst; eauto.
    Qed.

    
    Lemma in_flatten:
      forall A (l_l_a: list (list A)) a,
        In a (flatten l_l_a) ->
        exists l_a, In l_a l_l_a /\ In a l_a.
    Proof.
      induction l_l_a; simpl; intros; eauto.
      intuition.
      apply in_app_iff in H; intuition eauto.
      apply IHl_l_a in H0; destruct H0; intuition eauto.
    Qed.

          Lemma NoDup_map_fst_dedup_by_fst:
        forall A AEQ B (l:list (A * B)),
          NoDup (map fst (dedup_by_fst AEQ l)).
      Proof.
        induction l; simpl; intros; eauto.
        constructor.
        destruct (in_dec AEQ (fst a) (map fst l)); eauto.
        simpl; constructor; eauto.
        intros Hx.
        apply in_map_iff in Hx; cleanup.
        apply in_dedup_by_fst in H0; eauto.
        rewrite <- H in *.
        apply n; apply in_map; eauto.
      Qed.


  Lemma list_upd_batch_eq_list_upd_batch_total:
    forall A AEQ V l_a1 l_v1 l_a2 l_v2 (tm: @total_mem A AEQ V) m,
      Mem.list_upd_batch m l_a1 l_v1 =
      Mem.list_upd_batch m l_a2 l_v2 ->
      Forall (Forall (fun a => m a = None)) l_a1 ->
      Forall (Forall (fun a => m a = None)) l_a2 ->
      Forall2 (fun l_a l_v => length l_a = length l_v) l_a1 l_v1 ->
      Forall2 (fun l_a l_v => length l_a = length l_v) l_a2 l_v2 ->
      list_upd_batch tm l_a1  l_v1 =
      list_upd_batch tm l_a2 l_v2.
  Proof.
    intros.
    do 2 rewrite list_upd_batch_to_upd_batch in *; eauto.
    setoid_rewrite list_upd_batch_to_upd_batch_total; eauto.
    setoid_rewrite upd_batch_dedup_by_fst_total.
    eapply upd_batch_eq_upd_batch_total; eauto.            
    repeat rewrite <- upd_batch_dedup_by_fst; eauto.
    all: try solve [eapply flatten_length_eq; eauto].
    apply Forall_forall; intros.
    apply in_map_iff in H4; cleanup.
    apply in_dedup_by_fst in H5.
    destruct x0; simpl in *;
    apply in_combine_l in H5.
    apply in_flatten in H5; cleanup.
    eapply Forall_forall in H0; eauto.
    eapply Forall_forall in H0; eauto.

    apply Forall_forall; intros.
    apply in_map_iff in H4; cleanup.
    apply in_dedup_by_fst in H5.
    destruct x0; simpl in *;
    apply in_combine_l in H5.
    apply in_flatten in H5; cleanup.
    eapply Forall_forall in H1; eauto.
    eapply Forall_forall in H1; eauto.

    apply NoDup_map_fst_dedup_by_fst.
    apply NoDup_map_fst_dedup_by_fst. 
  Qed.
  
  Lemma empty_mem_list_upd_batch_eq_list_upd_batch_total:
    forall A AEQ V l_a1 l_v1 l_a2 l_v2 (tm: @total_mem A AEQ V),
      Mem.list_upd_batch empty_mem l_a1 l_v1 =
      Mem.list_upd_batch empty_mem l_a2 l_v2 ->
      Forall2 (fun l_a l_v => length l_a = length l_v) l_a1 l_v1 ->
      Forall2 (fun l_a l_v => length l_a = length l_v) l_a2 l_v2 ->
      list_upd_batch tm l_a1  l_v1 =
      list_upd_batch tm l_a2 l_v2.
  Proof.
    intros.
    eapply list_upd_batch_eq_list_upd_batch_total; eauto.
    eapply Forall_forall; intuition.
    eapply Forall_forall; intuition.
    eapply Forall_forall; intuition.
    eapply Forall_forall; intuition.
  Qed.


  
    Lemma upd_batch_in_some_total_mem :
      forall A AEQ V l_a l_v (m: @mem A AEQ V) (tm: @total_mem A AEQ V) a v,
        Mem.upd_batch m l_a l_v a = Some v ->
        m a = None ->
        NoDup l_a ->
        upd_batch tm l_a l_v a = v.
    Proof.
      induction l_a; simpl; intros; try congruence.
      destruct l_v; simpl; try congruence.
      destruct (AEQ a a0); subst.
      inversion H1; cleanup.
      rewrite upd_batch_upd; eauto.
      rewrite Mem.upd_batch_upd in H; eauto.
      rewrite Mem.upd_eq in H; eauto.
      rewrite upd_eq; eauto.
      congruence.
      eapply IHl_a; eauto.
      rewrite Mem.upd_ne; eauto.
      inversion H1; eauto.
    Qed.





Fixpoint repeated_apply {A B} (f: A -> B -> A) a l_b :=
  match l_b with
    | nil => a
    | b:: l_b' =>
      f (repeated_apply f a l_b') b
  end.

Lemma seln_repeated_apply_updn :
  forall V l_b (l: list V) v n def,
    ~ In n l_b ->
    seln (repeated_apply (fun l0 a0 => updn l0 a0 v) l l_b)
         n def = seln l n def.
Proof.
  induction l_b; simpl; eauto. 
  intros; rewrite seln_updn_ne; intuition.
Qed.

Lemma repeated_apply_length :
  forall A B l_b (l: list A) (f: list A -> B -> list A),
    (forall b l, length (f l b) = length l) ->
    length (repeated_apply f l l_b) = length l.
Proof.
  induction l_b; simpl; intros; eauto.
  rewrite H; eauto.
Qed.

Lemma repeated_apply_delete_comm:
     forall  A AEQ V (l_a: list A) (m: @mem A AEQ V) a,
       Mem.delete (repeated_apply (@Mem.delete A V AEQ) m l_a) a =
       repeated_apply (@Mem.delete A V AEQ) (Mem.delete m a) l_a.
   Proof.
     induction l_a; simpl; intros; eauto.
     rewrite <- IHl_a.
     destruct (AEQ a a0); subst; eauto.
     rewrite Mem.delete_comm; eauto.
   Qed.

   Lemma repeated_apply_updn_comm:
     forall V (l_a: list addr) (l: list V) a v v',
       ~ In a l_a ->
       updn (repeated_apply (fun l a => updn l a v) l l_a) a v' =
       repeated_apply (fun l a => updn l a v) (updn l a v') l_a.
   Proof.
     induction l_a; simpl; intros; eauto.
     rewrite <- IHl_a; intuition.
     rewrite updn_comm; intuition.
   Qed.

   Lemma repeated_apply_delete_not_in :
     forall A AEQ V (l_a: list A) m a,
       ~In a l_a ->
       repeated_apply (@Mem.delete A V AEQ) m l_a a =
       m a.
   Proof.
     induction l_a; simpl; intros; eauto.
     rewrite Mem.delete_ne; intuition.
   Qed.

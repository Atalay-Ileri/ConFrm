Require Import Lia Datatypes PeanoNat Compare_dec Framework TotalMem FSParameters Log Log.Specs.
Require Import DiskLayer CryptoDiskLayer CacheLayer CachedDiskLayer.
Require Import FunctionalExtensionality.

(** Cache uses disk addresses but its functions take data region addresses 
    and converts them to disk addresses to use *)
Local Fixpoint write_batch_to_cache al vl :=
  match al, vl with
  | a::al', v::vl' =>
    _ <- |CDCO| Write a v;
    write_batch_to_cache al' vl'           
  | _, _ => Ret tt
 end.

Definition Forall_dec {A} (P: A -> Prop) (P_dec: forall a: A, {P a}+{~P a}):
  forall l: list A, {Forall P l}+{~Forall P l}.
induction l; simpl; eauto.  
destruct (P_dec a), IHl;
eauto.
- right; intros.
  intros Hx; inversion Hx; eauto.
- right; intros.
  intros Hx; inversion Hx; eauto.
- right; intros.
  intros Hx; inversion Hx; eauto.
Defined.

(* Converts to disk address before writing to log *)
Definition write  addr_l (data_l: list value) :=
  if (Forall_dec (fun a => a < data_length) (fun a => lt_dec a data_length) addr_l) then
    if (NoDup_dec addr_l) then
      if (Nat.eq_dec (length addr_l) (length data_l)) then
        if (le_dec (length (addr_list_to_blocks (map (plus data_start) addr_l)) + length data_l) log_length) then
          
          committed <- |CDDP| commit (addr_list_to_blocks (map (plus data_start) addr_l)) data_l;
        _ <-
        if committed then
          Ret tt
        else
          _ <- |CDDP| apply_log;
        _ <- |CDCO| (Flush _ _);
        _ <- |CDDP| commit (addr_list_to_blocks (map (plus data_start) addr_l)) data_l;
        Ret tt;
        
        write_batch_to_cache (map (plus data_start) addr_l) data_l
        else
          Ret tt
      else
        Ret tt
    else
      Ret tt
  else
    Ret tt.


(* Takes a data region_address *)
Definition read a :=
  if lt_dec a data_length then
    mv <- |CDCO| Read _ (data_start + a);
  match mv with
  | Some v =>
    Ret v
  | None =>
  |CDDP| |DO| DiskLayer.Read (data_start + a)
  end
  else
    Ret value0.

Local Fixpoint write_lists_to_cache l_al_vl :=
  match l_al_vl with
  | nil =>
    Ret tt
  | al_vl :: l =>
    _ <- write_batch_to_cache (fst al_vl) (snd al_vl);
    write_lists_to_cache l
  end.

Definition recover :=
  _ <- |CDCO| (Flush _ _);
  log <- |CDDP| recover;
  write_lists_to_cache log.

(** Representation Invariants **) 
Inductive Cached_Log_Crash_State:=
| During_Commit (old_merged_disk new_merged_disk : @total_mem addr addr_dec value) : Cached_Log_Crash_State
| After_Commit (new_merged_disk : @total_mem addr addr_dec value) : Cached_Log_Crash_State
| During_Apply (merged_disk : @total_mem addr addr_dec value) : Cached_Log_Crash_State
| After_Apply (merged_disk : @total_mem addr addr_dec value) : Cached_Log_Crash_State
| During_Recovery (merged_disk : @total_mem addr addr_dec value) : Cached_Log_Crash_State.

Definition cached_log_rep merged_disk (s: Language.state CachedDiskLang) :=
  exists txns,
    fst s = Mem.list_upd_batch empty_mem (map addr_list txns) (map data_blocks txns) /\
    log_rep txns (snd s) /\
    merged_disk = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))) /\
    (forall a, a >= data_start -> snd ((snd (snd s)) a) = []).

Definition cached_log_crash_rep cached_log_crash_state (s: Language.state CachedDiskLang) :=
  match cached_log_crash_state with
  | During_Commit old_merged_disk new_merged_disk =>
    (exists txns,
       log_crash_rep (During_Commit_Log_Write txns) (snd s) /\
       old_merged_disk = total_mem_map fst (shift (plus data_start)
       (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))) /\
       (forall a, a >= data_start -> snd ((snd (snd s)) a) = [])) \/
    (exists old_txns txns,
       log_crash_rep (During_Commit_Header_Write old_txns txns) (snd s) /\

       new_merged_disk = total_mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list txns)
           (map data_blocks txns))) /\

    old_merged_disk = total_mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list old_txns)
                            (map data_blocks old_txns))) /\
    (forall a, a >= data_start -> snd ((snd (snd s)) a) = []))
      
  | After_Commit new_merged_disk =>
    exists txns,
    log_rep txns (snd s) /\
     new_merged_disk = total_mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list txns)
                            (map data_blocks txns))) /\
     (forall a, a >= data_start -> snd ((snd (snd s)) a) = [])

  | During_Apply merged_disk =>
    exists txns,
    log_crash_rep (Log.During_Apply txns) (snd s) /\
     merged_disk = total_mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list txns)
                        (map data_blocks txns)))

  | After_Apply merged_disk =>
    log_rep [] (snd s) /\
    merged_disk = total_mem_map fst (shift (plus data_start) (snd (snd s))) /\
    (forall a, a >= data_start -> snd ((snd (snd s)) a) = [])
   
  | During_Recovery merged_disk =>
    exists txns,
    log_crash_rep (Log.During_Recovery txns) (snd s) /\
    merged_disk = total_mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list txns)
                            (map data_blocks txns))) /\
    (forall a, a >= data_start -> snd ((snd (snd s)) a) = [])
    end.

Definition cached_log_reboot_rep merged_disk (s: Language.state CachedDiskLang) :=
  exists txns,
    log_reboot_rep txns (snd s) /\
    merged_disk = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))) /\
    (forall a, a >= data_start -> snd ((snd (snd s)) a) = []).


Set Nested Proofs Allowed.

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
      apply equal_f with (x0:= x2) in H0.
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
            apply equal_f with (x2:= fst x) in H.                
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

    Lemma log_rep_forall2_txns_length_match:
    forall txns s,
      log_rep txns s ->
      Forall2 (fun l_a l_v => length l_a = length l_v)
              (map addr_list txns) (map data_blocks txns).
  Proof.
    intros.
    unfold log_rep, log_rep_general, log_rep_explicit,
    log_rep_inner, txns_valid in *; cleanup.
    eapply forall_forall2.
    rewrite <- combine_map.
    apply Forall_forall; intros.
    apply in_map_iff in H; cleanup.
    simpl.
    eapply Forall_forall in H7; eauto.
    unfold txn_well_formed in *; cleanup; eauto.
    rewrite firstn_length_l; eauto.
    repeat rewrite map_length; eauto.
  Qed.



(*** SPECS ***)
Global Opaque Log.commit Log.apply_log.
Theorem write_batch_to_cache_finished:
  forall al vl o s s' t u,
    length al = length vl ->
    exec CachedDiskLang u o s (write_batch_to_cache al vl) (Finished s' t) ->
    snd s' = snd s /\
    fst s' = Mem.upd_batch (fst s) al vl.
Proof.
  induction al; simpl; intros;
  repeat invert_exec; cleanup;
  eauto; simpl in *; try lia.
  repeat invert_exec.
  edestruct IHal; eauto.
Qed.


Theorem write_batch_to_cache_crashed:
  forall al vl o s s' u,
    exec CachedDiskLang u o s (write_batch_to_cache al vl) (Crashed s') ->
    snd s' = snd s.
Proof.
  induction al; simpl; intros;
  repeat invert_exec; cleanup;
  eauto; simpl in *; try lia;
  invert_exec; eauto.
  split_ors; cleanup; repeat invert_exec; eauto.
  eapply IHal in H0; cleanup; eauto.
Qed.

Theorem write_lists_to_cache_finished:
  forall l_la_lv s o s' t u,
    Forall (fun la_lv => length (fst la_lv) = length (snd la_lv)) l_la_lv ->
    exec CachedDiskLang u o s (write_lists_to_cache l_la_lv) (Finished s' t) ->
    fst s' = Mem.list_upd_batch (fst s) (map fst l_la_lv) (map snd l_la_lv) /\
    snd s' = snd s.
Proof.
  induction l_la_lv; simpl; intros; repeat invert_exec; eauto.
  inversion H; cleanup.
  apply write_batch_to_cache_finished in H0; eauto.
  cleanup.
  apply IHl_la_lv in H1; eauto.
  cleanup; repeat cleanup_pairs; eauto.
Qed.  
  

Theorem write_lists_to_cache_crashed:
  forall l_la_lv s o s' u,
    Forall (fun la_lv => length (fst la_lv) = length (snd la_lv)) l_la_lv ->
    exec CachedDiskLang u o s (write_lists_to_cache l_la_lv) (Crashed s') ->
    snd s' = snd s.
Proof.
  induction l_la_lv; simpl; intros; repeat invert_exec; eauto.
  split_ors; cleanup; repeat invert_exec.
  apply write_batch_to_cache_crashed in H0; eauto.

  inversion H; cleanup.
  apply write_batch_to_cache_finished in H0; eauto.
  apply IHl_la_lv in H1; eauto.
  cleanup; repeat cleanup_pairs; eauto.
Qed.

Theorem read_finished:
  forall merged_disk a s o s' t u,
    cached_log_rep merged_disk s ->
    exec CachedDiskLang u o s (read a) (Finished s' t) ->
    ((exists v, 
    merged_disk a = v /\
    t = v /\
    a < data_length) \/
    (a >= data_length /\ t = value0)) /\
    s' = s.
Proof.
  unfold read; simpl; intros; repeat invert_exec; eauto.
  cleanup; repeat invert_exec; eauto.
  {
    unfold cached_log_rep in *; cleanup.
    
    eapply equal_f in H.
    rewrite H in H7.
    
    eexists.
    rewrite total_mem_map_shift_comm.
    rewrite shift_some.
    rewrite total_mem_map_fst_list_upd_batch_set.
    intuition eauto.
    {
      left; eexists; intuition eauto.
      rewrite list_upd_batch_to_upd_batch in H7.
      rewrite list_upd_batch_to_upd_batch_total.
      rewrite upd_batch_dedup_by_fst in H7.
      rewrite upd_batch_dedup_by_fst_total.
      
      symmetry; eapply upd_batch_in_some_total_mem; eauto.
      apply NoDup_map_fst_dedup_by_fst.
      all: try apply flatten_length_eq.
      all: eapply log_rep_forall2_txns_length_match; eauto.
    }
    destruct s; simpl; eauto.
  }

  {
    simpl in *.
    unfold cached_log_rep in *; cleanup.
    eapply equal_f in H.
    setoid_rewrite H7 in H.
    symmetry in H; eapply list_upd_batch_none in H.
    logic_clean.
    eexists.
    rewrite total_mem_map_shift_comm.
    rewrite shift_some.
    rewrite total_mem_map_fst_list_upd_batch_set.
    rewrite list_upd_batch_not_in; eauto.
    unfold total_mem_map; simpl.
    simpl in *; intuition eauto.
    repeat cleanup_pairs; eauto.
    {
    eapply forall_forall2.
    apply Forall_forall; intros.
    rewrite <- combine_map in H1.
    apply in_map_iff in H1; cleanup; simpl.

     unfold log_rep, log_rep_general, log_rep_explicit in *;
     simpl in *; logic_clean.
     unfold log_rep_inner, txns_valid in *; logic_clean.
     
     eapply Forall_forall in H12; eauto.
     unfold txn_well_formed in H12; logic_clean.
     rewrite H15 in *.
     apply firstn_length_l; eauto; lia.
     repeat rewrite map_length; eauto.
    }
  }
  intuition eauto.
  right; split; eauto; lia.
Qed.

Theorem read_crashed:
  forall a s o s' u,
    exec CachedDiskLang u o s (read a) (Crashed s') ->
    s' = s.
Proof.
  unfold read; simpl; intros; cleanup; repeat invert_exec; eauto.
  split_ors; cleanup; repeat invert_exec.
  destruct s; eauto.
  cleanup; repeat invert_exec;
  repeat cleanup_pairs; eauto.
  destruct s1; eauto.
Qed.


Lemma recover_finished:  
  forall merged_disk s o s' t u,
  cached_log_reboot_rep merged_disk s ->
  exec CachedDiskLang u o s recover (Finished s' t) ->
  cached_log_rep merged_disk s'.
Proof.
  unfold recover, cached_log_reboot_rep; intros; cleanup.
  repeat invert_exec.
  eapply recover_finished in H6; eauto.
  apply write_lists_to_cache_finished in H4.
  repeat cleanup_pairs.
  unfold cached_log_rep; simpl; eexists; intuition eauto.
  rewrite map_fst_combine, map_snd_combine by (repeat rewrite map_length; eauto); eauto.
  assert (A: map addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x))). {
    repeat rewrite map_map.
    apply map_ext_in.
    intros.
    rewrite map_map.
    rewrite map_noop; eauto.
    intros.
    unfold log_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H12; eauto.
    unfold txn_well_formed in H12; simpl in *; cleanup.
    eapply Forall_forall in H16; eauto; lia.
  }
  rewrite A at 2.
  rewrite shift_list_upd_batch_set_comm.
  rewrite shift_eq_after with (m1:=s2)(m2:=sync s3).
  rewrite <- shift_list_upd_batch_set_comm.
  rewrite <- A.

  repeat (rewrite total_mem_map_shift_comm, total_mem_map_fst_list_upd_batch_set);
  rewrite total_mem_map_fst_sync_noop; eauto.
  {
    unfold sumbool_agree; intros; intuition eauto.
    destruct (addr_dec x0 y); subst.
    destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
    destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
  }
  {
    intros; lia.
  }
  {
    intros; apply H8; lia.
  }
  {
    unfold sumbool_agree; intros; intuition eauto.
    destruct (addr_dec x0 y); subst.
    destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
    destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
  }
  {
    rewrite H8; simpl; eauto.
  }
  {
    cleanup.
    rewrite Forall_forall; intros.
    rewrite <- combine_map in H1.
    apply in_map_iff in H1; cleanup; simpl.
    unfold log_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H15; eauto.
    unfold txn_well_formed in H15; simpl in *; cleanup.
    apply firstn_length_l; eauto.
  }
Qed.

Lemma recover_crashed:  
  forall merged_disk s o s' u,
  cached_log_reboot_rep merged_disk s ->
  exec CachedDiskLang u o s recover (Crashed s') ->
  (cached_log_reboot_rep merged_disk s' \/
  cached_log_crash_rep (During_Recovery merged_disk) s' \/
  cached_log_crash_rep (After_Commit merged_disk) s') /\
  ((forall a, a >= data_start -> snd (snd s') a = snd (snd s) a) \/
     (forall a, a >= data_start -> snd (snd s') a = sync (snd (snd s)) a)) .
Proof.
  unfold recover, cached_log_reboot_rep; intros; cleanup.
  repeat invert_exec.
  split_ors; cleanup; repeat invert_exec.
  repeat cleanup_pairs; eauto.
  intuition eauto.
  split_ors; cleanup; repeat invert_exec.
  {
    eapply recover_crashed in H5; eauto.
    repeat cleanup_pairs.
    split_ors; cleanup.
    {
      intuition eauto.
      left; eexists; intuition eauto.
      assert (A: map addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x))). {
    repeat rewrite map_map.
    apply map_ext_in.
    intros.
    rewrite map_map.
    rewrite map_noop; eauto.
    intros.
    unfold log_reboot_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H22; eauto.
    unfold txn_well_formed in H22; simpl in *; cleanup_no_match.
    eapply Forall_forall in H25; eauto; lia.
      }
      rewrite A at 2.
      rewrite shift_list_upd_batch_set_comm.
      rewrite shift_eq_after with (m1:=s2)(m2:=s3).
      rewrite <- shift_list_upd_batch_set_comm.
      rewrite <- A; eauto.
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x0 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
      }
      {
        intros; lia.
      }
      {
        intros; apply H1; lia.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x0 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
      }
      {
        rewrite H1; eauto.
      }
    }
    split_ors; cleanup.
    {
      intuition eauto.
      right; left; eexists; intuition eauto.
      assert (A: map addr_list x =
                 map (map (Init.Nat.add data_start))
                     (map (map (fun a => a - data_start)) (map addr_list x))). {
        repeat rewrite map_map.
        apply map_ext_in.
        intros.
        rewrite map_map.
        rewrite map_noop; eauto.
        intros.
        unfold log_reboot_rep, log_rep_general, log_rep_explicit,
        log_rep_inner, txns_valid in *; simpl in *; cleanup.
        eapply Forall_forall in H13; eauto.
        unfold txn_well_formed in H13; simpl in *; cleanup_no_match.
        eapply Forall_forall in H17; eauto; lia.
      }
      rewrite A at 2.
      rewrite shift_list_upd_batch_set_comm.
      rewrite shift_eq_after with (m1:=s2)(m2:=s3).
      rewrite <- shift_list_upd_batch_set_comm.
      rewrite <- A; eauto.
      
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x0 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
      }
      {
        intros; lia.
      }
      {
        intros; apply H1; lia.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x0 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
      }
      {
        rewrite H1; eauto.
      }
    }
    intuition eauto.
    left; eexists; intuition eauto.
    {
      unfold log_rep, log_rep_general, log_reboot_rep in *.
      cleanup.
      do 4 eexists; intuition eauto; congruence.
    }
    assert (A: map addr_list x =
               map (map (Init.Nat.add data_start))
                   (map (map (fun a => a - data_start)) (map addr_list x))). {
      repeat rewrite map_map.
      apply map_ext_in.
      intros.
      rewrite map_map.
      rewrite map_noop; eauto.
      intros.
      unfold log_rep, log_rep_general, log_rep_explicit,
      log_rep_inner, txns_valid in *; simpl in *; cleanup.
      eapply Forall_forall in H12; eauto.
      unfold txn_well_formed in H12; simpl in *; cleanup_no_match.
      eapply Forall_forall in H16; eauto; lia.
    }
    
    rewrite A at 2.
    rewrite shift_list_upd_batch_set_comm.
    rewrite shift_eq_after with (m1:=s2)(m2:=sync s3).
    rewrite <- shift_list_upd_batch_set_comm.
    rewrite <- A; eauto.
    repeat rewrite total_mem_map_shift_comm.
    repeat rewrite total_mem_map_fst_list_upd_batch_set.
    rewrite total_mem_map_fst_sync_noop; eauto.
    
    {
      unfold sumbool_agree; intros; intuition eauto.
      destruct (addr_dec x0 y); subst.
      destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
      destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
    }
    {
      intros; lia.
    }
    {
      intros; apply H1; lia.
    }
    {
      unfold sumbool_agree; intros; intuition eauto.
      destruct (addr_dec x0 y); subst.
      destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
      destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
    }
    {
      rewrite H1; simpl; eauto.
    }
  }
  {
    eapply Log.Specs.recover_finished in H6; eauto; cleanup.
    apply write_lists_to_cache_crashed in H4; cleanup.
    repeat cleanup_pairs.
    {
      intuition eauto.
      right; right; eexists; intuition eauto.
    {
      unfold log_rep, log_rep_general, log_reboot_rep in *.
      cleanup.
      assert (A: map addr_list x =
                 map (map (Init.Nat.add data_start))
                     (map (map (fun a => a - data_start)) (map addr_list x))). {
        repeat rewrite map_map.
        apply map_ext_in.
        intros.
        rewrite map_map.
        rewrite map_noop; eauto.
        intros.
        unfold log_rep, log_rep_general, log_rep_explicit,
        log_rep_inner, txns_valid in *; simpl in *; cleanup_no_match.
        eapply Forall_forall in H13; eauto.
        unfold txn_well_formed in H13; simpl in *; cleanup_no_match.
        eapply Forall_forall in H24; eauto; lia.
      }
    
      rewrite A at 2.
      rewrite shift_list_upd_batch_set_comm.
      rewrite shift_eq_after with (m1:=s3)(m2:=sync s4).
      rewrite <- shift_list_upd_batch_set_comm.
      rewrite <- A; eauto.
      repeat rewrite total_mem_map_shift_comm.
      repeat rewrite total_mem_map_fst_list_upd_batch_set.
      rewrite total_mem_map_fst_sync_noop; eauto.
      
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x9 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x9) (data_start + y)); eauto; lia.
      }
      {
        intros; lia.
      }
      {
        intros; apply H8; lia.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x9 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x9) (data_start + y)); eauto; lia.
      }
    }
    {
      rewrite H8; simpl; eauto.
    }
    }
    {
      apply Forall_forall; intros.
      rewrite <- combine_map in H1.
      apply in_map_iff in H1; cleanup; simpl.
      unfold log_reboot_rep, log_rep_explicit, log_rep_inner, txns_valid in H;
      simpl in *; logic_clean.
      eapply Forall_forall in H16; eauto.
      unfold txn_well_formed in H16; logic_clean.
      rewrite H19.
      apply firstn_length_l; eauto.
      lia.
    }
  }
Qed.

  
Theorem write_finished:
  forall merged_disk s o al vl s' t u,
  cached_log_rep merged_disk s ->
  exec CachedDiskLang u o s (write al vl) (Finished s' t) ->
  (cached_log_rep merged_disk s' /\
   (~Forall (fun a => a < data_length) al \/
    ~NoDup al \/
    length al <> length vl \/
    length (addr_list_to_blocks (map (plus data_start) al)) + length vl > log_length )) \/
  (cached_log_rep (upd_batch merged_disk al vl) s' /\
   Forall (fun a => a < data_length) al /\
   NoDup al /\
   length al = length vl /\
   length (addr_list_to_blocks (map (plus data_start) al)) + length vl <= log_length).
Proof.
  unfold write; simpl; intros.
  cleanup; simpl in *; invert_exec_no_match; simpl in *; cleanup_no_match; simpl in *; eauto.
  invert_exec.
  unfold cached_log_rep in *; logic_clean.
  destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
  unfold log_rep in *; logic_clean.
  eapply commit_finished in H3; eauto.
  all: try rewrite H6.
  split_ors; cleanup_no_match.
  {(** initial commit is success **)
    right.
    repeat invert_exec.
    apply write_batch_to_cache_finished in H1; eauto; cleanup.
    repeat cleanup_pairs.
    split; eauto.
    exists (x4++[x7]).
    simpl.
    repeat rewrite map_app; simpl.
    
    unfold log_rep, log_rep_general, log_rep_explicit,
    log_rep_inner, txns_valid in *; cleanup; simpl in *.
    eapply_fresh forall_app_l in H12. 
    inversion Hx; simpl in *; cleanup.
    unfold txn_well_formed in H21; cleanup.
    rewrite firstn_app2; eauto.
    simpl; intuition eauto.
    {
      rewrite Mem.list_upd_batch_app; eauto.
      repeat rewrite map_length; eauto.
    }
    {
      do 3 eexists; intuition eauto.
    }
    {
      assert (A: map addr_list x4 ++ [map (Init.Nat.add data_start) al] =
                 map (map (Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x4) ++ [al])). {
        repeat rewrite map_map; simpl.
        rewrite map_app; simpl.
        repeat rewrite map_map.
        setoid_rewrite map_ext_in at 3.
        eauto.
        intros.
        rewrite map_map.        
        setoid_rewrite map_ext_in.
        apply map_id.
        intros; simpl.
        eapply Forall_forall in H12; eauto.
        unfold txn_well_formed in H12; logic_clean.
        eapply Forall_forall in H35; eauto; lia.
        
      }
      setoid_rewrite A.
      rewrite shift_list_upd_batch_set_comm; eauto.
      setoid_rewrite shift_eq_after with (m1:= s0) (m2:= sync s3); intros; try lia.
      rewrite <- shift_list_upd_batch_set_comm; eauto.      
      rewrite <- A.

      repeat rewrite total_mem_map_shift_comm.
      repeat rewrite total_mem_map_fst_list_upd_batch_set.
      rewrite total_mem_map_fst_sync_noop.
      rewrite list_upd_batch_app; simpl.
      rewrite shift_upd_batch_comm; eauto.
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x) (data_start + y)); eauto; lia.
      }
      {
        repeat rewrite map_length; eauto.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x) (data_start + y)); eauto; lia.
      }
      {
        apply H11; lia.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x) (data_start + y)); eauto; lia.
      }
    }
    {
      rewrite H11; simpl; eauto.
    }
    rewrite map_length; eauto.
    rewrite map_length; eauto.
  }
  {(** First commit failed. Time to apply the log **)
    repeat invert_exec.
    simpl in *.
    repeat cleanup_pairs; simpl in *.
    eapply apply_log_finished in H10; eauto.
    logic_clean.
    apply write_batch_to_cache_finished in H1.
    logic_clean.
    unfold log_rep in *; logic_clean.
    eapply commit_finished in H11; eauto.
    all: try rewrite H7.
    split_ors; cleanup_no_match.
    {(** second commit is success **)
    right.
    repeat cleanup_pairs.
    split; eauto.
    exists ([x1]).
    simpl.
    
    unfold log_rep, log_rep_general, log_rep_explicit,
    log_rep_inner, txns_valid in *; cleanup; simpl in *. 
    inversion H15; simpl in *; cleanup.
    unfold txn_well_formed in H2; cleanup.
    rewrite firstn_app2; eauto.
    unfold log_header_block_rep in *; simpl in *; cleanup.
    simpl; intuition eauto.
    {
      do 3 eexists; intuition eauto.
    }
    {
      rewrite shift_upd_batch_set_comm.
      setoid_rewrite shift_eq_after with (m1:= s1) (m2:= sync
          (sync
             (upd_set (list_upd_batch_set s4 (map addr_list x4) (map data_blocks x4)) hdr_block_num
                      (encode_header (update_hdr (decode_header (fst (s4 hdr_block_num))) header_part0))))); intros; try lia.
      rewrite sync_idempotent.
      rewrite total_mem_map_fst_upd_batch_set.
      repeat rewrite total_mem_map_shift_comm.
      rewrite total_mem_map_fst_sync_noop.
      rewrite total_mem_map_fst_upd_set.
      repeat rewrite total_mem_map_fst_list_upd_batch_set.
      rewrite shift_upd_noop; eauto.

      {
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.
      }
      {
        eapply H13; lia.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x0 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
      }
    }
    {
      rewrite H13; simpl; eauto.
    }
    rewrite map_length; eauto.
    }
    {
      rewrite app_length in H11.
      repeat cleanup_pairs.
      unfold log_rep, log_rep_general, log_rep_explicit,
      log_rep_inner, header_part_is_valid, txns_valid in *;
      simpl in *; cleanup; simpl in *. 
          
      rewrite <- H12 in *; simpl in *.
      lia.
    }
    {
      rewrite firstn_app2; eauto.
      apply FinFun.Injective_map_NoDup; eauto.
      unfold FinFun.Injective; intros; lia.
      rewrite map_length; eauto.
    }
    {
      rewrite firstn_app2; eauto.    
      apply Forall_forall; intros.
      apply in_map_iff in H8; cleanup.
      eapply_fresh Forall_forall in f; eauto.
      pose proof data_fits_in_disk.
      split; try lia.
      rewrite map_length; eauto.
    }    
    {
      rewrite app_length, map_length; lia.
    }
    {
      rewrite map_length; eauto.
    }
  } 
  {
    rewrite H7.
    rewrite firstn_app2; eauto.
    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    rewrite map_length; eauto.
  }
  {
    rewrite H7.
    rewrite firstn_app2; eauto.    
    apply Forall_forall; intros.
    apply in_map_iff in H8; cleanup_no_match.
    eapply_fresh Forall_forall in f; eauto.
    pose proof data_fits_in_disk.
    split; try lia.
    rewrite map_length; eauto.
  }
  {
    rewrite H7.
    rewrite app_length, map_length; lia.
  }
  {
    left; intuition eauto; lia.
  }
  {
    left; intuition eauto; lia.
  }
Qed.


Theorem write_crashed:
  forall merged_disk s o al vl s' u,
  cached_log_rep merged_disk s ->
  exec CachedDiskLang u o s (write al vl) (Crashed s') ->
  cached_log_rep merged_disk s' \/
  ((cached_log_crash_rep (During_Commit merged_disk (upd_batch merged_disk al vl)) s' \/
  cached_log_crash_rep (After_Commit (upd_batch merged_disk al vl)) s' \/
  cached_log_crash_rep (During_Apply merged_disk) s' \/
  cached_log_crash_rep (After_Apply merged_disk) s') /\
   Forall (fun a => a < data_length) al /\
   NoDup al /\
   length al = length vl /\
   length (addr_list_to_blocks (map (plus data_start) al)) + length vl <= log_length).
Proof.
  unfold cached_log_rep, write; simpl; intros.
  cleanup; invert_exec.
  {
    split_ors; cleanup; repeat invert_exec.
    {
      destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
      eapply commit_crashed in H4; eauto.
      {
        repeat (split_ors; cleanup);
        repeat cleanup_pairs; eauto.
        {
          left; eexists; intuition eauto.
        }
        {
          right; repeat (split; eauto).
          left; unfold cached_log_crash_rep; simpl.
          left; eexists; intuition eauto.
          
          assert (A: map addr_list x =
                     map (map (Init.Nat.add data_start))
                         (map (map (fun a => a - data_start)) (map addr_list x))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H14; eauto.
            unfold txn_well_formed, record_is_valid in H14; logic_clean.
            eapply Forall_forall in H19; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s3) with (shift (Init.Nat.add data_start) s2); eauto.
          {
            apply shift_eq_after.
            intros; lia.
            intros; apply H4; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x0 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x0 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
          }
          {
            rewrite H4; eauto.
          }
        }
        {
          right; intuition eauto.
          left; unfold cached_log_crash_rep; simpl.
          right; do 2 eexists; intuition eauto.
          {
            
            assert (A: map addr_list (x++[x0]) =
                       map (map (Init.Nat.add data_start))
                           (map (map (fun a => a - data_start))
                                (map addr_list (x++[x0])))). {
              repeat rewrite map_map; simpl.
              setoid_rewrite map_ext_in at 2.
              eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H20; eauto.
            unfold txn_well_formed, record_is_valid in H20; logic_clean.
            eapply Forall_forall in H25; eauto; lia.
          }
          assert (A0: map addr_list x =
                      map (map (Init.Nat.add data_start))
                          (map (map (fun a => a - data_start))
                               (map addr_list x))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H20; eauto.
            unfold txn_well_formed, record_is_valid in H20; logic_clean.
            eapply Forall_forall in H25; eauto; lia.
          }
          rewrite A, A0.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s3) with (shift (Init.Nat.add data_start) s2); eauto.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          rewrite total_mem_map_fst_upd_batch_set.
          unfold log_crash_rep in *; simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in H13; logic_clean.
          eapply forall_app_l in H16.
          simpl in *.
          inversion H16; subst.
          unfold txn_well_formed in H19; logic_clean.
          rewrite H21, H0, H5 in *.
          rewrite firstn_app2.
          replace (map (fun a : nat => a - data_start) (map (Init.Nat.add data_start) al)) with al; eauto.

          {
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            rewrite map_id; eauto.
            intros; simpl.
            lia.
          }
          rewrite map_length; eauto.
          repeat rewrite map_length; eauto.
          
          apply shift_eq_after.
          intros; lia.
          intros; apply H7; lia.
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          }
          {
           
           assert (A0: map addr_list x =
                       map (map (Init.Nat.add data_start))
                           (map (map (fun a => a - data_start))
                                (map addr_list x))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H20; eauto.
            unfold txn_well_formed, record_is_valid in H20; logic_clean.
            eapply Forall_forall in H25; eauto; lia.
          }
          rewrite A0.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s3) with (shift (Init.Nat.add data_start) s2); eauto.
          
          repeat rewrite map_app.

          apply shift_eq_after.
          intros; lia.
          intros; apply H7; lia.
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          }
          {
            rewrite H7; eauto.
          }
        }

        {
          right; intuition eauto.
          right; left; unfold cached_log_crash_rep; simpl.
          eexists; intuition eauto.
          
          assert (A: map addr_list (x++[x0]) =
                     map (map (Init.Nat.add data_start))
                         (map (map (fun a => a - data_start))
                              (map addr_list (x++[x0])))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_rep, log_rep_general, log_rep_explicit,
            log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H14; eauto.
            unfold txn_well_formed, record_is_valid in H14; logic_clean.
            eapply Forall_forall in H25; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s2) with (shift (Init.Nat.add data_start) (sync s3)); eauto.

          rewrite <- shift_list_upd_batch_set_comm, <- A.
          rewrite <- total_mem_map_fst_upd_batch_set.
          rewrite <- shift_upd_batch_set_comm.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_upd_batch_set.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          rewrite total_mem_map_fst_sync_noop; eauto.
          
          unfold log_rep, log_rep_general, log_rep_explicit in *;
          simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in *; logic_clean.
          eapply forall_app_l in H18.
          simpl in *.
          inversion H18; subst.
          unfold txn_well_formed in H23; logic_clean.
          rewrite H22, H0, H5 in *.
          rewrite firstn_app2; eauto.
          rewrite map_length; eauto.
          repeat rewrite map_length; eauto.
          
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }          
          {
            apply shift_eq_after.
            intros; lia.
            intros; rewrite H7; eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          {
            rewrite H7; simpl; eauto.
          }
        }
      }
      all: try rewrite H5, firstn_app2.
      all: try rewrite app_length;
      try rewrite map_length; try lia.
      {
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
      }
      {
        apply Forall_forall; intros.
        apply in_map_iff in H6; cleanup_no_match.
        eapply_fresh Forall_forall in f; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
      }
      {
        rewrite H5, app_length, map_length; lia.
      }
    }
    {
      unfold log_rep in *; logic_clean.
      destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
      eapply commit_finished in H5; eauto.
      split_ors; cleanup; try congruence.
      {
        split_ors; cleanup; repeat invert_exec;
        repeat cleanup_pairs.
        {
          right; intuition eauto;
          right; left; unfold cached_log_crash_rep; simpl.
          eexists; intuition eauto.
          
          assert (A: map addr_list (x++[x3]) =
                     map (map (Init.Nat.add data_start))
                         (map (map (fun a => a - data_start))
                              (map addr_list (x++[x3])))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_rep, log_rep_general, log_rep_explicit,
            log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H14; eauto.
            unfold txn_well_formed, record_is_valid in H14; logic_clean.
            eapply Forall_forall in H25; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s2) with (shift (Init.Nat.add data_start) (sync s3)); eauto.

          rewrite <- shift_list_upd_batch_set_comm, <- A.
          rewrite <- total_mem_map_fst_upd_batch_set.
          rewrite <- shift_upd_batch_set_comm.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_upd_batch_set.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          rewrite total_mem_map_fst_sync_noop; eauto.
          
          unfold log_rep, log_rep_general, log_rep_explicit in *;
          simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in *; logic_clean.
          eapply forall_app_l in H18.
          simpl in *.
          inversion H18; subst.
          unfold txn_well_formed in H23; logic_clean.
          rewrite H22, H5, H1 in *.
          rewrite firstn_app2; eauto.
          rewrite map_length; eauto.
          repeat rewrite map_length; eauto.
          
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }          
          {
            apply shift_eq_after.
            intros; lia.
            intros; rewrite H9; eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }
          {
            rewrite H9; simpl; eauto.
          }
        }
        {
          eapply write_batch_to_cache_crashed in H6.
          simpl in *; cleanup.
          right; intuition eauto.
          right; left; unfold cached_log_crash_rep; simpl.
          eexists; intuition eauto.
          
          assert (A: map addr_list (x++[x3]) =
                     map (map (Init.Nat.add data_start))
                         (map (map (fun a => a - data_start))
                              (map addr_list (x++[x3])))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_rep, log_rep_general, log_rep_explicit,
            log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H15; eauto.
            unfold txn_well_formed, record_is_valid in H15; logic_clean.
            eapply Forall_forall in H26; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s2) with (shift (Init.Nat.add data_start) (sync s3)); eauto.

          rewrite <- shift_list_upd_batch_set_comm, <- A.
          rewrite <- total_mem_map_fst_upd_batch_set.
          rewrite <- shift_upd_batch_set_comm.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_upd_batch_set.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          rewrite total_mem_map_fst_sync_noop; eauto.
          
          unfold log_rep, log_rep_general, log_rep_explicit in *;
          simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in *; logic_clean.
          eapply forall_app_l in H19.
          simpl in *.
          inversion H19; subst.
          unfold txn_well_formed in H24; logic_clean.
          rewrite H23, H5, H1 in *.
          rewrite firstn_app2; eauto.
          rewrite map_length; eauto.
          repeat rewrite map_length; eauto.
          
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }          
          {
            apply shift_eq_after.
            intros; lia.
            intros; rewrite H9; eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }
          {
            rewrite H9; simpl; eauto.
          }
        }
      }
      all: try rewrite H1, firstn_app2.
      all: try rewrite app_length;
      try rewrite map_length; try lia.
      {
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
      }
      {
        apply Forall_forall; intros.
        apply in_map_iff in H2; cleanup_no_match.
        eapply_fresh Forall_forall in f; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
      }
      {
        rewrite H1, app_length, map_length; lia.
      }
    }
    {
      unfold log_rep in *; logic_clean.
      eapply commit_finished in H5; eauto.
      {
        split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        split_ors; cleanup; repeat invert_exec.
        {
          split_ors; cleanup; repeat invert_exec.
          {(** Apply log crahed **)
            simpl in *;
            eapply apply_log_crashed in H2; eauto.
            cleanup; split_ors; cleanup; repeat cleanup_pairs.
             {
               left; unfold cached_log_rep; simpl.
               eexists; intuition eauto.
             }
             {               
               split_ors; cleanup.
               {
                 left. unfold cached_log_rep; simpl.
                 eexists; intuition eauto.
                 repeat rewrite total_mem_map_shift_comm.
                 repeat rewrite total_mem_map_fst_list_upd_batch_set.
                 rewrite total_mem_map_fst_upd_batch_set.
                 rewrite total_mem_map_fst_list_upd_batch_set.
                 rewrite upd_batch_to_list_upd_batch_singleton.
                 setoid_rewrite <- list_upd_batch_app at 2.
                 unfold log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
                 rewrite <- H10.
                 erewrite RepImplications.bimap_get_addr_list.
                 4: eauto.
                 rewrite list_upd_batch_firstn_noop; eauto.                 
                 eapply log_rep_forall2_txns_length_match; eauto.
                 eauto.
                 rewrite map_length; eauto.
                 unfold log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
                 rewrite <- H10.                 
                 erewrite RepImplications.bimap_get_addr_list.
                 repeat rewrite firstn_length, map_length; eauto.
                 3: eauto.
                 eauto.
                 rewrite map_length; eauto.
                 (** Apply log crash being synced  not true *)
                 admit.
               }
               split_ors; cleanup.
               {
                 left; unfold cached_log_rep; simpl.
                 eexists; intuition eauto.
                 repeat rewrite total_mem_map_shift_comm.
                 repeat rewrite total_mem_map_fst_list_upd_batch_set.
                 rewrite total_mem_map_fst_sync_noop.
                 rewrite total_mem_map_fst_list_upd_batch_set.
                 unfold log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
                 rewrite <- H10.
                 erewrite RepImplications.bimap_get_addr_list.
                 4: eauto.
                 rewrite TotalMem.list_upd_batch_noop; eauto.
                 eapply log_rep_forall2_txns_length_match; eauto.
                 eapply log_rep_forall2_txns_length_match; eauto.
                 eauto.
                 rewrite map_length; eauto.
               }
               {
                 simpl in *.
                 cleanup; simpl in *.
                 right; intuition eauto.
                 right; right; left; unfold cached_log_rep; simpl in *.
                 eexists; intuition eauto.
                 
                 repeat rewrite total_mem_map_shift_comm.
                 repeat rewrite total_mem_map_fst_list_upd_batch_set.
                 rewrite total_mem_map_fst_upd_set.
                 rewrite total_mem_map_fst_sync_noop.
                 rewrite total_mem_map_fst_list_upd_batch_set.
                 setoid_rewrite <- shift_upd_noop at 6.
                 rewrite upd_list_upd_batch_upd_noop.
                 setoid_rewrite shift_upd_noop.
                 unfold log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; logic_clean.
                 rewrite <- H10.
                 erewrite RepImplications.bimap_get_addr_list.
                 4: eauto.
                 rewrite TotalMem.list_upd_batch_noop; eauto.
                 {
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H12.
                   apply in_map_iff in H12; cleanup.
                   simpl.
                   eapply Forall_forall in H11; eauto.
                   unfold txn_well_formed in H11; logic_clean.
                   rewrite H14.
                   apply firstn_length_l; eauto.
                   lia.
                   repeat rewrite map_length; eauto.
                 }
                 {
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H12.
                   apply in_map_iff in H12; cleanup.
                   simpl.
                   eapply Forall_forall in H11; eauto.
                   unfold txn_well_formed in H11; logic_clean.
                   rewrite H14.
                   apply firstn_length_l; eauto.
                   lia.
                   repeat rewrite map_length; eauto.
                 }
                 eauto.
                 rewrite map_length; eauto.
                 {
                   intros; pose proof hdr_before_log.
                   pose proof data_start_where_log_ends.
                   lia.
                 }
                 {                   
                   unfold log_rep_general, log_rep_explicit,
                   log_rep_inner, txns_valid in *; logic_clean.
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H12.
                   apply in_map_iff in H12; cleanup.
                   simpl.
                   eapply Forall_forall in H11; eauto.
                   unfold txn_well_formed in H11; logic_clean.
                   rewrite H14.
                   apply firstn_length_l; eauto.
                   lia.
                   repeat rewrite map_length; eauto.
                 }
                 {
                   intros; pose proof hdr_before_log.
                   pose proof data_start_where_log_ends.
                   lia.
                 }
               }
             }
          }
          eapply apply_log_finished in H4; eauto.
          simpl in *; cleanup.
          repeat cleanup_pairs.
          split_ors; cleanup.
          {(** Flush Crashed **)
            repeat invert_exec.            
             {
               right; intuition eauto.
               right; right; right; unfold cached_log_rep; simpl.
               intuition eauto.
               rewrite <- sync_shift_comm.
               rewrite shift_upd_set_noop.
               rewrite total_mem_map_fst_sync_noop; eauto.
               {
                 intros; pose proof hdr_before_log.
                 pose proof data_start_where_log_ends.
                 lia.
               }
             }
          }
          repeat invert_exec.
          split_ors; cleanup; repeat invert_exec.
          { (** Second commit crashed **)
            simpl in *.
            destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
            eapply commit_crashed in H6; eauto.
            split_ors; cleanup; 
            simpl in *; repeat cleanup_pairs.
            {
              left.
              eexists; intuition eauto.
              simpl; eauto.
              simpl.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite total_mem_map_fst_sync_noop; eauto.
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
            }
            split_ors; cleanup; 
            simpl in *; repeat cleanup_pairs.
            {
              right; intuition eauto.
              left; left; eexists; intuition eauto.
              simpl.
              rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
                  (encode_header (update_hdr x0 header_part0)))).
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              repeat rewrite total_mem_map_fst_sync_noop; eauto.
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H2; lia.
              rewrite H2; simpl; eauto.
            }
            split_ors; cleanup; 
            simpl in *; repeat cleanup_pairs.
            {
              right; intuition eauto.
              left; right; do 2 eexists; intuition eauto.
              simpl.
              replace (addr_list x1) with (map (Init.Nat.add data_start) al).           
              rewrite shift_upd_batch_set_comm.
              rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
            (encode_header (update_hdr x0 header_part0)))).
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite total_mem_map_fst_upd_batch_set.
              repeat rewrite total_mem_map_fst_sync_noop; eauto.              
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H8; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x3 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x3) (data_start + y)); eauto; lia.
              }
              {
                unfold log_crash_rep in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H16; cleanup.
                inversion H19; cleanup.
                unfold txn_well_formed in H22; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
              }
              {
                simpl.
                rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
            (encode_header (update_hdr x0 header_part0)))).
                rewrite <- sync_shift_comm.
                rewrite shift_upd_set_noop.
                repeat rewrite total_mem_map_fst_sync_noop; eauto.
                {
                  intros; pose proof hdr_before_log.
                  pose proof data_start_where_log_ends.
                  lia.
                }
                intros; lia.
                intros; apply H8; lia.
              }
              rewrite H8; simpl; eauto.
             }
            {
              right; intuition eauto.
              right; left; eexists; intuition eauto.
              simpl.
              replace (addr_list x1) with (map (Init.Nat.add data_start) al).
              rewrite shift_upd_batch_set_comm.
              rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (sync
            (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
                     (encode_header (update_hdr x0 header_part0))))).
              rewrite sync_idempotent.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite total_mem_map_fst_upd_batch_set.
              repeat rewrite total_mem_map_fst_sync_noop; eauto.              
              
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H8; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x3 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x3) (data_start + y)); eauto; lia.
              }
              {
                unfold log_rep, log_rep_general, log_rep_explicit in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H13; cleanup.
                inversion H4; cleanup.
                unfold txn_well_formed in H27; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
              }
              rewrite H8; simpl; eauto.
            }
            all: try rewrite H7, firstn_app2.
            all: try rewrite app_length;
            try rewrite map_length; try lia.
            {
              apply FinFun.Injective_map_NoDup; eauto.
              unfold FinFun.Injective; intros; lia.
            }
            {
              apply Forall_forall; intros.
              apply in_map_iff in H8; cleanup_no_match.
              eapply_fresh Forall_forall in f; eauto.
              pose proof data_fits_in_disk.
              split; try lia.
            }
            {
              rewrite H7, app_length, map_length; lia.
            }
          }
          unfold log_rep in *; logic_clean.
          destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
          eapply commit_finished in H6; eauto.
          simpl in *; repeat cleanup_pairs; simpl in *.
          split_ors; cleanup; try congruence; try lia.
          2: {
            unfold log_rep_general, log_rep_explicit, log_header_block_rep in *; simpl in *; logic_clean.
            unfold sync, upd_set in H2.
            destruct (addr_dec hdr_block_num hdr_block_num); try lia.
            destruct (list_upd_batch_set s1 (map addr_list x) (map data_blocks x) hdr_block_num); simpl in *;
            destruct x1; simpl in *; cleanup;
            rewrite encode_decode_header, app_length in H6; simpl in *;
            lia.
          }
          {
            right; intuition eauto.
            right; left; unfold cached_log_crash_rep; simpl.
            eexists; intuition eauto.
            simpl.
            replace (addr_list x1) with (map (Init.Nat.add data_start) al).
            rewrite shift_upd_batch_set_comm.
            rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (sync
            (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
                     (encode_header (update_hdr x0 header_part0))))).
              rewrite sync_idempotent.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite total_mem_map_fst_upd_batch_set.
              repeat rewrite total_mem_map_fst_sync_noop; eauto.              
              
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H9; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x2 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
              }
              {
                unfold log_rep, log_rep_general, log_rep_explicit in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H13; cleanup.
                inversion H4; cleanup.
                unfold txn_well_formed in H27; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
              }
              rewrite H9; simpl; eauto.
            }
            all: try rewrite H7, firstn_app2.
            all: try rewrite app_length;
            try rewrite map_length; try lia.
            {
              apply FinFun.Injective_map_NoDup; eauto.
              unfold FinFun.Injective; intros; lia.
            }
            {
              apply Forall_forall; intros.
              apply in_map_iff in H8; cleanup_no_match.
              eapply_fresh Forall_forall in f; eauto.
              pose proof data_fits_in_disk.
              split; try lia.
            }
            {
              rewrite H7, app_length, map_length; lia.
            }
        }
        {(** write_batch_to_cache_crashed **)
          eapply apply_log_finished in H6; eauto.
          simpl in *; cleanup.
          unfold log_rep in *; logic_clean.
          destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
          simpl in *; repeat cleanup_pairs; simpl in *.
          eapply commit_finished in H7; eauto.
          simpl in *; repeat cleanup_pairs; simpl in *.
          split_ors; cleanup; try congruence; try lia.
          2: {
            unfold log_rep_general, log_rep_explicit, log_header_block_rep in *; simpl in *; logic_clean.
            unfold sync, upd_set in H2.
            destruct (addr_dec hdr_block_num hdr_block_num); try lia.
            destruct (list_upd_batch_set s1 (map addr_list x) (map data_blocks x) hdr_block_num); simpl in *;
            destruct x1; simpl in *; cleanup;
            rewrite encode_decode_header, app_length in H6; simpl in *;
            lia.
          }
          eapply write_batch_to_cache_crashed in H1; eauto.
          simpl in *; cleanup.
          repeat cleanup_pairs; simpl in *.
          {
            right; intuition eauto; right; left; unfold cached_log_crash_rep; simpl.
            eexists; intuition eauto.
            simpl.
            replace (addr_list x1) with (map (Init.Nat.add data_start) al).
            rewrite shift_upd_batch_set_comm.
            rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (sync
            (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
                     (encode_header (update_hdr x0 header_part0))))).
              rewrite sync_idempotent.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite total_mem_map_fst_upd_batch_set.
              repeat rewrite total_mem_map_fst_sync_noop; eauto.              
              
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H10; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x5 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x5) (data_start + y)); eauto; lia.
              }
              {
                unfold log_rep, log_rep_general, log_rep_explicit in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H13; cleanup.
                inversion H1; cleanup.
                unfold txn_well_formed in H27; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
              }
              rewrite H10; simpl; eauto.
            }
            all: try rewrite H9, firstn_app2.
            all: try rewrite app_length;
            try rewrite map_length; try lia.
            {
              apply FinFun.Injective_map_NoDup; eauto.
              unfold FinFun.Injective; intros; lia.
            }
            {
              apply Forall_forall; intros.
              apply in_map_iff in H2; cleanup_no_match.
              eapply_fresh Forall_forall in f; eauto.
              pose proof data_fits_in_disk.
              split; try lia.
            }
            {
              rewrite H9, app_length, map_length; lia.
            }
        }
      }
      all: destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
      all: try rewrite H1, firstn_app2.
      all: try rewrite app_length;
      try rewrite map_length; try lia.
      {
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
      }
      {
        apply Forall_forall; intros.
        apply in_map_iff in H2; cleanup_no_match.
        eapply_fresh Forall_forall in f; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
      }
      {
        rewrite H1, app_length, map_length; lia.
      }
    }
  }
  all: try solve [left; eexists; intuition eauto].
  Unshelve.
  apply value0.
Admitted.


  
  

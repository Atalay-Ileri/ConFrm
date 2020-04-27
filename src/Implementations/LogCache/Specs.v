(*
Require Import Framework CacheLayer LoggedDiskLayer DiskLayer CachedDiskLayer.
Require Import LogCache.Definitions LoggedDisk.Definitions.
Open Scope pred_scope.

Lemma oracle_ok_bind_split:
  forall O (L: Language O) T T' (p1: Language.prog L T) (p2: T -> Language.prog  L T') o s,
    Language.oracle_ok L (x <- p1; p2 x) o s ->
    exists o1 o2,
      o = o1 ++ o2 /\
      Language.oracle_ok L p1 o1 s /\
      (forall s' r,
         Language.exec L o1 s p1 (Finished s' r) -> Language.oracle_ok L (p2 r) o2 s').
Proof.
  unfold oracle_ok in *; eauto.
Qed.

Opaque oracle_ok.

Theorem read_ok :
  forall d a vs disk_frame F o s,
    LANG: CachedDiskLang
    LOGIC: CachedDiskHL
    << o, s >>
      PRE: (cached_log_rep disk_frame d s /\
            (F * a |-> vs)%pred d)
      PROG: (read a)
    << r, s' >>
      POST: (cached_log_rep disk_frame d s' /\
             r = fst vs)
      CRASH: (cached_log_rep disk_frame d s')
      OPRE: True
      OPOST: exists oh, oracle_refines_to _ s (Op LoggedDiskOperation _ (LoggedDisk.Read a)) o oh
      OCRASH: exists oh, oracle_refines_to _ s (Op LoggedDiskOperation _ (LoggedDisk.Read a)) o oh.
Proof.
  unfold read; intros.
  step.
  {
    intros.
    eapply p1_ok; eauto with specs.
    admit. (* TODO: Figure out oracle situation for p1_ok *)
    { simpl; eauto. }
    { simpl; unfold cached_log_rep; intros; cleanup. 
      eassign (fun s' => s' = (fst s)); simpl; eauto. }
    {
      simpl; intros; eauto.
      eassign (fun r s' => ((fun s'0 => s'0 = fst s) * [[r = fst s a]] * [[ s' = s ]]) (fst s')) .
      simpl. pred_apply. cancel.
      intros m Hm; eauto.
      destruct s; simpl in *; destruct_lifts; eauto.
    }
    { instantiate (1:= fun _ _ _ _ => True); simpl; eauto. }
    { simpl; instantiate (1:= fun s' => s' = s); simpl; intros.
      destruct s; simpl in *; cleanup; eauto. }
    { instantiate (1:= fun _ _ _ => True); simpl; eauto. }
  }
  
  {
    simpl.
    instantiate (1 := fun s' => cached_log_rep disk_frame d s').
    simpl. intuition eauto.
  }
  { simpl; intros; destruct_lifts; cleanup; eauto. }
  { simpl; intros; cleanup; eauto. }
  
  intros.
  destruct r.
  -
    step.
    { intuition eauto. }
    {
      simpl; intros; destruct_lifts; cleanup.
      intuition.
      admit. (* Solvable *)
    }

  -
    step.
    instantiate (5:= fun o p s => Language.oracle_ok _ p o s).
    eapply p2_ok; eauto with specs.
    admit. (* TODO: Figure out oracle situation for p2_ok *)
    { simpl. (* instantiate (1:= o0). o0. intros; cleanup; eauto.
      eexists; split; [|eauto].
      eauto.
      apply H9. *)
      admit.
    }
    {
      eassign (diskIs (mem_except (snd (snd s')) a)).
      simpl; intros; destruct_lifts; cleanup.
      unfold cached_log_rep in *; cleanup.
      eassign (vs_1, vs_2).            
      admit. (* Solvable *) }
    {
      simpl; intros; eauto.
      eassign (fun r s'' =>
                 cached_log_rep disk_frame d s'' /\
                 r = fst vs /\
                 s'' = s') .
      destruct_lifts; cleanup.
      admit. (* Solvable *)
    }
    { instantiate (1:= fun _ _ _ _ => True); simpl; eauto. }
    { simpl.
      eassign (fun s'' => cached_log_rep disk_frame d s'' /\ s'' = s').
      simpl; intros; destruct_lifts; cleanup.
      admit. (* Solvable *) }
  { instantiate (1:= fun _ _ _ => True); simpl; eauto. }
  {
    simpl.
    instantiate (1 := fun s'' => cached_log_rep disk_frame d s'').
    simpl. intuition eauto.
  }
  { simpl; intros; cleanup; eauto. }

  step.
    { simpl; intros; cleanup; eauto. }
    { simpl in *; intros; cleanup; eauto. }   
    eauto.
  -
    instantiate (2:= fun o p s => Language.oracle_ok _ p o s).
    cleanup; eauto.
    do 2 eexists; repeat (split; intros; eauto).
    unfold Language.oracle_ok in *; simpl; eauto.
    eexists;  repeat (split; intros; eauto).

  - (* OPOST *)
    simpl; intros; cleanup.
    eexists; unfold read; split; eauto.
    do 2 eexists; repeat (split; intros; eauto).
    unfold Language.oracle_ok in *; simpl; eauto.
    eexists;  repeat (split; intros; eauto).

  - (* OCRASH *)
    simpl; intros; cleanup.
    eexists; unfold read; split; eauto.
    do 2 eexists; repeat (split; intros; eauto).
    unfold Language.oracle_ok in *; simpl; eauto.
    eexists;  repeat (split; intros; eauto).
  Unshelve.
  all: try exact CachedDiskLang.
  exact nil.
Admitted.

Fixpoint map2 {A B C} (f: A -> B -> C) (la: list A) (lb : list B) :=
  match la, lb with
  | a :: la', b :: lb' =>
    (f a b)::map2 f la' lb'
  | _, _ =>
    nil
  end.
                       
Theorem write_batch_ok :
  forall al vl vsl d disk_frame F o s,
    << o, s >>
      PRE: (cached_log_rep disk_frame d s /\
            (F * al |L> vsl)%pred d /\
            length al = length vl /\
            length vl = length vsl)
      PROG: (write_batch al vl)
    << r, s' >>
      POST: (exists d' disk_frame',
             cached_log_rep disk_frame' d' s' /\
             (F * al |L> (map2 (fun v vs => (v, fst vs::snd vs)) vl vsl))%pred d')
      CRASH: (exists d' disk_frame' n,
             cached_log_rep disk_frame' d' s' /\
             (F * (firstn n al) |L> (map2 (fun v vs => (v, fst vs::snd vs)) (firstn n vl) (firstn n vsl)) *
              (skipn n al) |L> (skipn n vsl))%pred d' /\
             n <= length vl).
Proof.
  induction al; simpl in *.
  
  {
    step; simpl in *; intros;
    repeat (cleanup; simpl in * ).
    -
      setoid_rewrite firstn_nil.
      setoid_rewrite skipn_nil.
      simpl.
      do 3 eexists; intuition eauto.
      pred_apply; cancel.
    -
      do 2 eexists; intuition eauto.
  }

  {
    destruct vl; simpl in *.
    { step; intros; cleanup; simpl in *; congruence. }
    destruct vsl; simpl in *.
    { intros; eapply pre_impl_false.
      intros; cleanup; simpl in *; congruence. }
   
    step.
    eapply p1_ok; eauto with specs.
    instantiate (3:= fun o p s => oracle_ok p o s).
    admit. (* TODO: Figure out oracle situation for p1_ok *)
    
    { simpl; eauto. }
    { simpl.
      instantiate (3:= fun sx => cached_log_rep disk_frame d sx /\
                             (F * a |-> s * al |L> vsl)%pred d ).
      unfold cached_log_rep; simpl.
      intros; cleanup.
      admit. (* Solvable *)
    }
    {
      simpl.
      instantiate (1:= fun r s' => (diskIs (mem_except (fst s') a) * a |-> v) (fst s') ).
      simpl; intros.
      apply diskIs_extract.
      pred_apply; cancel.
      unfold diskIs; eauto.
    }
     { instantiate (1:= fun _ _ _ _ => True); simpl; eauto. }
    { simpl.
      eassign (fun (s': state) =>
                 match fst s0 a with
                 | Some v0 => diskIs (mem_except (fst s') a) * a |-> v0
                 | None => diskIs (fst s')
                 end (fst s')).
      simpl; intros; destruct_lifts; cleanup.
      apply diskIs_extract.
      pred_apply; cancel.
      unfold diskIs; eauto.
      unfold diskIs; eauto.
    }
    { instantiate (1:= fun _ _ _ => True); simpl; eauto. }
    {
      simpl; intros; cleanup; intuition.
      pred_apply; cancel.
    }
Abort.

Theorem write_ok :
  forall al vl vsl d disk_frame F o s,
    << o, s >>
      PRE: (cached_log_rep disk_frame d s /\
            (F * al |L> vsl)%pred d /\
            length al = length vl /\
            length vl = length vsl)
      PROG: (write_batch al vl)
    << r, s' >>
      POST: (exists d' disk_frame',
             cached_log_rep disk_frame' d' s' /\
             (F * al |L> (map2 (fun v vs => (v, fst vs::snd vs)) vl vsl))%pred d')
      CRASH: (exists d' disk_frame' n,
             cached_log_rep disk_frame' d' s' /\
             (F * (firstn n al) |L> (map2 (fun v vs => (v, fst vs::snd vs)) (firstn n vl) (firstn n vsl)) *
              (skipn n al) |L> (skipn n vsl))%pred d' /\
             n <= length vl).
Proof. Admitted.
*)

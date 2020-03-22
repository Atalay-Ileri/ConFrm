Require Import Framework CacheLayer DiskLayer CachedDiskLayer.
Require Import LogCache.Definitions.
Open Scope pred_scope.

Lemma oracle_ok_bind_split:
  forall T T' (p1: prog T) (p2: T -> prog T') o s,
    oracle_ok (x <- p1; p2 x) o s ->
    exists o1 o2,
      o = o1 ++ o2 /\
      oracle_ok p1 o1 s /\
      (forall s' r,
         exec o1 s p1 (Finished s' r) -> oracle_ok (p2 r) o2 s').
Proof.
  unfold oracle_ok in *; eauto.
Qed.

Opaque oracle_ok.

Theorem read_ok :
  forall d a vs disk_frame F o s,
    << o, s >>
      PRE: (cached_log_rep disk_frame d s /\
            (F * a |-> vs)%pred d)
      PROG: (read a)
    << r, s' >>
      POST: (cached_log_rep disk_frame d s' /\
             r = fst vs)
      CRASH: (cached_log_rep disk_frame d s').
Proof.
  unfold read; intros.  
  step.
  {
    eapply p1_ok; eauto with specs.
    admit. (* TODO: Figure out oracle situation for p1_ok *)
    { simpl; eauto. }
    { simpl; unfold cached_log_rep; intros; cleanup. 
      eassign (fun s' => s' = (fst s)); simpl; eauto. }
    {
      simpl; intros; eauto.
      eassign (fun r (s': state) => ((fun s'0 => s'0 = fst s) * [[r = fst s a]] * [[ s' = s ]]) (fst s')) .
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
    instantiate (5:= fun o p s => oracle_ok p o s).
    eapply p2_ok; eauto with specs.
    admit. (* TODO: Figure out oracle situation for p2_ok *)
    { simpl; eauto. }
    {
      eassign (diskIs (mem_except (snd (snd s')) a)).
      simpl; intros; destruct_lifts; cleanup.
      unfold cached_log_rep in *; cleanup.
      eassign (vs_cur, vs_old).      
      
      admit. (* Solvable *) }
    {
      simpl; intros; eauto.
      eassign (fun r (s'': state) =>
                 cached_log_rep disk_frame d s'' /\
                 r = fst vs /\
                 s'' = s') .
      destruct_lifts; cleanup.
      admit. (* Solvable *)
    }
    { instantiate (1:= fun _ _ _ _ => True); simpl; eauto. }
    { simpl.
      eassign (fun (s'': state) =>cached_log_rep disk_frame d s'' /\ s'' = s').
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
    instantiate (1:= fun o p s => oracle_ok p o s).
    eauto.
Admitted.

                       

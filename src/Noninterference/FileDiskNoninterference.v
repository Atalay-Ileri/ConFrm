Require Import Framework File FileDiskLayer.

Variable disk_size: nat.
Notation "'FileDisk'" := (FileDiskLang disk_size) (at level 0).

Definition same_for_user (s1 s2: FileDisk.(state)) :=
  let u1 := fst s1 in
  let u2 := fst s2 in
  let d1 := snd s1 in
  let d2 := snd s2 in
  u1 = u2 /\
  addrs_match d1 d2 /\
  addrs_match d2 d1 /\
  (forall inum file1 file2,
     d1 inum = Some file1 ->
     d2 inum = Some file2 ->
     (file1.(owner) = u1 \/
      file2.(owner) = u1) ->
     file1 = file2) /\
  (forall inum file1 file2,
     d1 inum = Some file1 ->
     d2 inum = Some file2 ->
     file1.(owner) = file2.(owner) /\ 
     length file1.(blocks) = length file2.(blocks)).

Print SelfSimulation.

(*

Theorem self_simulation_from_wp :
  forall O (L: Language O)
    (valid_state: L.(state) -> Prop)
    (valid_prog: forall T, L.(prog) T -> Prop)
    (R: L.(state) -> L.(state) -> Prop), 

    (forall T (p: L.(prog) T) (s1 s2: L.(state)) o s1' t1,
       valid_state s1 ->
       valid_state s2 ->
       valid_prog T p ->
       R s1 s2 ->
       weakest_precondition L p (fun t' s' => R s1' s' /\ t' = t1) o s1 ->
       exec L o s1 p (Finished s1' t1) ->
       weakest_precondition L p (fun t' s' => R s1' s' /\ t' = t1) o s2) ->
    SelfSimulation L valid_state valid_prog R.
Proof.
  intros.
  constructor.
  intros.
  destruct s1'.
  { (* Finished *)
    eapply H in H3; eauto.
    eapply wp_to_exec in H3; cleanup.
    eexists; simpl; intuition eauto.
    simpl.
 *)

Theorem Invariant_for_file_disk_read:
  SelfSimulation FileDisk (fun _ => True) (fun T p => match p with
                                             | Op _ o =>
                                               match o with
                                               | Read _ _ => True
                                               |_ => False
                                               end
                                             | _ => False
                                             end) same_for_user.
Proof.
  econstructor.
  intros; destruct p; simpl in *; try tauto.  
  destruct p; try tauto; cleanup.
 
  invert_exec; cleanup.
  { (* Read Worked *)
    invert_exec; cleanup.
    { (* Read successful *)
      exists (Finished s2 (Some v)).
      simpl; intuition eauto.
      unfold same_for_user in *; cleanup.
      specialize (H1 a).
      destruct_fresh (snd s2 a); eauto; try congruence.
      specialize (H3 a file f H9 D).
      setoid_rewrite H0 in H10.        
      rewrite H3 in *; eauto.
      repeat (econstructor; eauto; simpl).
      exfalso; apply H1; eauto; setoid_rewrite H9; congruence.
    }          
    { (* Read Failed *)
      exists (Finished s2 None);        
      simpl; split; [| intuition eauto].
      econstructor; simpl.
      repeat split_ors; cleanup;
      try solve [eapply ExecReadFail; eauto].
      
      -
        destruct_fresh (snd s2 a); eauto.
        unfold same_for_user in *; cleanup.
        specialize (H3 a).
        exfalso; eapply H3; try congruence; eauto.
        eapply ExecReadFail; eauto.
      
      - unfold same_for_user in *; cleanup.
        specialize (H3 a).
        destruct_fresh (snd s2 a); eauto; try congruence.
        specialize (H5 a file f H0 D).
        specialize (H6 a file f H0 D); cleanup.
        eapply ExecReadFail; eauto.
        right; right; intuition eauto.
        left; intuition; cleanup; eauto.
        right; apply nth_error_None.
        rewrite <- H7; apply nth_error_None; eauto.
        
        exfalso; eapply H3; eauto;
        setoid_rewrite H0; congruence.
    }
  }
  { (* Read Crashed *)
    exists (Crashed s2).
    intuition eauto;
    simpl; repeat invert_exec; cleanup; eauto.
    { (* Crashed Before *)
      repeat econstructor; eauto.
    }
    {
      split_ors; cleanup;
      inversion H8; cleanup.
      -
        repeat econstructor; eauto.
        unfold same_for_user in *; cleanup.
        specialize (H1 a).
        destruct_fresh (snd s2 a); eauto; try congruence.
        specialize (H3 a file f H6 D).
        specialize (H4 a file f H6 D); cleanup.
        rewrite H3 in *; eauto.        
        exfalso; eapply H1; eauto;
        setoid_rewrite H6; congruence.
        
        unfold same_for_user in *; cleanup; eauto.

      - admit.
    }
    {
      split_ors; cleanup;
      inversion H8; cleanup; eauto.
    }
    Unshelve.
    all: repeat constructor; eauto.
    all: exact user0.
Admitted.

Axiom self_simulation_for_file_disk:
  SelfSimulation FileDisk (fun _ => True) (fun _ _ => True) same_for_user.



oracle_refines_to_same_from_related refinement same_for_user ->

exec_compiled_preserves_validity refinement                           
   (refines_to_valid refinement same_for_user).

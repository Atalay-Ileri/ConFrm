Require Import List Primitives Layer.
Require Import Simulation.Definitions RefinementLift. 
Import ListNotations.

Set Implicit Arguments.

(* This module automates the construction of a refinement
L + L1 refines L + L2 if L1 refines L2 *)
Section HC_Refinement.

Variable O O1 O2: Core.
Variable L1 : Language O1.
Variable L2 : Language O2.
Variable HCL1 : Language (HorizontalComposition O O1).
Variable HCL2 : Language (HorizontalComposition O O2).
Variable RC: CoreRefinement L1 O2.

Definition compile T (o: (HorizontalComposition O O2).(operation) T) : HCL1.(prog) T := 
    match o with
    | P1 p1 => Op (HorizontalComposition O O1) (P1 p1)
    | P2 p2 => lift_L2 _ (RC.(compile_core) p2)
    end.

Definition HC_refines := fun (si: HCL1.(state)) (sa: HCL2.(state)) => 
fst si = fst sa /\ RC.(refines_core) (snd si) (snd sa).

Definition HC_refines_reboot := fun (si: HCL1.(state)) (sa: HCL2.(state)) => 
fst si = fst sa /\ RC.(refines_reboot_core) (snd si) (snd sa).

Lemma HC_exec_compiled_preserves_refinement_finished_core :
forall T (p2: (HorizontalComposition O O2).(operation) T) o1 s1 s1' r u,
  (exists s2, HC_refines s1 s2) ->
  HCL1.(exec) u o1 s1 (compile p2) (Finished s1' r) ->
  (exists s2', HC_refines s1' s2').
  Proof.
    destruct p2; simpl; intros.
    {
        unfold HC_refines in *; cleanup;
        repeat invert_exec.
        simpl; exists (s0, snd x); split; eauto.
    }
    {
        unfold HC_refines in *; cleanup; 
        repeat invert_exec; eauto.
        eapply RC.(exec_compiled_preserves_refinement_finished_core) in H3; eauto.
        cleanup.
        simpl; exists (fst s1, x1); split; eauto.
    }
Qed.

(*
Fixpoint HC_oracle_transformation (o1: oracle HCL1) (o2: oracle L1) :=
match o1 with
| [] => o2 = []
| t1::o1' => 
    match t1 with
    | OpToken _ t =>
        exists t' o2', 
        t = Token2 _ _ t' /\
        o2 = (OpToken _ t') :: o2' /\
        HC_oracle_transformation o1' o2'
    | Cont _ =>
        exists o2', 
        o2 = (Cont _):: o2' /\
        HC_oracle_transformation o1' o2'
    | Crash _ =>
        exists o2', 
        o2 = (Crash _):: o2' /\
        HC_oracle_transformation o1' o2'
    end
end.
*)

Definition HC_transform_oracle := 
map (fun o : Language.token' O1 =>
match o with
| OpToken _ o3 =>
    OpToken (HorizontalComposition O O1) (Token2 O O1 o3)
| Language.Crash _ => Language.Crash (HorizontalComposition O O1)
| Language.Cont _ => Language.Cont (HorizontalComposition O O1)
end).

(* Problem Here is A single token in abstract turns into an oracle for implementation, it is like flattened *)
Definition HC_token_refines T u (d1: HCL1.(state)) 
(p: (HorizontalComposition O O2).(operation) T) 
(get_reboot_state: HCL1.(state) -> HCL1.(state)) (o1: oracle HCL1) t2 : Prop :=
match p with
| P1 p1 => exists t , t2 = Token1 _ _ t /\ o1 = [OpToken (HorizontalComposition O O1) (Token1 O O1 t)] 
| P2 p2 =>
    exists t o, t2 = Token2 _ _ t /\ 
    o1 = HC_transform_oracle o /\
    forall s,
    RC.(token_refines) u (snd d1) p2 (fun s1 => snd (get_reboot_state (s, s1))) o t
end.
    

Definition HC_Core_Refinement : CoreRefinement HCL1 (HorizontalComposition O O2) :=
Build_CoreRefinement compile HC_refines HC_refines_reboot
HC_token_refines
HC_exec_compiled_preserves_refinement_finished_core.

Definition HC_Refinement := LiftRefinement HCL2 HC_Core_Refinement.

(*
Lemma HC_oracle_transformation_id:
forall o1 o2,
HC_oracle_transformation
(map
    (fun o : Language.token' O1 =>
    match o with
    | OpToken _ o1 =>
        OpToken (HorizontalComposition O O1)
          (Token2 O O1 o1)
    | Language.Crash _ =>
        Language.Crash (HorizontalComposition O O1)
    | Language.Cont _ =>
        Language.Cont (HorizontalComposition O O1)
    end) o1) o2 ->
    o1 = o2.
  Proof.
    induction o1; simpl; intros; eauto.
    {
      destruct a; simpl; cleanup; eauto.
      inversion H; subst.
      all: erewrite IHo1; eauto.
    }
  Qed.

Lemma HC_oracle_transformation_id_crashed:
forall o1 o2 o,
HC_oracle_transformation
(map
    (fun o : Language.token' O1 =>
    match o with
    | OpToken _ o1 =>
        OpToken (HorizontalComposition O O1)
          (Token2 O O1 o1)
    | Language.Crash _ =>
        Language.Crash (HorizontalComposition O O1)
    | Language.Cont _ =>
        Language.Cont (HorizontalComposition O O1)
    end) o1 ++ o) o2 ->
    exists o2' rest,
    o2 = o2'++rest /\
    o1 = o2' /\ HC_oracle_transformation o rest.
  Proof.
    induction o1; simpl; intros; eauto.
    do 2 eexists; simpl; intuition eauto.
    simpl; eauto.
    {
      destruct a; simpl; cleanup; eauto.
      inversion H; subst.

      edestruct IHo1; eauto; cleanup; eauto.
      do 2 eexists; intuition eauto.
      simpl; eauto.

      edestruct IHo1; eauto; cleanup; eauto.
      do 2 eexists; intuition eauto.
      simpl; eauto.

      edestruct IHo1; eauto; cleanup; eauto.
      do 2 eexists; intuition eauto.
      simpl; eauto.
    }
  Qed.

  Lemma HC_oracle_transformation_app:
forall x0 x1 x2,
HC_oracle_transformation  x0 (x1 ++ x2) ->
exists x x',
x0 = x ++ x' /\
x = map
(fun o : Language.token' O1 =>
    match o with
    | OpToken _ o1 =>
        OpToken (HorizontalComposition O O1)
          (Token2 O O1 o1)
    | Language.Crash _ =>
        Language.Crash (HorizontalComposition O O1)
    | Language.Cont _ =>
        Language.Cont (HorizontalComposition O O1)
    end) x1 /\ 
  HC_oracle_transformation x' x2.
  Proof.
    induction x0; simpl; intros; eauto.
    {
      exists [], [].
      apply app_eq_nil in H; cleanup.
      simpl; intuition eauto.
    }
    {
    cleanup; eauto.
    {
      destruct x1.
      {
        exists []; simpl in *; eexists; intuition.
        cleanup; simpl.
        do 2 eexists; intuition eauto.
      }
      {
        simpl in *; cleanup.
        eapply IHx0 in H1; eauto; cleanup.
        do 2 eexists; intuition eauto.
        simpl; eauto.
      }
    }
    {
      destruct x1.
      {
        exists []; simpl in *; eexists; intuition.
        cleanup; simpl.
        do 2 eexists; intuition eauto.
      }
      {
        simpl in *; cleanup.
        eapply IHx0 in H0; eauto; cleanup.
        do 2 eexists; intuition eauto.
        simpl; eauto.
      }
    }
    {
      destruct x1.
      {
        exists []; simpl in *; eexists; intuition.
        cleanup; simpl.
        do 2 eexists; intuition eauto.
      }
      {
        simpl in *; cleanup.
        eapply IHx0 in H0; eauto; cleanup.
        do 2 eexists; intuition eauto.
        simpl; eauto.
      }
    }
    }
  Qed.

  Lemma HC_oracle_transformation_same:
    forall 
      (o1 : list (Language.token' O1)),
    HC_oracle_transformation 
      (map
          (fun o : Language.token' O1 =>
          match o with
          | OpToken _ o3 =>
              OpToken (HorizontalComposition O O1) (Token2 O O1 o3)
          | Language.Crash _ => Language.Crash (HorizontalComposition O O1)
          | Language.Cont _ => Language.Cont (HorizontalComposition O O1)
          end) o1) o1.
    Proof.
      induction o1; simpl; intros; eauto.
      destruct a; simpl; intuition eauto.
    Qed.


Lemma HC_oracle_transformation_id_rev:
forall T (p: L1.(prog) T) x0 u x3 s s' r,
HC_oracle_transformation x0 x3 ->
exec L1 u x3 s p (Finished s' r) ->
x0 = map
(fun o : Language.token' O1 =>
    match o with
    | OpToken _ o1 =>
        OpToken (HorizontalComposition O O1)
          (Token2 O O1 o1)
    | Language.Crash _ =>
        Language.Crash (HorizontalComposition O O1)
    | Language.Cont _ =>
        Language.Cont (HorizontalComposition O O1)
    end) x3.
  Proof.
    induction p; simpl; intros.
    {
      unfold HC_oracle_transformation in *.
      invert_exec.
      simpl in *.
      destruct x0; eauto.
      congruence.
      cleanup; simpl in *.
      destruct x0; cleanup; try congruence.
    }
    {
    unfold HC_oracle_transformation in *.
    invert_exec.
    simpl in *.
    destruct x0; eauto.
    congruence.
    cleanup; simpl in *.
    destruct x0; cleanup; congruence.
    }
    {
    invert_exec.
    simpl in *.
    eapply HC_oracle_transformation_app in H0; cleanup.
    edestruct IHp.
    2: eauto.
    apply HC_oracle_transformation_same.
    erewrite H with (x0 := x5); eauto.
    rewrite map_app; eauto.
    }
  Qed.


  Lemma HC_oracle_transformation_unique:
  forall x0 x1 x2,
  HC_oracle_transformation x0 x1 ->
  HC_oracle_transformation x0 x2 ->
  x1 = x2.
    Proof.
      induction x0; simpl; intros; subst; eauto.
      cleanup.
      inversion H0.
      eapply IHx0 in H4; eauto; subst; eauto.
      eapply IHx0 in H2; eauto; subst; eauto.
      eapply IHx0 in H2; eauto; subst; eauto.
    Qed.

    Lemma HC_oracle_transformation_app_composed:
forall o1 o2 o,
HC_oracle_transformation (o1 ++ o2) o ->
exists x1 x2,
o = x1 ++ x2 /\
HC_oracle_transformation o1 x1 /\
HC_oracle_transformation o2 x2.
Proof.
  induction o1; simpl; intros.
  {
    do 2 eexists; simpl; intuition eauto.
    simpl; eauto.
  }
  {
    cleanup.
    - eapply IHo1 in H1; cleanup.
      do 2 eexists; intuition eauto.
      simpl; eauto.
    - eapply IHo1 in H0; cleanup.
      do 2 eexists; intuition eauto.
      simpl; eauto.
    - eapply IHo1 in H0; cleanup.
    do 2 eexists; intuition eauto.
    simpl; eauto.
  }
Qed.

Lemma HC_oracle_transformation_merge:
forall o1 o2 x1 x2,
HC_oracle_transformation o1 x1 ->
HC_oracle_transformation o2 x2 ->
HC_oracle_transformation (o1 ++ o2) (x1 ++ x2).
Proof.
  induction o1; simpl; intros.
  {
    subst; eauto.
  }
  {
    cleanup;
    eapply IHo1 in H0; eauto; cleanup;
    do 2 eexists; intuition eauto.
  }
Qed.

Lemma HC_oracle_transformation_prefix_l:
forall o1 o2 o3 o4 x1 x4,
  HC_oracle_transformation o1 x4 ->
  HC_oracle_transformation o2 x1 ->
  o1 ++ o3 = o2 ++ o4 ->
  exists x x',
  x4 ++ x = x1 ++ x'.
  Proof.
    induction o1; simpl; intros;
    destruct o2; simpl in *; cleanup; 
    simpl; eauto;
    edestruct IHo1; eauto;
    cleanup; do 2 eexists; eauto;
    rewrite cons_app;
    rewrite H; simpl; eauto.
    Unshelve.
    all: constructor.
  Qed.

  Lemma HC_oracle_transformation_eq_l:
forall o1 o2 x,
  HC_oracle_transformation o1 x ->
  HC_oracle_transformation o2 x ->
  o1 = o2.
  Proof.
    induction o1; simpl; intros;
    destruct o2; simpl in *; cleanup; 
    simpl; eauto; try congruence;
    erewrite IHo1; eauto.
  Qed.
*)

    Lemma HC_map_ext_eq:
    forall x x1,
    HC_transform_oracle x1 =
    HC_transform_oracle x ->
    x1 = x.
      Proof.
        intros. 
        eapply map_ext_eq in H; eauto.
        intros; cleanup; intuition congruence.
      Qed.

      Lemma HC_map_ext_eq_prefix:
    forall x x1 x' x1',
    HC_transform_oracle x1 ++ x1' =
    HC_transform_oracle x ++ x' ->
    exists x1' x', x1 ++ x1' = x ++ x'.
      Proof.
        intros. 
        eapply map_ext_eq_prefix in H; eauto.
        solve [repeat constructor].
        intros; cleanup; intuition congruence.
      Qed.

      Ltac HC_map_ext_unify :=
        match goal with
        |[H: HC_transform_oracle _ 
        = HC_transform_oracle _ |- _] =>
          apply HC_map_ext_eq in H; subst
        | [H: HC_transform_oracle _ 
        = map _ _ |- _] =>
          apply HC_map_ext_eq in H; subst
        |[H: HC_transform_oracle _ ++ _ 
         = HC_transform_oracle _ ++ _ |- _] =>
          apply HC_map_ext_eq_prefix in H
        end; repeat HC_map_ext_unify.

    (* HC preserving simulations *)
    Lemma HC_exec_exists_2_to_1:
    forall T (p: HCL2.(prog) T) o1 o2 u s1 s2 s1' r grs,
     let HCR := HC_Refinement in
     (forall T (o : operation O2 T) s1 s2 s1' r x1 x2 grs',
    exec L1 u x1 s1 (compile_core RC o) (Finished s1' r) ->
    Simulation.Definitions.token_refines RC u s1 o grs' x1 x2 ->
    RC.(refines_core) s1 s2 ->
    exists s2', Core.exec O2 u x2 s2 o (Finished s2' r) /\
    RC.(refines_core) s1' s2') ->
    
    exec HCL1 u o1 s1 (HCR.(Simulation.Definitions.compile) p) (Finished s1' r) ->
    HCR.(Simulation.Definitions.oracle_refines) u s1 p grs o1 o2 ->
    HCR.(Simulation.Definitions.refines) s1 s2 ->
    exists s2', exec HCL2 u o2 s2 p (Finished s2' r) /\
    HCR.(Simulation.Definitions.refines) s1' s2'.
      Proof.
        induction p; simpl; intros.
        {
          cleanup.
          unfold HC_refines in *; cleanup; eauto.
          destruct o.
          {
            invert_exec'' H0.
            repeat invert_exec.
            simpl in *; cleanup.
            eexists; repeat econstructor; eauto.
          }
          {
            simpl in *; cleanup.
            repeat invert_exec.
            simpl in *; cleanup.
            HC_map_ext_unify.
            edestruct H; eauto; cleanup.
            eexists; repeat econstructor; eauto.
          }
        }
        {
          unfold HC_refines in *; cleanup; eauto.
          split_ors; cleanup; simpl in *; 
          repeat invert_exec.
          eexists; repeat econstructor; eauto.
        }
        {
        invert_exec; simpl in *.
        split_ors; cleanup.
        eapply exec_deterministic_wrt_oracle_prefix in H1; eauto; cleanup.
        rewrite <- app_assoc; eauto.
    
        eapply exec_finished_deterministic_prefix in H1; eauto; cleanup.
        eapply exec_deterministic_wrt_oracle in H4; eauto; cleanup.
    
        simpl in *; eauto.
        cleanup.
        edestruct IHp; eauto; cleanup.
        edestruct H; eauto; cleanup.
    
        eexists; split; eauto. 
        repeat econstructor; eauto.
      }
      Unshelve.
      apply (fst s1).
      eauto.
      Qed.

End HC_Refinement.

Arguments HC_Refinement {_ _ _ _}.




Require Import Eqdep Lia Lra Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference LoggedDiskRefinement.
Require Import ATC_ORS HSS ATCDLayer ATCD_Simulation ATCD_AOE  LogCache_FinishedNotCrashed.
Import FileDiskLayer.

Ltac unify_execs_prefix :=
  match goal with 
  | [ H: LayerImplementation.exec' ?u ?o1 ?s ?p (Finished _ _),
      H0: LayerImplementation.exec' ?u ?o2 ?s ?p (Finished _ _),
      H1: ?o1 ++ _ = ?o2 ++ _ |- _] =>
      eapply exec_finished_deterministic_prefix in H; [|apply H0| apply H1]
  | [ H: LayerImplementation.exec' ?u ?o1 ?s ?p (Finished _ _),
      H0: exec _ ?u ?o2 ?s ?p (Finished _ _),
      H1: ?o1 ++ _ = ?o2 ++ _ |- _] =>
      eapply exec_finished_deterministic_prefix in H; [|apply H0| apply H1]
  | [ H: exec _ ?u ?o1 ?s ?p (Finished _ _),
      H0: exec _ ?u ?o2 ?s ?p (Finished _ _),
      H1: ?o1 ++ _ = ?o2 ++ _ |- _] =>
      eapply exec_finished_deterministic_prefix in H; [|apply H0| apply H1]
  | [ H: LayerImplementation.exec' ?u ?o1 ?s ?p (Finished _ _),
      H0: LayerImplementation.exec' ?u ?o2 ?s ?p (Crashed _),
      H1: ?o1 ++ _ = ?o2 ++ _ |- _] =>
      exfalso; eapply finished_not_crashed_oracle_prefix; [apply H| apply H1 | apply H0]
  | [ H: LayerImplementation.exec' ?u ?o1 ?s ?p (Finished _ _),
      H0: LayerImplementation.exec' ?u (?o1 ++ _) ?s ?p (Crashed _) |- _] =>
      exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto;
      try solve [rewrite <- app_assoc; eauto]
  | [ H: LayerImplementation.exec' ?u ?o1 ?s ?p (Finished _ _),
      H0: exec _ ?u (?o1 ++ _) ?s ?p (Crashed _) |- _] =>
      exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto;
      try solve [rewrite <- app_assoc; eauto]
  | [ H: LayerImplementation.exec' ?u ?o1 ?s ?p (Finished _ _),
      H0: exec _ ?u ?o2 ?s ?p (Crashed _),
      H1: ?o1 ++ _ = ?o2 |- _] =>
      exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto;
      try solve [rewrite <- app_assoc; setoid_rewrite app_nil_r at 2; eauto]
  end.

  (*
  Lemma ATCD_ORS_compositional:
  forall l_selector u T (p1 p2: prog ATCLang T) T' (p3 p4: T -> prog ATCLang T') rec P RS RSR, 
  (forall l_selector, oracle_refines_same_from_related ATCD_Refinement u p1 p2 rec (ATCD_reboot_list l_selector) RS) ->
  
  (forall u o oa s1 s2 s1' s2' r1 r2 grs,
  LayerImplementation.exec' u o s1 (ATCD_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
  LayerImplementation.exec' u o s2 (ATCD_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
  refines_related ATCD_Refinement RS s1 s2 ->
  oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement T u s1 p1 grs o oa ->
  oracle_refines  _ _ ATCDLang ATCLang ATCD_CoreRefinement T u s2 p2 grs o oa ->
  oracle_refines_same_from_related ATCD_Refinement u (p3 r1) (p4 r2) rec (ATCD_reboot_list l_selector) P) ->
  
  (forall l_selector, oracle_refines_same_from_related_reboot _ _ _ _ ATCD_Refinement u rec rec rec (ATCD_reboot_list l_selector) RSR) ->
  
  (forall u o1 o2 o3 o4 oa1 oa2 s1 s2 s1' s2' r1 r2 grs,
  LayerImplementation.exec' u o1 s1 (ATCD_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
  LayerImplementation.exec' u o2 s2 (ATCD_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
  oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement T u s1 p1 grs o1 oa1 ->
  oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement T u s2 p2 grs o2 oa2 ->
  o1 ++ o3 = o2 ++ o4 ->
  refines_related ATCD_Refinement RS s1 s2 ->
  o1 = o2) ->
  
  (forall T (p: prog ATCLang T) s s' r o o_abs grs, 
  LayerImplementation.exec' u o s (ATCD_Refinement.(Simulation.Definitions.compile) p) (Finished s' r) ->
  oracle_refines _ _ _ _ ATCD_CoreRefinement T u s p grs o o_abs ->
  forall grs', oracle_refines _ _ _ _ ATCD_CoreRefinement T u s p grs' o o_abs) ->
  
  (forall u o oa1 oa2 s1 s2 s1' s2' r1 r2 grs,
  LayerImplementation.exec' u o s1 (ATCD_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
  LayerImplementation.exec' u o s2 (ATCD_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
  refines_related ATCD_Refinement RS s1 s2 ->
  oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement _ u s1 p1 grs o oa1 ->
  oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement _ u s2 p2 grs o oa2 ->
  refines_related ATCD_Refinement P s1' s2') ->

  (forall u o1 o2 oa1 oa2 s1 s2 s1' s2' r1,
  LayerImplementation.exec' u o1 s1 (ATCD_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
  refines_related ATCD_Refinement RS s1 s2 ->
  oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement T u s1 p1 (ATCD_reboot_f (hd (fun _ => 0) l_selector)) o1 oa1 ->
  oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement T u s2 p2 (ATCD_reboot_f (hd (fun _ => 0) l_selector)) (o1++o2) oa2 ->
  ~LayerImplementation.exec' u (o1 ++ o2) s2 (ATCD_Refinement.(Simulation.Definitions.compile) p2) (Crashed s2')) ->

  (forall u o1 o2 oa1 oa2 s1 s2 s1' s2' r2,
  LayerImplementation.exec' u o1 s2 (ATCD_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
  refines_related ATCD_Refinement RS s1 s2 ->
  oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement T u s1 p1 (ATCD_reboot_f (hd (fun _ => 0) l_selector)) (o1++o2) oa1 ->
  oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement T u s2 p2 (ATCD_reboot_f (hd (fun _ => 0) l_selector)) o1 oa2 ->
  ~LayerImplementation.exec' u (o1 ++ o2) s1 (ATCD_Refinement.(Simulation.Definitions.compile) p1) (Crashed s1')) ->
  
  (forall u o oa1 oa2 s1 s2 s1' s2',
  LayerImplementation.exec' u o s1 (ATCD_Refinement.(Simulation.Definitions.compile) (Bind p1 p3)) (Crashed s1') ->
  LayerImplementation.exec' u o s2 (ATCD_Refinement.(Simulation.Definitions.compile) (Bind p2 p4)) (Crashed s2') ->
  refines_related ATCD_Refinement RS s1 s2 ->
  oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement _ u s1 (Bind p1 p3) (ATCD_reboot_f (hd (fun _ => 0) l_selector)) o oa1 ->
  oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement _ u s2 (Bind p2 p4) (ATCD_reboot_f (hd (fun _ => 0) l_selector)) o oa2 ->
  refines_related_reboot _ _ _ _ ATCD_Refinement RSR ((ATCD_reboot_f (hd (fun _ => 0) l_selector)) s1') ((ATCD_reboot_f (hd (fun _ => 0) l_selector)) s2')) ->

  oracle_refines_same_from_related ATCD_Refinement u (Bind p1 p3) (Bind p2 p4) rec (ATCD_reboot_list l_selector) RS.
  Proof.
      unfold oracle_refines_same_from_related,
      ATCD_reboot_list; 
      simpl; intros; destruct l_selector; simpl in *; intuition.
      {
        destruct l_o_imp; simpl in *; try tauto;
      cleanup; simpl in *; try congruence; try lia;
      try solve [cleanup; tauto].
      {  
        repeat split_ors; cleanup;
        try solve [cleanup; tauto].
        repeat match goal with
        | [H: exec ATCDLang _ _ _ (Bind _ _) _ |- _] =>
        invert_exec'' H
        end.
        repeat match goal with
        | [H: forall _, _ |- _] =>
        specialize (H (ATCD_reboot_f (fun _ => 0)))
        end.
        repeat split_ors; cleanup; repeat unify_execs; cleanup.
        match goal with
        | [H: exec _ _ (?o ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ ?o ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto
        end.
        match goal with
        | [H: exec _ _ (?o1 ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ _ ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto;
        setoid_rewrite app_nil_r at 2; eauto
        end.
        match goal with
        | [H: exec _ _ (?o1 ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ _ ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto;
        setoid_rewrite app_nil_r at 2; eauto
        end.
  
        match goal with
        | [H: exec _ _ _ ?s ?p (Finished _ _),
          H0: LayerImplementation.exec' _ _ ?s ?p (Finished _ _) |- _] =>
        eapply exec_finished_deterministic_prefix in H; try solve [apply H0];
        eauto; cleanup
        end.
        match goal with
        | [H: exec _ _ _ ?s ?p (Finished _ _),
          H0: LayerImplementation.exec' _ _ ?s ?p (Finished _ _) |- _] =>
        eapply exec_finished_deterministic_prefix in H; try solve [apply H0];
        eauto; cleanup
        end.
        match goal with
        | [H: _++_ = ?l++?l0,
          H0: _++_ = ?l++?l0 |- _] =>
        rewrite <- H in H0; clear_lists; subst
        end.
        repeat match goal with
        | [H: exec _ _ ?o ?s ?p _,
          H0: LayerImplementation.exec' _ ?o ?s ?p _ |- _] =>
        eapply_fresh  exec_deterministic_wrt_oracle in H; try solve [apply H0];
        eauto; cleanup
        end.
  
        match goal with
        | [H: LayerImplementation.exec' _ ?o1 ?s1 _ (Finished _ _),
          H0: LayerImplementation.exec' _ ?o2 ?s2 _ (Finished _ _),
          H1: ?o1 ++ _ = ?o2 ++ _,
          A2: oracle_refines _ _ _ _ _ _ _ _ _ _ ?o1 _, 
          A3: oracle_refines _ _ _ _ _ _ _ _ _ _ ?o2 _,
          A4: refines_related _ _ ?s1 ?s2 |- _] =>
          specialize H2 with (1:=H)(2:= H0)(3:= A2)(4:=A3)(5:=H1)(6:= A4); subst; cleanup
        end.
        

        specialize (H [] [x3] [x12] [x5]).
        simpl in *.
        specialize H with (1 := H8).
        simpl in *.
        assert ([x12] = [x5]). {
          eapply H.
        intuition; left; do 2 eexists; 
        intuition eauto.
        intuition; left; do 2 eexists; 
        intuition eauto.
        }
        cleanup.
        match goal with
        | [A: LayerImplementation.exec' _ _ ?s1_imp _ (Finished _ _),
          A0: LayerImplementation.exec' _ _ ?s2_imp _ (Finished _ _),
          A1: refines_related _ _ ?s1_imp ?s2_imp,
          A2: oracle_refines _ _ _ _ _ _ _ ?s1_imp _ _ _ _, 
          A3: oracle_refines _ _ _ _ _ _ _ ?s2_imp _ _ _ _ |- _] =>
          specialize H0 with (1:=A)(2:= A0)(3:= A1)(4:=A2)(5:=A3); subst; cleanup
        end.
        specialize (H0 [x4] [x13] [x6]).
        eapply_fresh H4 in H19; eauto.

        eapply_fresh exec_compiled_preserves_refinement_finished in H19; eauto.
        eapply_fresh exec_compiled_preserves_refinement_finished in H20; eauto.
        cleanup.
        assert ([x13] = [x6]). {
          eapply H0.
          eauto.
          simpl.
          intuition; left; do 2 eexists; 
          intuition eauto.
          simpl.
          intuition; left; do 2 eexists; 
          intuition eauto.
        }
        cleanup; eauto.
        unfold refines_related in *; simpl in *; cleanup; eauto.
        unfold refines_related in *; simpl in *; cleanup; eauto.
        match goal with
        | [H: ?o ++ _ = _ ++ _ |- ?o ++ _ = _ ++ _] =>
        rewrite H; eauto
        end.
      }
    }
      {
        destruct l_o_imp; 
        simpl in *; cleanup; try tauto.
        repeat split_ors; cleanup; simpl in *;
        try solve [cleanup; try tauto; try lia].
        {  
        repeat split_ors; cleanup;
        try solve [cleanup; tauto].
        repeat match goal with
        | [H: exec ATCDLang _ _ _ (Bind _ _) _ |- _] =>
        invert_exec'' H
        end.
        repeat match goal with
        | [H: forall _, _ |- _] =>
        specialize (H (ATCD_reboot_f t))
        end.
        repeat split_ors; cleanup; repeat unify_execs; cleanup.
        match goal with
        | [H: exec _ _ (?o ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ ?o ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto
        end.
        match goal with
        | [H: exec _ _ (?o1 ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ _ ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto;
        setoid_rewrite app_nil_r at 2; eauto
        end.
        match goal with
        | [H: exec _ _ (?o1 ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ _ ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto;
        setoid_rewrite app_nil_r at 2; eauto
        end.
  
        match goal with
        | [H: exec _ _ _ ?s ?p (Finished _ _),
          H0: LayerImplementation.exec' _ _ ?s ?p (Finished _ _) |- _] =>
        eapply exec_finished_deterministic_prefix in H; try solve [apply H0];
        eauto; cleanup
        end.
        match goal with
        | [H: exec _ _ _ ?s ?p (Finished _ _),
          H0: LayerImplementation.exec' _ _ ?s ?p (Finished _ _) |- _] =>
        eapply exec_finished_deterministic_prefix in H; try solve [apply H0];
        eauto; cleanup
        end.
        match goal with
        | [H: _++_ = ?l++?l0,
          H0: _++_ = ?l++?l0 |- _] =>
        rewrite <- H in H0; clear_lists; subst
        end.
        repeat match goal with
        | [H: exec _ _ ?o ?s ?p _,
          H0: LayerImplementation.exec' _ ?o ?s ?p _ |- _] =>
        eapply_fresh  exec_deterministic_wrt_oracle in H; try solve [apply H0];
        eauto; cleanup
        end.
  
        match goal with
        | [H: LayerImplementation.exec' _ ?o1 ?s1 _ (Finished _ _),
          H0: LayerImplementation.exec' _ ?o2 ?s2 _ (Finished _ _),
          H1: ?o1 ++ _ = ?o2 ++ _,
          A2: oracle_refines _ _ _ _ _ _ _ _ _ _ ?o1 _, 
          A3: oracle_refines _ _ _ _ _ _ _ _ _ _ ?o2 _,
          A4: refines_related _ _ ?s1 ?s2 |- _] =>
          specialize H2 with (1:=H)(2:= H0)(3:= A2)(4:=A3)(5:=H1)(6:= A4); subst; cleanup
        end.
        
        
        specialize (H [] [x3] [x12] [x5]).
        simpl in *.
        specialize H with (1 := H8).
        simpl in *.
        assert ([x12] = [x5]). {
          eapply H.
        intuition; left; do 2 eexists; 
        intuition eauto.
        intuition; left; do 2 eexists; 
        intuition eauto.
        }
        cleanup.
        match goal with
        | [A: LayerImplementation.exec' _ _ ?s1_imp _ (Finished _ _),
          A0: LayerImplementation.exec' _ _ ?s2_imp _ (Finished _ _),
          A1: refines_related _ _ ?s1_imp ?s2_imp,
          A2: oracle_refines _ _ _ _ _ _ _ ?s1_imp _ _ _ _, 
          A3: oracle_refines _ _ _ _ _ _ _ ?s2_imp _ _ _ _ |- _] =>
          specialize H0 with (1:=A)(2:= A0)(3:= A1)(4:=A2)(5:=A3); subst; cleanup
        end.
        specialize (H0 [x4] [x13] [x6]).
        eapply_fresh H4 in H18; eauto.
        eapply_fresh exec_compiled_preserves_refinement_finished in H18; eauto.
        eapply_fresh exec_compiled_preserves_refinement_finished in H19; eauto.
        cleanup.
        assert ([x13] = [x6]). {
          eapply H0.
          eauto.
          simpl.
          intuition; left; do 2 eexists; 
          intuition eauto.
          simpl.
          intuition; left; do 2 eexists; 
          intuition eauto.
        }
        cleanup; eauto.
        unfold refines_related in *; simpl in *; cleanup; eauto.
        unfold refines_related in *; simpl in *; cleanup; eauto.
        match goal with
        | [H: ?o ++ _ = _ ++ _ |- ?o ++ _ = _ ++ _] =>
        rewrite H; eauto
        end.
      }
      eapply_fresh H1 in H16; eauto.
      specialize (Hx H14); subst.
      
      repeat match goal with
        | [H: exec ATCDLang _ _ _ (Bind _ _) _ |- _] =>
        invert_exec'' H
        end.
      {
        repeat split_ors; cleanup; repeat unify_execs; cleanup.
        match goal with
        | [H: exec _ _ (?o ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ ?o ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto
        end.
        match goal with
        | [H: exec _ _ (?o1 ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ _ ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto;
        setoid_rewrite app_nil_r at 2; eauto
        end.
        match goal with
        | [H: exec _ _ (?o1 ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ _ ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto;
        setoid_rewrite app_nil_r at 2; eauto
        end.
  
        match goal with
        | [H: exec _ _ _ ?s ?p (Finished _ _),
          H0: LayerImplementation.exec' _ _ ?s ?p (Finished _ _) |- _] =>
        eapply exec_finished_deterministic_prefix in H; try solve [apply H0];
        eauto; cleanup
        end.
        match goal with
        | [H: exec _ _ _ ?s ?p (Finished _ _),
          H0: LayerImplementation.exec' _ _ ?s ?p (Finished _ _) |- _] =>
        eapply exec_finished_deterministic_prefix in H; try solve [apply H0];
        eauto; cleanup
        end.
        match goal with
        | [H: _++_ = ?l++?l0,
          H0: _++_ = ?l++?l0 |- _] =>
        rewrite <- H in H0; clear_lists; subst
        end.
        repeat match goal with
        | [H: exec _ _ ?o ?s ?p _,
          H0: LayerImplementation.exec' _ ?o ?s ?p _ |- _] =>
        eapply_fresh  exec_deterministic_wrt_oracle in H; try solve [apply H0];
        eauto; cleanup
        end.
  
        match goal with
        | [H: LayerImplementation.exec' _ ?o1 ?s1 _ (Finished _ _),
          H0: LayerImplementation.exec' _ ?o2 ?s2 _ (Finished _ _),
          H1: ?o1 ++ _ = ?o2 ++ _,
          A2: oracle_refines _ _ _ _ _ _ _ _ _ _ ?o1 _, 
          A3: oracle_refines _ _ _ _ _ _ _ _ _ _ ?o2 _,
          A4: refines_related _ _ ?s1 ?s2 |- _] =>
          specialize H2 with (1:=H)(2:= H0)(3:= A2)(4:=A3)(5:=H1)(6:= A4); subst; cleanup
        end.
        
        specialize H4 with (1:= H22) (2:= H23) (3:= H8).
        specialize (H l_selector [x1] [x10] [x3]).
        simpl in *.
        specialize H with (1 := H8).
        simpl in *.
        assert ([x10] = [x3]). {
          eapply H.
        intuition; left; do 2 eexists; 
        intuition eauto.

        intuition; left; do 2 eexists; 
        intuition eauto.
        }
        cleanup_no_match.
        match goal with
        | [A: LayerImplementation.exec' _ _ ?s1_imp _ (Finished _ _),
          A0: LayerImplementation.exec' _ _ ?s2_imp _ (Finished _ _),
          A1: refines_related _ _ ?s1_imp ?s2_imp,
          A2: oracle_refines _ _ _ _ _ _ _ ?s1_imp _ _ _ _, 
          A3: oracle_refines _ _ _ _ _ _ _ ?s2_imp _ _ _ _ |- _] =>
          specialize H0 with (1:=A)(2:= A0)(3:= A1)(4:=A2)(5:=A3); subst; cleanup_no_match
        end.
        specialize (H0 (x2::l_o_imp) (x11::l) (x4::l)).
        assert ((x11::l) = (x4::l)). {
          eapply H0.
          eapply H4; eauto.
          simpl; intuition eauto.
          simpl; intuition eauto.
        }
        cleanup; eauto.
        match goal with
        | [H: ?o ++ _ = _ ++ _ |- ?o ++ _ = _ ++ _] =>
        rewrite H; eauto
        end.
      }
      {
        repeat split_ors; cleanup; repeat unify_execs; cleanup.
        match goal with
        | [H: exec _ _ (?o ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ ?o ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto
        end.
        match goal with
        | [H: exec _ _ (?o1 ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ _ ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto;
        setoid_rewrite app_nil_r at 2; eauto
        end.

        match goal with
        | [H: exec _ _ _ ?s ?p (Finished _ _),
          H0: LayerImplementation.exec' _ _ ?s ?p (Finished _ _) |- _] =>
        eapply exec_finished_deterministic_prefix in H; try solve [apply H0];
        eauto; cleanup
        end.

        exfalso; eauto.

        match goal with
        | [H: LayerImplementation.exec' _ (?o1 ++ _) ?s ?p _,
        H0: exec _ _ _ ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto;
        setoid_rewrite app_nil_r at 2; eauto
        end.
      }
      {
        repeat split_ors; cleanup; repeat unify_execs; cleanup.
        match goal with
        | [H: exec _ _ (?o ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ ?o ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto
        end.
        

        match goal with
        | [H: exec _ _ _ ?s ?p (Finished _ _),
          H0: LayerImplementation.exec' _ _ ?s ?p (Finished _ _) |- _] =>
        eapply exec_finished_deterministic_prefix in H; try solve [apply H0];
        eauto; cleanup
        end.

        exfalso; eauto.

        match goal with
        | [H: exec _ _ (?o1 ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ _ ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto;
        setoid_rewrite app_nil_r at 2; eauto
        end.

        match goal with
        | [H: LayerImplementation.exec' _ (?o1 ++ _) ?s ?p _,
        H0: exec _ _ _ ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto;
        setoid_rewrite app_nil_r at 2; eauto
        end.
      }
      {
        repeat split_ors; cleanup; repeat unify_execs; cleanup.
        specialize (H (t::l_selector) (o::l_o_imp) (o1::l) (o0::l)).
        simpl in *.
        specialize H with (1 := H8).
        simpl in *.
        {
          eapply H.
          intuition; right; do 2 eexists; 
          intuition eauto.

          intuition; right; do 2 eexists; 
          intuition eauto.
        }
        match goal with
        | [H: LayerImplementation.exec' _ (?o ++ _) ?s ?p _,
          H0: exec _ _ ?o ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto
        end.
        match goal with
        | [H: LayerImplementation.exec' _ (?o ++ _) ?s ?p _,
          H0: exec _ _ ?o ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto
        end.
        match goal with
        | [H: LayerImplementation.exec' _ (?o ++ _) ?s ?p _,
          H0: exec _ _ ?o ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto
        end.
      }
      {
        eapply H7; eauto.
      } 
    }
    Unshelve.
    all: eauto.
  Qed.
*)


  Opaque LogCache.recover.
  Lemma ATCD_ORS_recover:
      forall l_selector u R,
      oracle_refines_same_from_related_reboot _ _ _ _ ATCD_Refinement u
      (Simulation.Definitions.compile ATC_Refinement File.recover)
      (Simulation.Definitions.compile ATC_Refinement File.recover)
      (Simulation.Definitions.compile ATC_Refinement File.recover)
      (ATCD_reboot_list l_selector) R. (* (ATCLang_related_states_reboot u' ex). *)
      Proof.
        Transparent File.recover.
        unfold oracle_refines_same_from_related_reboot, 
        ATCD_reboot_list; induction l_selector; simpl in *.
        { (* Finished *)
          intros.
          unfold File.recover in *; simpl in *.
          destruct l_o_imp; simpl in *; intuition.
          cleanup; try tauto.
          repeat split_ors; cleanup;
          simpl in *; try lia.
          specialize (H7 (ATCD_reboot_f (fun _ => 0))).
          specialize (H4 (ATCD_reboot_f (fun _ => 0))).
          cleanup.
          repeat invert_exec; simpl in *; cleanup.
          eapply HC_map_ext_eq in H8.
          eapply HC_map_ext_eq in H8.
          subst.

          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto;
          try congruence.
          apply HC_map_ext_eq in H7; subst.
          apply HC_map_ext_eq in H0; subst.
          rewrite <- H4 in *; clear H4; simpl in *; cleanup.
    
          repeat apply HC_map_ext_eq in H4; subst.
          specialize (H15 tt).
          specialize (H18 tt).
          specialize (H26 tt).
          specialize (H29 tt).
          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto;
          try congruence.

          apply HC_map_ext_eq in H11; subst.
          apply HC_map_ext_eq in H14; subst.
          specialize (H12 []).
          specialize (H15 []).
          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto;
          try congruence; repeat unify_execs; cleanup.
        }
        {(*Crashed*)
          intros.
          unfold TCD_reboot_list, File.recover in *; simpl in *.
          destruct l_o_imp; simpl in *; intuition.
          cleanup; try tauto.
          repeat split_ors; cleanup;
          simpl in *; try lia.
          {
            specialize (H7 (ATCD_reboot_f a)).
            specialize (H4 (ATCD_reboot_f a)).
            cleanup.
            repeat invert_exec; simpl in *; cleanup.
            eapply HC_map_ext_eq in H8.
            eapply HC_map_ext_eq in H8.
            subst.

            repeat split_ors; cleanup;
            repeat invert_exec; simpl in *; cleanup; eauto;
            try congruence.
            apply HC_map_ext_eq in H7; subst.
          apply HC_map_ext_eq in H0; subst.
          rewrite <- H4 in *; clear H4; simpl in *; cleanup.
    
          repeat apply HC_map_ext_eq in H4; subst.
            specialize (H15 tt).
            specialize (H18 tt).
            specialize (H26 tt).
            specialize (H29 tt).
            repeat split_ors; cleanup;
            repeat invert_exec; simpl in *; cleanup; eauto;
            try congruence.

            apply HC_map_ext_eq in H11; subst.
            apply HC_map_ext_eq in H14; subst.
            specialize (H12 []).
            specialize (H15 []).
            repeat split_ors; cleanup;
            repeat invert_exec; simpl in *; cleanup; eauto;
            try congruence; repeat unify_execs; cleanup.
          }
          {
            cleanup.
            repeat invert_exec; simpl in *; cleanup.
            repeat split_ors; cleanup; try congruence;
            repeat invert_exec; simpl in *; cleanup; eauto;
            try congruence.
            {
              specialize (H11 tt).
              specialize (H15 tt).
              cleanup.
              eapply IHl_selector in H5.
              3: apply H7.
              2:{
                unfold refines_related_reboot in *;
                cleanup.
                eexists (_, (_, _)), (_, (_, _)); split; eauto.
                2: split; eauto.
                {
                  simpl in *; unfold HC_refines_reboot in *;
                  simpl in *; cleanup; eauto.
                  simpl in *; unfold HC_refines_reboot in *;
                  simpl in *; cleanup; eauto.
                  intuition.
                  eapply refines_reboot_to_refines_reboot; eauto.
                }
                {
                  simpl in *; unfold HC_refines_reboot in *;
                  simpl in *; cleanup; eauto.
                  simpl in *; unfold HC_refines_reboot in *;
                  simpl in *; cleanup; eauto.
                  intuition.
                  eapply refines_reboot_to_refines_reboot; eauto.
                }
                shelve.
              }
              subst; eauto.
              simpl in *; cleanup; eauto.
            }
            {

            cleanup.
            repeat invert_exec; simpl in *; cleanup.
            simpl in *; cleanup.
            rewrite <- H2, <- H6 in *; clear H2 H6.
          subst.

          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto;
          try congruence.
            }
            {
              cleanup.
            repeat invert_exec; simpl in *; cleanup.
            simpl in *; cleanup.
            rewrite <- H8 in *; clear H8.
            simpl in *; cleanup.
            }
            {
              cleanup.
              repeat invert_exec; simpl in *; cleanup.
              simpl in *; cleanup.
              rewrite  <- H6 in *; clear H6.
              simpl in *; cleanup.
            }
            {
              cleanup.
            repeat invert_exec; simpl in *; cleanup.
            simpl in *; cleanup.
          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto;
          try congruence.
            
          apply HC_map_ext_eq in H8; subst.
          rewrite <- H3 in *; clear H3; 
          simpl in *; cleanup.
    
          repeat apply HC_map_ext_eq in H4; subst.
          repeat apply HC_map_ext_eq in H8; subst.
          repeat apply HC_map_ext_eq in H2; subst.
          specialize (H15 tt).
          specialize (H18 tt).
          specialize (H28 tt).
          specialize (H31 tt).
          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto;
          try congruence.

          apply HC_map_ext_eq in H8; subst.
          apply HC_map_ext_eq in H15; subst.
          specialize (H9 []).
          specialize (H16 []).
          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto;
          try congruence; repeat unify_execs; cleanup.
          
          eapply IHl_selector in H5.
          3: apply H7.
          2:{
            unfold refines_related_reboot in *;
            cleanup.
            eexists (_, (_, _)), (_, (_, _)); split; eauto.
            2: split; eauto.
            {
              simpl in *; unfold HC_refines_reboot in *;
              simpl in *; cleanup; eauto.
              simpl in *; unfold HC_refines_reboot in *;
              simpl in *; cleanup; eauto.
              intuition.
              unfold refines_reboot in *; cleanup.
              apply H9 in H12.
              split.
              repeat split_ors.
              eapply RepImplications.cached_log_reboot_rep_to_reboot_rep; eauto.
              eapply RepImplications.cached_log_crash_rep_during_recovery_to_reboot_rep; eauto.
              eapply RepImplications.cached_log_crash_rep_after_commit_to_reboot_rep; eauto.
              simpl; apply select_total_mem_synced.
            }
            {
              simpl in *; unfold HC_refines_reboot in *;
              simpl in *; cleanup; eauto.
              simpl in *; unfold HC_refines_reboot in *;
              simpl in *; cleanup; eauto.
              intuition.
              unfold refines_reboot in *; cleanup.
              apply H6 in H4.
              split.
              repeat split_ors.
              eapply RepImplications.cached_log_reboot_rep_to_reboot_rep; eauto.
              eapply RepImplications.cached_log_crash_rep_during_recovery_to_reboot_rep; eauto.
              eapply RepImplications.cached_log_crash_rep_after_commit_to_reboot_rep; eauto.
              simpl; apply select_total_mem_synced.
            }
            shelve.
          }
          subst; eauto.
        }
      }
    }
    Unshelve.
    all: try solve [exact (fun _ _ => True)].
    all: simpl; eauto.
Qed.


Lemma oracle_refines_independent_from_reboot_function:
      forall u (T : Type) (p : prog ATCLang T)
    s s' r o o_abs grs,
    LayerImplementation.exec' u o s (Simulation.Definitions.compile ATCD_Refinement p)
    (Finished s' r) ->
    oracle_refines _ _ ATCDLang ATCLang
    ATCD_CoreRefinement T u s p grs o o_abs ->
    forall grs',
    oracle_refines _ _ ATCDLang ATCLang
    ATCD_CoreRefinement T u s p grs' o o_abs.
    Proof.
      induction p; simpl; eauto.
      intros. 
      {
        destruct o; simpl in *; cleanup.
        {
          invert_exec'' H; repeat invert_exec;
          eexists; intuition eauto.
        }
        {
          eapply lift2_invert_exec in H; cleanup.
          apply HC_map_ext_eq in H; eauto; subst.
          specialize (H3 tt); simpl in *.
          destruct o; simpl in *.
          {
            cleanup; invert_exec'' H1; 
            repeat invert_exec;
            eexists; intuition eauto;
            do 2 eexists; intuition eauto;
            simpl; intuition eauto. 
            all: simpl; eauto.
          }
          {
            eapply lift2_invert_exec in H1; cleanup.
          apply HC_map_ext_eq in H; eauto; subst.
          specialize (H5 []); simpl in *.
          destruct o; simpl in *.
          {
            split_ors; cleanup; repeat unify_execs; cleanup.
            eexists; intuition eauto;
            do 2 eexists; intuition eauto;
            simpl; intuition eauto.
            do 2 eexists; intuition eauto.
          }
          {
            repeat split_ors; cleanup; repeat unify_execs; cleanup.
            eexists; intuition eauto;
            do 2 eexists; intuition eauto;
            simpl; intuition eauto.
            do 2 eexists; intuition eauto.
            edestruct H5; eauto.

            repeat split_ors; cleanup; repeat unify_execs; cleanup;
            left; eexists; intuition eauto;
            repeat split_ors; cleanup; repeat unify_execs; cleanup.
          }
          {
            repeat split_ors; cleanup; repeat unify_execs; cleanup.
            eexists; intuition eauto;
            do 2 eexists; intuition eauto;
            simpl; intuition eauto.
            do 2 eexists; intuition eauto.
          } 
          {
            repeat split_ors; cleanup; repeat unify_execs; cleanup.
            eexists; intuition eauto;
            do 2 eexists; intuition eauto;
            simpl; intuition eauto.
            do 2 eexists; intuition eauto.
          }
        }
      }
    }
    {
      intros.
      invert_exec'' H0.
      split_ors; cleanup.
      match goal with
      | [H: exec _ _ (?o ++ _) ?s ?p _,
        H0: LayerImplementation.exec' _ ?o ?s ?p _ |- _] =>
        exfalso; eapply finished_not_crashed_oracle_prefix in H; eauto;
        rewrite <- app_assoc; eauto
      end.
      match goal with
      | [H: exec _ _ _ ?s ?p (Finished _ _),
        H0: LayerImplementation.exec' _ _ ?s ?p (Finished _ _) |- _] =>
      eapply exec_finished_deterministic_prefix in H; try solve [apply H0];
      eauto; cleanup
      end.
      repeat match goal with
      | [H: exec _ _ ?o ?s ?p _,
        H0: LayerImplementation.exec' _ ?o ?s ?p _ |- _] =>
      eapply_fresh  exec_deterministic_wrt_oracle in H; try solve [apply H0];
      eauto; cleanup
      end.
    
      right.
      do 7 eexists; intuition eauto.
      Unshelve.
      all: eauto.
    }
Qed.
(*
    Lemma HC_oracle_refines_lift2:
    forall T (p: TD.(prog) T) o u s x,
    oracle_refines _ _ATCDLang ATCLang
    (HC_Core_Refinement ATCDLang ATCLang Definitions.TDCoreRefinement)
    T u s
    (lift_L2 AuthenticationOperation p)
    (fun
    s : HorizontalComposition.state' AuthenticationOperation
          TransactionCacheOperation => (fst s, ([], snd (snd s))))
    o
    (map
    (fun
        o : LayerImplementation.token'
              (TransactionalDiskLayer.TDCore data_length) =>
      match o with
      | OpToken _ o1 =>
          OpToken
            (HorizontalComposition AuthenticationOperation
              (TransactionalDiskLayer.TDCore data_length))
            (Token2 AuthenticationOperation
              (TransactionalDiskLayer.TDCore data_length) o1)
      | LayerImplementation.Crash _ =>
          LayerImplementation.Crash
            (HorizontalComposition AuthenticationOperation
              (TransactionalDiskLayer.TDCore data_length))
      | LayerImplementation.Cont _ =>
          LayerImplementation.Cont
            (HorizontalComposition AuthenticationOperation
              (TransactionalDiskLayer.TDCore data_length))
      end) x) ->
    
      ((RefinementLift.compile
    (HorizontalComposition AuthenticationOperation
        TransactionCacheOperation)
    (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TDCore data_length)) ATCDLang ATCLang
    (HC_Core_Refinement ATCDLang ATCLang Definitions.TDCoreRefinement) T
    (lift_L2 AuthenticationOperation p)) = 
    (lift_L2 AuthenticationOperation 
    (RefinementLift.compile TransactionCacheOperation
    (TransactionalDiskLayer.TDCore data_length) Definitions.imp TD
    Definitions.TDCoreRefinement T p))) ->
    
      exists o',
      oracle_refines _ _ Definitions.imp TD Definitions.TDCoreRefinement
      T u (snd s) p (fun s => ([], snd s)) o' x /\
      HC_oracle_transformation o o'.
      Proof.
        induction p; simpl; intuition eauto.
        {
          cleanup.
          specialize (H3 tt).
          eexists; intuition eauto.
          eexists; intuition eauto.
          destruct x; simpl in *; cleanup; try congruence.
          destruct x; simpl in *; cleanup; try congruence; eauto.
        }
        {
          cleanup.
        destruct x; simpl in *; cleanup; try congruence; eauto.
        destruct x; simpl in *; cleanup; try congruence; eauto.
        eexists; intuition eauto.
        left; eexists; intuition eauto.
        econstructor.
        invert_exec.
        eexists; intuition eauto.
        simpl; eauto.
        }
        {
          cleanup.
            destruct x; simpl in *; cleanup; try congruence; eauto.
            destruct x; simpl in *; cleanup; try congruence; eauto.
            eexists; intuition eauto.
            right; do 2 eexists; intuition eauto.
            econstructor.
            invert_exec.
            eexists; intuition eauto.
            simpl; eauto.
          }
          {
            cleanup.
            inversion H1; cleanup; eauto.
            edestruct IHp; eauto; cleanup.
            simpl in *.
            eexists; intuition eauto.
            eapply lift2_invert_exec_crashed in H0; cleanup.
            apply HC_map_ext_eq in H6; subst.
            left; eexists; intuition eauto.
          }
          {
            cleanup.
            inversion H1; cleanup; eauto.
            destruct (Compare_dec.le_dec (length x2) (length x)). 
            {
              rewrite <- firstn_skipn with (l:= x)(n:= length x2) in H2.
              rewrite map_app in H2.
              apply app_split_length_eq_l in H2; eauto; cleanup.
              eapply FunctionalExtensionality.equal_f with (x3:= x5) in H8; eauto.
            
              rewrite <- H0 in *.
              edestruct IHp; eauto; cleanup.
              edestruct H; eauto; cleanup.
    
              eapply lift2_invert_exec in H3; cleanup.
              apply HC_map_ext_eq in H2; subst.
              destruct x6.
              {
                eapply lift2_invert_exec in H4; cleanup.
                apply HC_map_ext_eq in H10; subst.
                eexists; intuition eauto.
                right; do 7 eexists; intuition eauto.
                rewrite firstn_skipn; eauto.
                apply HC_oracle_transformation_merge;
                eapply HC_oracle_transformation_same.
              }
              {
                eapply lift2_invert_exec_crashed in H4; cleanup.
                apply HC_map_ext_eq in H10; subst.
                eexists; intuition eauto.
                right; do 7 eexists; intuition eauto.
                rewrite firstn_skipn; eauto.
                apply HC_oracle_transformation_merge;
                eapply HC_oracle_transformation_same.
              }
              rewrite map_length, firstn_length_l; eauto.
            }
            {
              eapply f_equal in H2.
              rewrite map_length, app_length in H2; try lia.
            }
          }
      Qed.
*)
    

Definition LD_have_same_structure {T T'} (p1: LoggedDiskLayer.logged_disk_prog T) 
(p2: LoggedDiskLayer.logged_disk_prog T') :=
  match p1, p2 with
  | LoggedDiskLayer.Read _, LoggedDiskLayer.Read _ => True
  | LoggedDiskLayer.Write l1 l3, LoggedDiskLayer.Write l2 l4 => 
  length l1 = length l2 /\
  length l3 = length l4 /\
  (NoDup l1 <-> NoDup l2) /\ 
  (Forall (fun a : nat => a < data_length) l1 <->
    Forall (fun a : nat => a < data_length) l2)
  | LoggedDiskLayer.Recover, LoggedDiskLayer.Recover => True
  | LoggedDiskLayer.Init l1, LoggedDiskLayer.Init l2 => length l1 = length l2
  | _, _ => False
  end.

Definition TC_have_same_structure {T T'} (p1: TransactionCacheLayer.TransactionCacheOperation.(operation) T) 
  (p2: TransactionCacheLayer.TransactionCacheOperation.(operation) T') :=
    match p1, p2 with
    | P1 p1 , P1 p2 =>
      match p1, p2 with  
      | ListLayer.Get _, ListLayer.Get _ => True
      | ListLayer.Put a1, ListLayer.Put a2 => True
      | ListLayer.Delete _, ListLayer.Delete _ => True
      | _, _ => False
      end
    | P2 p1, P2 p2 =>
      LD_have_same_structure p1 p2
    | _, _ => False
    end.

Fixpoint ATC_have_same_structure {T T'} (p1: ATCLang.(prog) T) (p2: ATCLang.(prog) T') u s1 s2 :=
  match p1, p2 with
  | Op _ o1, Op _ o2 =>
    match o1, o2 with
    | P1 _, P1 _ => True (*It can only be auth*)
    | P2 t1, P2 t2 =>
      TC_have_same_structure t1 t2
    | _, _ => False
    end
  | Ret _, Ret _ => True
  | @Bind _ T1_1 T1_2 p1_1 p1_2, @Bind _ T2_1 T2_2 p2_1 p2_2 =>
    T1_1 = T2_1 /\
    T1_2 = T2_2 /\
    ATC_have_same_structure p1_1 p2_1 u s1 s2 /\
    (forall s1' r1 s2' r2 o,
        exec ATCLang u o s1 p1_1 (Finished s1' r1) ->
        exec ATCLang u o s2 p2_1 (Finished s2' r2) ->
    ATC_have_same_structure (p1_2 r1) (p2_2 r2) u s1' s2')
  | _, _ => False
  end.

Lemma LD_oracle_refines_operation_eq:
forall (u0 : user) (T : Type) (o1 : operation (LoggedDiskOperation log_length data_length) T)
(T' : Type) (o2 : operation (LoggedDiskOperation log_length data_length) T')
x16 x17 x18 x19 x20 x21 x22 x23 s0 s3 s1' s2'
(r1 : T) (r2 : T'),
token_refines T u0 s0 o1 x22 x21
x17 ->
token_refines T' u0 s3 o2 x19 x18
x23 ->
exec (CachedDiskLang) u0 x21 s0
(LoggedDiskCoreRefinement.(Simulation.Definitions.compile_core) o1) 
(Finished s1' r1) ->
exec (CachedDiskLang) u0 x18 s3
(LoggedDiskCoreRefinement.(Simulation.Definitions.compile_core) o2)
(Finished s2' r2) ->
LD_have_same_structure o1 o2 -> 

(exists s1a,refines s0 s1a) ->
(exists s2a, refines s3 s2a) ->

x18 ++ x16 = x21 ++ x20 -> x18 = x21 /\ x17 = x23.
Proof.
intros;
destruct o1, o2; simpl in *; cleanup; try tauto.
{
  repeat split_ors; cleanup; repeat unify_execs_prefix; cleanup;
  repeat unify_execs; cleanup.
  eapply LogCache_FinishedNotCrashed.read_finished_oracle_eq in H1; eauto.
}
{
  unfold refines, LogCache.cached_log_rep, Log.log_rep, Log.log_header_rep in *.
  cleanup.
  edestruct H; eauto;
  edestruct H0; eauto;
  repeat (split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup);
  eapply_fresh write_finished_oracle_eq in H1; try eapply H2; 
  eauto; cleanup; eauto;
  repeat (split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup); eauto.
  all: intuition eauto.
}
{
  unfold refines, LogCache.cached_log_rep, Log.log_rep, Log.log_header_rep,
  Log.log_rep_general in *.
  cleanup.
  repeat (split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup).
  eapply recover_finished_oracle_eq in H1; eauto.
  do 2 eexists; split; intuition eauto; try congruence.
  do 2 eexists; split; intuition eauto; try congruence.
}
{
  repeat (split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup).
  eapply init_finished_oracle_eq in H1; eauto.
}
Unshelve.
all: eauto.
Qed.

Lemma TC_oracle_refines_operation_eq:
forall (u0 : user) (T : Type) (o1 : operation TransactionCacheOperation T)
(T' : Type) (o2 : operation TransactionCacheOperation T')
x16 x17 x18 x19 x20 x21 x22 x23 s0 s3 s1' s2'
(r1 : T) (r2 : T'),
TCD_CoreRefinement.(Simulation.Definitions.token_refines) u0 s0 o1 x22 x21
x17 ->
TCD_CoreRefinement.(Simulation.Definitions.token_refines) u0 s3 o2 x19 x18
x23 ->
exec (TCDLang) u0 x21 s0
(TCD_CoreRefinement.(Simulation.Definitions.compile_core) o1) 
(Finished s1' r1) ->
exec (TCDLang) u0 x18 s3
(TCD_CoreRefinement.(Simulation.Definitions.compile_core) o2)
(Finished s2' r2) ->
TC_have_same_structure o1 o2 -> 
(exists s1a,refines (snd s0) s1a) ->
(exists s2a, refines (snd s3) s2a) ->
x18 ++ x16 = x21 ++ x20 -> x18 = x21 /\ x17 = x23.
Proof.
intros;
destruct o1, o2; simpl in *; cleanup; try tauto;
repeat invert_exec; cleanup; eauto.
eapply HC_map_ext_eq in H;
eapply HC_map_ext_eq in H1; cleanup.
apply HC_map_ext_eq_prefix in H6; eauto; cleanup.
eapply LD_oracle_refines_operation_eq in H; eauto.
cleanup; eauto.
Unshelve.
all: exact [].
Qed.


Lemma write_crashed_oracle_length_eq_prefix:
    forall l l1 l0 l2 u o1 o2 o3 o4 s1 s2 s3 s4,
      (exists txns, Log.log_rep txns (snd s1)) ->
      (exists txns, Log.log_rep txns (snd s2)) ->
      (NoDup l1 <-> NoDup l) ->
  (Forall (fun a : nat => a < data_length) l1 <->
  Forall (fun a : nat => a < data_length) l) ->
        exec CachedDiskLang u o1 s1 (LogCache.write l1 l2) (Crashed s3) ->
        exec CachedDiskLang u o2 s2 (LogCache.write l l0) (Crashed s4) -> 
        length l1 = length l ->
        o1 ++ o3 = o2 ++ o4 ->
        length o1 = length o2.
  Proof.
    unfold Log.log_rep; intros; cleanup.
    eapply write_crashed_oracle_eq in H5.
    6: eauto.
    6: eauto.
    all: subst; eauto.
    Qed.



Set Nested Proofs Allowed.
  Lemma le_lt_exfalso:
  forall c n m,
    n < m ->
    c < n ->
    ~ c >= m.
    unfold not; intros. lia.
  Qed.

Lemma lt_lt_exfalso:
forall a b c n m,
n < m ->
a < b ->
c * n + a < c * m + b.
intros; destruct c; eauto.
nia.
Qed.

Lemma lt_weaken:
forall a n m,
n < m ->
n < a + m.
intros; lia.
Qed.


Lemma recs_eqv_fold_left_add:
  forall recs1 recs2 n,
  Forall2 (fun rec1 rec2 => Log.addr_count rec1 = Log.addr_count rec2) recs1 recs2 -> 
Forall2 (fun rec1 rec2 => Log.data_count rec1 = Log.data_count rec2) recs1 recs2 -> 
  fold_left Nat.add (map
    (fun txnr : Log.txn_record =>
      Log.addr_count txnr * 2 +
      Log.data_count txnr * 4 + 3)
    recs1) n = 
  fold_left Nat.add (map
    (fun txnr : Log.txn_record =>
      Log.addr_count txnr * 2 +
      Log.data_count txnr * 4 + 3)
    recs2) n.
  Proof.
    induction recs1; destruct recs2; simpl in *; intros;
    try inversion H; try inversion H0; cleanup; eauto.
  Qed.

Lemma encode_header_extensional:
forall hdr1 hdr2,
Log.encode_header hdr1 = Log.encode_header hdr2 ->
hdr1 = hdr2.
Proof.
  intros.
  assert (Log.decode_header (Log.encode_header hdr1) = Log.decode_header (Log.encode_header hdr2)). {
    rewrite H; eauto.
  }
  repeat rewrite Log.encode_decode_header in *; eauto.
Qed.

Definition no_accidental_overlap (selector: @total_mem addr addr_dec nat) 
(s: @total_mem addr addr_dec (value * list value)) :=
  forall i, 
  i < log_length ->   
  length (snd (s (log_start + i))) = 1 ->
  selector (log_start + i) = 1 ->
  fst (s (log_start + i)) <> hd value0 (snd (s (log_start + i))).

Lemma LD_oracle_refines_operation_eq_crashed:
forall (u0 : user) (T : Type) (o1 : operation (LoggedDiskOperation log_length data_length) T)
(T' : Type) (o2 : operation (LoggedDiskOperation log_length data_length) T')
x16 x17 x18 x20 x21 x23 s0 s3 s1' s2' hdr1 hdr2 selector merged_disk1 merged_disk2,
token_refines T u0 s0 o1 (fun s => (empty_mem, (fst (snd s), select_total_mem selector (snd (snd s))))) x21
x17 ->
token_refines T' u0 s3 o2 (fun s => (empty_mem, (fst (snd s), select_total_mem selector (snd (snd s))))) x18
x23 ->
exec (CachedDiskLang) u0 x21 s0
(LoggedDiskCoreRefinement.(Simulation.Definitions.compile_core) o1) 
(Crashed s1') ->
exec (CachedDiskLang) u0 x18 s3
(LoggedDiskCoreRefinement.(Simulation.Definitions.compile_core) o2)
(Crashed s2') ->
LD_have_same_structure o1 o2 -> 
(exists txns1,
    fst s0 = Mem.list_upd_batch empty_mem (map Log.addr_list txns1) (map Log.data_blocks txns1) /\
    Log.log_header_rep hdr1 txns1 (snd s0) /\
    merged_disk1 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd s0)) (map Log.addr_list txns1) (map Log.data_blocks txns1))) /\
    (forall a, a >= data_start -> snd ((snd (snd s0)) a) = [])) ->
(exists txns2, 
    fst s3 = Mem.list_upd_batch empty_mem (map Log.addr_list txns2) (map Log.data_blocks txns2) /\
    Log.log_header_rep hdr2 txns2 (snd s3) /\
    merged_disk2 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd s3)) (map Log.addr_list txns2) (map Log.data_blocks txns2))) /\
    (forall a, a >= data_start -> snd ((snd (snd s3)) a) = [])) ->

Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
Forall2 (fun rec1 rec2 => Log.addr_count rec1 = Log.addr_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
Forall2 (fun rec1 rec2 => Log.data_count rec1 = Log.data_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 

no_accidental_overlap selector (snd (snd s1')) ->
no_accidental_overlap selector (snd (snd s2')) ->
x18 ++ x16 = x21 ++ x20 -> 
x17 = x23.
Proof.
intros;
destruct o1, o2; simpl in *; try tauto.
{
  repeat split_ors; cleanup; repeat unify_execs_prefix; cleanup;
  repeat unify_execs; cleanup; eauto.
}
{
  intros.
  eapply_fresh write_crashed_oracle_length_eq_prefix in H1; eauto.
  setoid_rewrite Hx in H0.
  clear Hx.
  setoid_rewrite app_length in H.
  setoid_rewrite app_length in H0.
  destruct H3.
  setoid_rewrite H3 in H.
  setoid_rewrite addr_list_to_blocks_length_eq in H;
  try solve [do 2 rewrite map_length with (f:= (Nat.add data_start)); apply H3].
  repeat match goal with
  |[H: exists _, _ |- _] => destruct H
  end.
  specialize H with (1:= H4).
  specialize H0 with (1:= H5).
  eapply recs_eqv_fold_left_add with (n:= 0) in H7; eauto.
  setoid_rewrite H7 in H.
  setoid_rewrite H6 in H. 
  (* clear H6 H7. *)
  remember (fold_left Nat.add
  (map
     (fun txnr : Log.txn_record =>
      Log.addr_count txnr * 2 + Log.data_count txnr * 4 + 3)
     (Log.records (Log.current_part hdr2))) 0) as c2.
  (* clear Heqc2. *)
  
  remember (length (addr_list_to_blocks (map (Nat.add data_start) l1))) as c1.
  setoid_rewrite <- Heqc1 in H.
  (* clear Heqc1. *)

  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia. 
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  {
    unfold select_total_mem, select_for_addr in *; simpl in *.
    do 2 cleanup;
    match goal with
    | [H: Log.encode_header _ = Log.encode_header _ |- _] =>
    apply encode_header_extensional in H; congruence
    end.
  }
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  {
    unfold select_total_mem, select_for_addr in *; simpl in *.
    do 2 cleanup;
    match goal with
    | [H: Log.encode_header _ = Log.encode_header _ |- _] =>
    apply encode_header_extensional in H; congruence
    end.
  }
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  {
     assert (selector (log_start + Log.count (Log.current_part hdr2) + x5) = 1). {
      unfold select_total_mem, select_for_addr in H32; simpl in *.
      edestruct H34; eauto.
      cleanup; eauto.
      
      exfalso; apply H32; eauto.

      destruct_fresh (snd (snd (snd s1') (log_start + Log.count (Log.current_part hdr2) + x5)));
      try setoid_rewrite D0 in H33; simpl in *; try lia.
      destruct l3; simpl in *; try lia.
      rewrite D0 in H32; simpl in *.
      destruct n; simpl in *; eauto.

      exfalso; apply H32; eauto.
    }

    edestruct H47; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
    repeat rewrite map_length; eauto.

    rewrite <- PeanoNat.Nat.add_assoc in H32.
    exfalso; eapply H10; eauto.
    eapply PeanoNat.Nat.lt_le_trans.
    2: apply H44.
    rewrite <- PeanoNat.Nat.add_assoc.
    apply Plus.plus_lt_compat_l.
    erewrite addr_list_to_blocks_length_eq; eauto.
    repeat rewrite map_length; eauto.
    eauto.

    setoid_rewrite PeanoNat.Nat.add_assoc.
    eauto.
    destruct_fresh (snd
    (snd (snd x6)
       (log_start + Log.count (Log.current_part hdr2) +
        x5))); 
    setoid_rewrite D in H48;
    simpl in *; try lia.
    destruct l3; simpl in *; try lia.
    setoid_rewrite D; simpl.
    setoid_rewrite H33.
    rewrite <- H46; eauto.
    unfold select_total_mem, select_for_addr; simpl in *.
    repeat rewrite <- PeanoNat.Nat.add_assoc.
    rewrite PeanoNat.Nat.add_assoc.
    rewrite H14.
    setoid_rewrite D.
    simpl; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
    repeat rewrite map_length; eauto.
  }
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  {
     assert (selector (log_start + x5) = 1). {
      unfold select_total_mem, select_for_addr in H32; simpl in *.
      edestruct H34; eauto.
      cleanup; eauto.
      
      exfalso; apply H32; eauto.

      destruct_fresh (snd (snd (snd s1') (log_start + x5)));
      setoid_rewrite D0 in H33; simpl in *; try lia.
      destruct l3; simpl in *; try lia.
      rewrite D0 in H32; simpl in *.
      destruct n; simpl in *; eauto.
      exfalso; apply H32; eauto.
    }

    edestruct H47; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
    repeat rewrite map_length; eauto.

    exfalso; eapply H10; eauto.
    eapply PeanoNat.Nat.lt_le_trans; eauto.
    destruct_fresh (snd
    (snd (snd x6)
       (log_start + x5))); 
    setoid_rewrite D in H48;
    simpl in *; try lia.
    destruct l3; simpl in *; try lia.
    setoid_rewrite D; simpl.
    setoid_rewrite H33.
    rewrite <- H46; eauto.
    unfold select_total_mem, select_for_addr; simpl in *.
    rewrite H14.
    setoid_rewrite D.
    simpl; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
    repeat rewrite map_length; eauto.
  }
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  {
    unfold select_total_mem, select_for_addr in *; simpl in *.
    do 2 cleanup;
    match goal with
    | [H: Log.encode_header _ = Log.encode_header _ |- _] =>
    apply encode_header_extensional in H; congruence
    end.
  }
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  {
     assert (selector (log_start + Log.count (Log.current_part hdr2) + x10) = 1). {
      unfold select_total_mem, select_for_addr in H46; simpl in *.
      edestruct H47; eauto.
      cleanup; eauto.
      
      exfalso; apply H46; eauto.

      destruct_fresh (snd (snd (snd x5) (log_start + Log.count (Log.current_part hdr2) + x10)));
      try setoid_rewrite D0 in H33; simpl in *; try lia.
      destruct l3; simpl in *; try lia.
      rewrite D0 in H46; simpl in *.
      destruct n; simpl in *; eauto.

      exfalso; apply H46; eauto.
    }

    edestruct H34; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
    repeat rewrite map_length; eauto.

    rewrite <- PeanoNat.Nat.add_assoc in H33.
    exfalso; eapply H9; eauto.
    eapply PeanoNat.Nat.lt_le_trans.
    2: apply H44.
    rewrite <- PeanoNat.Nat.add_assoc.
    apply Plus.plus_lt_compat_l.
    erewrite addr_list_to_blocks_length_eq; eauto.
    repeat rewrite map_length; eauto.
    eauto.

    setoid_rewrite PeanoNat.Nat.add_assoc.
    eauto.
    destruct_fresh (snd
    (snd (snd s1')
       (log_start + Log.count (Log.current_part hdr2) +
        x10))); 
    setoid_rewrite D in H48;
    simpl in *; try lia.
    destruct l3; simpl in *; try lia.
    setoid_rewrite D; simpl.
    setoid_rewrite H33.
    rewrite <- H32; eauto.
    unfold select_total_mem, select_for_addr; simpl in *.
    repeat rewrite <- PeanoNat.Nat.add_assoc.
    rewrite PeanoNat.Nat.add_assoc.
    rewrite H14.
    setoid_rewrite D.
    simpl; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
    repeat rewrite map_length; eauto.
  }
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  {
    unfold select_total_mem, select_for_addr in *; simpl in *.
    do 2 cleanup;
    match goal with
    | [H: Log.encode_header _ = Log.encode_header _ |- _] =>
    apply encode_header_extensional in H; congruence
    end.
  }
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia.
  {
    assert (selector (log_start + x10) = 1). {
      unfold select_total_mem, select_for_addr in H46; simpl in *.
      edestruct H47; eauto.
      cleanup; eauto.
      
      exfalso; apply H46; eauto.

      destruct_fresh (snd (snd (snd x5) (log_start + x10)));
      setoid_rewrite D0 in H33; simpl in *; try lia.
      destruct l3; simpl in *; try lia.
      rewrite D0 in H46; simpl in *.
      destruct n; simpl in *; eauto.
      exfalso; apply H46; eauto.
    }

    edestruct H34; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
    repeat rewrite map_length; eauto.

    exfalso; eapply H9; eauto.
    eapply PeanoNat.Nat.lt_le_trans; eauto.
    destruct_fresh (snd
    (snd (snd s1')
       (log_start + x10))); 
    setoid_rewrite D in H48;
    simpl in *; try lia.
    destruct l3; simpl in *; try lia.
    setoid_rewrite D; simpl.
    setoid_rewrite H33.
    rewrite <- H32; eauto.
    unfold select_total_mem, select_for_addr; simpl in *.
    rewrite H14.
    setoid_rewrite D.
    simpl; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
    repeat rewrite map_length; eauto.
  }
  unfold Log.log_rep; cleanup; eexists; eauto.
  unfold Log.log_rep; cleanup; eexists; eauto.
  cleanup; intuition eauto.
  cleanup; intuition eauto.
  cleanup; intuition eauto.
}
{
  repeat (split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto).
}
{
  repeat (split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto).
}
Unshelve.
all: eauto.
Qed.

Lemma TC_oracle_refines_operation_eq_crashed:
forall (u0 : user) (T : Type) (o1 : operation TransactionCacheOperation T)
(T' : Type) (o2 : operation TransactionCacheOperation T')
x16 x17 x18 x20 x21 x23 s0 s3 s1' s2' hdr1 hdr2 selector merged_disk1 merged_disk2,
TCD_CoreRefinement.(Simulation.Definitions.token_refines) u0 s0 o1 
(fun s => ([], (empty_mem, (fst (snd (snd s)), select_total_mem selector (snd (snd (snd s))))))) x21
x17 ->
TCD_CoreRefinement.(Simulation.Definitions.token_refines) u0 s3 o2 
(fun s => ([], (empty_mem, (fst (snd (snd s)), select_total_mem selector (snd (snd (snd s))))))) x18
x23 ->
exec (TCDLang) u0 x21 s0
(TCD_CoreRefinement.(Simulation.Definitions.compile_core) o1) 
(Crashed s1') ->
exec (TCDLang) u0 x18 s3
(TCD_CoreRefinement.(Simulation.Definitions.compile_core) o2)
(Crashed s2') ->
TC_have_same_structure o1 o2 -> 
(exists txns1,
    fst (snd s0) = Mem.list_upd_batch empty_mem (map Log.addr_list txns1) (map Log.data_blocks txns1) /\
    Log.log_header_rep hdr1 txns1 (snd (snd s0)) /\
    merged_disk1 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd (snd s0))) (map Log.addr_list txns1) (map Log.data_blocks txns1))) /\
    (forall a, a >= data_start -> snd ((snd (snd (snd s0))) a) = [])) ->
(exists txns2, 
    fst (snd s3) = Mem.list_upd_batch empty_mem (map Log.addr_list txns2) (map Log.data_blocks txns2) /\
    Log.log_header_rep hdr2 txns2 (snd (snd s3)) /\
    merged_disk2 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd (snd s3))) (map Log.addr_list txns2) (map Log.data_blocks txns2))) /\
    (forall a, a >= data_start -> snd ((snd(snd (snd s3))) a) = [])) ->
Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
Forall2 (fun rec1 rec2 => Log.addr_count rec1 = Log.addr_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
Forall2 (fun rec1 rec2 => Log.data_count rec1 = Log.data_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
no_accidental_overlap selector (snd (snd (snd s1'))) ->
no_accidental_overlap selector (snd (snd (snd s2'))) ->
x18 ++ x16 = x21 ++ x20 -> x17 = x23.
Proof.
intros;
destruct o1, o2; simpl in *; cleanup; try tauto;
repeat invert_exec; cleanup; eauto.
eapply HC_map_ext_eq in H;
eapply HC_map_ext_eq in H1; cleanup.
apply HC_map_ext_eq_prefix in H11; eauto; cleanup.
specialize (H19 []).
specialize (H21 []).
eapply LD_oracle_refines_operation_eq_crashed in H; eauto.
cleanup; eauto.
Unshelve.
all: exact [].
Qed.

Lemma ATCD_oracle_refines_impl_eq:
forall u T p1 T' p2 s1 s2 s1' s2' s1a s2a r1 r2 o1 o2 o3 o4 oa1 oa2 selector, (* oa3 oa4, *)
oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement
  T u s1 p1 (ATCD_reboot_f selector) o1 oa1 ->
oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement
  T' u s2 p2 (ATCD_reboot_f selector) o2 oa2 ->

@HC_refines _ _ _ _ _ ATCLang TCD_CoreRefinement s1 s1a ->
@HC_refines _ _ _ _ _ ATCLang TCD_CoreRefinement s2 s2a ->

  exec ATCDLang u o1 s1 (ATCD_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
  exec ATCDLang u o2 s2 (ATCD_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
  ATC_have_same_structure p1 p2 u s1a s2a ->

  (forall u T (o1: operation TransactionCacheOperation T) T' (o2 : operation TransactionCacheOperation T') x x0 x1 x2 x3 x4 x5 x6 s1 s2 s1' s2' r1 r2,
  TCD_CoreRefinement.(Simulation.Definitions.token_refines) u s1 o1 x5 x4 x0 ->
  TCD_CoreRefinement.(Simulation.Definitions.token_refines) u s2 o2 x2 x1 x6 ->
  exec TCDLang u x4 s1
  (TCD_CoreRefinement.(Simulation.Definitions.compile_core) o1)
  (Finished s1' r1) ->
  exec TCDLang u x1 s2
  (TCD_CoreRefinement.(Simulation.Definitions.compile_core) o2)
  (Finished s2' r2) ->
  TC_have_same_structure o1 o2 ->

(exists s1a,refines (snd s1) s1a) ->
(exists s2a, refines (snd s2) s2a) ->
  x1 ++ x = x4 ++ x3 ->
  x1 = x4 /\ x0 = x6) ->

o1 ++ o3 = o2 ++ o4 ->
not_init p1 /\ not_init p2 ->
o1 = o2 /\ oa1 = oa2.
Proof.
  induction p1; destruct p2; simpl; intros; try tauto; 
  cleanup_no_match; try tauto.
  {
    clear H8 H9.
    cleanup; try tauto;
    unfold HC_token_refines in *; cleanup;
    simpl in *; cleanup; eauto.

    specialize (H9 tt).
    specialize (H11 tt).
    eapply_fresh HC_map_ext_eq_prefix in H7; eauto; cleanup_no_match.
    eapply lift2_invert_exec in H3; cleanup.
    eapply lift2_invert_exec in H4; cleanup.
    eapply_fresh HC_map_ext_eq in H4; eauto; subst.
    eapply_fresh HC_map_ext_eq in H0; eauto; subst.

    assert (x6 = x5 /\ x3 = x1). {
      unfold HC_refines in *; cleanup; simpl in *; eauto.
      unfold HC_refines in *; cleanup; simpl in *; eauto.
    }
    cleanup; eauto.
  }
  {
    repeat invert_exec; eauto.
    repeat split_ors; cleanup; 
    simpl in *; cleanup; 
    try congruence; eauto.
    repeat invert_exec.
    repeat invert_exec.
  }
  {
    repeat invert_exec.
    repeat rewrite <- app_assoc in *.
    repeat split_ors; cleanup; repeat unify_execs_prefix;
    cleanup; repeat unify_execs; cleanup.
    exfalso; eapply finished_not_crashed_oracle_prefix; 
    [eauto | | eauto];
    rewrite <- app_assoc; eauto.

    exfalso; eapply finished_not_crashed_oracle_prefix; 
    [eauto | | eauto];
    rewrite <- app_assoc; eauto.

    exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto;
    rewrite <- app_assoc; eauto.

    eapply_fresh exec_finished_deterministic_prefix in H17; eauto; cleanup.
    eapply_fresh exec_finished_deterministic_prefix in H22; eauto; cleanup.
    repeat unify_execs; cleanup.
    
    repeat rewrite <- app_assoc in *.
    
    eapply_fresh ATCD_exec_lift_finished in H17; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply_fresh ATCD_exec_lift_finished in H22; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    simpl in *; cleanup.

    eapply_fresh IHp1 in H8; eauto; subst; cleanup.

    eapply H in H6; eauto.
    cleanup; eauto.
  }
Unshelve.
all: eauto.
Qed.

Lemma ATCD_oracle_refines_prefix_one_crashed:
forall u T (p1 : ATCLang.(prog) T) T' (p2 : ATCLang.(prog) T') o1 o2 o3 o4 s1 s2 s1' s2' r1 s1a s2a oa1 oa2 selector,
oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement
  T u s1 p1 (ATCD_reboot_f selector) o1 oa1 ->
oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement
  T' u s2 p2 (ATCD_reboot_f selector) o2 oa2 ->


exec ATCDLang u o1 s1 (ATCD_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
exec ATCDLang u o2 s2 (ATCD_Refinement.(Simulation.Definitions.compile) p2) (Crashed s2') ->


@HC_refines _ _ _ _ _ ATCLang TCD_CoreRefinement s1 s1a ->
@HC_refines _ _ _ _ _ ATCLang TCD_CoreRefinement s2 s2a ->

ATC_have_same_structure p1 p2 u s1a s2a ->
not_init p1 ->
not_init p2 ->
o1 ++ o3 = o2 ++ o4 ->
False.
Proof.
  induction p1; simpl; intros. 
  {
    repeat (simpl in *; cleanup; try tauto; eauto);
    repeat invert_exec; simpl in *; cleanup; try congruence.
    
    (*
    eapply lift2_invert_exec in H1; cleanup.
    eapply lift2_invert_exec_crashed in H2; cleanup.
    *)
    rewrite <- H, <- H0 in *; clear H H0; 
    simpl in *; cleanup.
    rewrite <- H, <- H0 in *; clear H H0; 
    simpl in *; cleanup.
    rewrite <- H, <- H0 in *; clear H H0; 
    simpl in *; cleanup.

    repeat eapply HC_map_ext_eq in H2.
    repeat eapply HC_map_ext_eq in H.
    subst.
    specialize (H11 tt).
    specialize (H13 tt).
    cleanup; try congruence.
    repeat eapply HC_map_ext_eq in H2.
    repeat eapply HC_map_ext_eq in H13.
    subst.

    eapply HC_map_ext_eq_prefix in H8; cleanup.
    eapply HC_map_ext_eq_prefix in H; cleanup.
    specialize (H11 []).
    specialize (H14 []).
    destruct o, o5; cleanup; simpl in *; 
    try tauto; 
    repeat split_ors; cleanup; 
    repeat unify_execs; cleanup; 
    try congruence.

    eapply read_finished_not_crashed; eauto.
    unfold HC_refines in *; simpl in *; logic_clean.
    unfold HC_refines in *; simpl in *; logic_clean.
    unfold refines, LogCache.cached_log_rep in *; simpl in *; logic_clean.
    eapply write_finished_not_crashed; eauto.
    unfold HC_refines in *; simpl in *; logic_clean.
    unfold HC_refines in *; simpl in *; logic_clean.
    unfold refines, LogCache.cached_log_rep,
    Log.log_rep, Log.log_rep_general in *; simpl in *; logic_clean.
    eapply recover_finished_not_crashed; eauto.
    unfold Log.log_reboot_rep_explicit_part; do 2 eexists;
    intuition eauto; try congruence.
    unfold Log.log_reboot_rep_explicit_part; do 2 eexists;
    intuition eauto; try congruence.
    eapply H6; eauto.
  }
  {
    repeat (simpl in *; cleanup; try tauto; eauto).
    repeat split_ors; cleanup; eauto;
    simpl in *; cleanup; eauto;
    repeat invert_exec; simpl in *; cleanup.
  }
  {
    repeat (simpl in *; cleanup; try tauto; eauto).
    repeat invert_exec.
    repeat rewrite <- app_assoc in *.
    repeat split_ors; cleanup; eauto;
    repeat rewrite <- app_assoc in *; eauto;

    try solve [exfalso; eapply finished_not_crashed_oracle_prefix; 
    [eauto | | eauto];
    rewrite <- app_assoc; eauto].
    {
      eapply_fresh exec_finished_deterministic_prefix in H16; eauto; cleanup.
      repeat unify_execs; cleanup.
      repeat rewrite <- app_assoc in *; eauto.
    }
    {
      exfalso; eapply finished_not_crashed_oracle_prefix in H3; eauto. 
      rewrite <- app_assoc; eauto.
    }
    {
      exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto. 
      rewrite <- app_assoc; eauto.
    }
    {
      eapply exec_finished_deterministic_prefix in H17; eauto; cleanup.
      eapply exec_finished_deterministic_prefix in H22; eauto; cleanup.
      repeat unify_execs; cleanup.


      eapply_fresh exec_compiled_preserves_refinement_finished in H2; eauto; 
      cleanup; simpl in *.
      eapply_fresh exec_compiled_preserves_refinement_finished in H14; eauto; 
      cleanup; simpl in *.
      eapply_fresh ATCD_exec_lift_finished in H2; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      eapply_fresh ATCD_exec_lift_finished in H14; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      simpl in *; cleanup.

      eapply_fresh ATCD_oracle_refines_impl_eq in H19. 
      7: eauto.
      all: eauto.
      2: apply TC_oracle_refines_operation_eq.
      cleanup.
      

      eapply H.
      7: eauto.
      all: eauto.
    }
  }
  Unshelve.
  all: eauto.
Qed.


Lemma ATCD_ORS_equiv_impl:
forall u T (p1 p2: ATCLang.(prog) T) rec l_grs (EQ1 EQ2: state ATCLang -> state ATCLang -> Prop),
oracle_refines_same_from_related ATCD_Refinement u
p1 p2 rec l_grs EQ2 ->
(forall s1 s2, EQ1 s1 s2 -> EQ2 s1 s2) ->
oracle_refines_same_from_related ATCD_Refinement u
p1 p2 rec l_grs EQ1.
Proof.
  unfold oracle_refines_same_from_related; intros.
  eapply H; eauto.
  unfold refines_related in *; cleanup; eauto.
  do 2 eexists; intuition eauto.
Qed.

Lemma ATC_have_same_structure_sym:
forall T1 (p1 : ATCLang.(prog) T1) 
T2 (p2 : ATCLang.(prog) T2) u s1 s2,
ATC_have_same_structure p1 p2 u s1 s2 ->
ATC_have_same_structure p2 p1 u s2 s1.
Proof.
induction p1; destruct p2; 
simpl; intros; 
simpl in *; cleanup; eauto.

destruct o1, o2;
simpl in *; cleanup; eauto.

destruct o, o0;
simpl in *; cleanup; eauto.

intuition eauto.
intuition eauto.
Qed.


Lemma equivalence_preserved:
forall u T (p1 p2: prog ATCLang T) o s1 s2 s1a s2a 
hdr1 hdr2 txns1 txns2 s1' s2' r1 r2 selector oa,
Log.log_header_rep hdr1 txns1 (snd (snd (snd s1))) ->
Log.log_header_rep hdr2 txns2 (snd (snd (snd s2))) ->

@HC_refines _ _ _ _ ATCDLang ATCLang TCD_CoreRefinement s1 s1a ->
@HC_refines _ _ _ _ ATCDLang ATCLang TCD_CoreRefinement s2 s2a ->

exec ATCDLang u o s1 (ATCD_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
exec ATCDLang u o s2 (ATCD_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
ATC_have_same_structure p1 p2 u s1a s2a ->
Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2)  ->
Forall2 (fun rec1 rec2 => Log.addr_count rec1 = Log.addr_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) ->
Forall2 (fun rec1 rec2 => Log.data_count rec1 = Log.data_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) ->

not_init p1 ->
not_init p2 ->

oracle_refines ATCDCore ATCCore ATCDLang ATCLang ATCD_CoreRefinement T
    u s1 p1 (ATCD_reboot_f selector) o oa ->
oracle_refines ATCDCore ATCCore ATCDLang ATCLang ATCD_CoreRefinement T
    u s2 p2 (ATCD_reboot_f selector) o oa ->

exists hdr1' hdr2' txns1' txns2',
Log.log_header_rep hdr1' txns1' (snd (snd (snd s1'))) /\
Log.log_header_rep hdr2' txns2' (snd (snd (snd s2'))) /\
Log.count (Log.current_part hdr1') = Log.count (Log.current_part hdr2') /\
Forall2 (fun rec1 rec2 => Log.addr_count rec1 = Log.addr_count rec2) (Log.records (Log.current_part hdr1')) (Log.records (Log.current_part hdr2')) /\
Forall2 (fun rec1 rec2 => Log.data_count rec1 = Log.data_count rec2) (Log.records (Log.current_part hdr1')) (Log.records (Log.current_part hdr2')).
Proof.
  induction p1; destruct p2; simpl in *; intros;
  cleanup; try tauto.
  {
    destruct o2, o3; simpl in *.
    repeat invert_exec; simpl in *; cleanup; 
    do 4 eexists; intuition eauto.
  }
  {
    destruct o3, o5; simpl in *; cleanup; try tauto;
    repeat invert_exec; simpl in *; cleanup; 
    do 4 eexists; intuition eauto.
  }
  {
    destruct o3, o5; simpl in *; cleanup; try tauto;
    repeat invert_exec; simpl in *; cleanup; 
    do 4 eexists; intuition eauto.
  }
  {
    simpl in *.
    destruct o5; simpl in *; cleanup; try tauto.
  }
  {
    destruct o3, o5; simpl in *; cleanup; try tauto;
    repeat invert_exec; simpl in *; cleanup;
    try solve [do 4 eexists; intuition eauto].
    3:{
      clear H3 H4 H11 H13 H14 H16.
      Transparent LogCache.recover.
      unfold LogCache.recover in *.
      repeat invert_exec; simpl in *; cleanup.
      unfold Log.log_header_rep, Log.log_rep_general in *; logic_clean.
      eapply Specs.recover_finished in H14; eauto.
      2: {
        unfold Log.log_reboot_rep.
        do 4 eexists; intuition eauto.
        repeat cleanup_pairs; eauto.
        congruence.
      }

      eapply Specs.recover_finished in H22; eauto.
      2: {
        unfold Log.log_reboot_rep.
        do 4 eexists; intuition eauto.
        repeat cleanup_pairs; eauto.
        congruence.
      }
      eapply LogCache.write_lists_to_cache_finished_disk in H12. 
      eapply LogCache.write_lists_to_cache_finished_disk in H19.
      unfold Log.log_rep, Log.log_rep_general in *; cleanup.
      repeat cleanup_pairs; simpl in *.
      do 4 eexists; split; eauto.
          split; eauto.
          unfold 
          Log.log_header_rep, Log.log_rep_general, 
          Log.log_rep_explicit, Log.log_header_block_rep,
          Log.log_rep_inner, Log.header_part_is_valid,
          Log.txns_valid in *;
          cleanup; simpl in *; eauto.
    }
    {
      eapply LogCache.read_finished_disk in H18; eauto.
      eapply LogCache.read_finished_disk in H22; eauto.
      cleanup.
      try solve [do 4 eexists; intuition eauto].
    }
    {
      clear H3 H4 H11 H13 H14 H16.
      eapply LogCache.write_finished_log_rep in H21; eauto.
      eapply LogCache.write_finished_log_rep in H25; eauto.
      destruct H21, H25; try logic_clean.
      {
        do 4 eexists; simpl in *; eauto.
      }
      {
        repeat split_ors; logic_clean; try solve [intuition; try tauto; try lia].
        {
          setoid_rewrite H5 in H16. 
          setoid_rewrite H17 in H16.
          exfalso; eauto.
        }
        {
          erewrite addr_list_to_blocks_length_eq in H25.
          2: do 2 rewrite map_length; symmetry; apply H5.
          setoid_rewrite H17 in H21.
          instantiate (1:=(Nat.add data_start)) in H25.
          exfalso; eapply PeanoNat.Nat.lt_nge; eauto.
        }
        {
          cleanup; simpl in *.
          setoid_rewrite H5 in H16. 
          lia.
        } 
        {
          setoid_rewrite H5 in H16. 
          setoid_rewrite H17 in H16.
          exfalso; eauto.
        }
        {
          erewrite addr_list_to_blocks_length_eq in H25.
          2: do 2 rewrite map_length; symmetry; apply H5.
          setoid_rewrite H17 in H21.
          instantiate (1:=(Nat.add data_start)) in H25.
          exfalso; eapply PeanoNat.Nat.lt_nge; eauto.
        }
        {
          cleanup; simpl in *.
          setoid_rewrite H5 in H16. 
          lia.
        } 
      }
      {
        repeat split_ors; logic_clean; try solve [intuition; try tauto; try lia].
        {
          setoid_rewrite <- H5 in H21. 
          setoid_rewrite <- H17 in H21.
          exfalso; eauto.
        }
        {
          setoid_rewrite <- H5 in H21. 
          setoid_rewrite <- H17 in H21.
          exfalso; eauto.
        }
        {
          erewrite addr_list_to_blocks_length_eq in H23.
          2: do 2 rewrite map_length; rewrite H5; eauto.
          setoid_rewrite <- H17 in H23.
          instantiate (1:=(Nat.add data_start)) in H23.
          exfalso; eapply PeanoNat.Nat.lt_nge; eauto.
        }
        {
          erewrite addr_list_to_blocks_length_eq in H23.
          2: do 2 rewrite map_length; rewrite H5; eauto.
          setoid_rewrite <- H17 in H23.
          instantiate (1:=(Nat.add data_start)) in H23.
          exfalso; eapply PeanoNat.Nat.lt_nge; eauto.
        }
        {
          cleanup; simpl in *.
          setoid_rewrite <- H5 in H21. 
          lia.
        }
        {
          cleanup; simpl in *.
          setoid_rewrite <- H5 in H21. 
          lia.
        }
      }
      {
        repeat split_ors; logic_clean.
        {
          do 4 eexists; split; eauto.
          split; eauto.
          unfold 
          Log.log_header_rep, Log.log_rep_general, 
          Log.log_rep_explicit, Log.log_header_block_rep,
          Log.log_rep_inner, Log.header_part_is_valid,
          Log.txns_valid in *;
          cleanup; simpl in *; eauto.
          rewrite <- H40, <- H53 in *.
          repeat rewrite map_app; simpl.
          eapply forall_app_l in H41, H54; simpl in *.
          inversion H41; inversion H54; subst.
          unfold Log.txn_well_formed in *; cleanup.
          split.
          repeat rewrite fold_left_app; simpl.
          erewrite addr_list_to_blocks_length_eq.
          2: do 2 rewrite map_length; apply H5. 
          instantiate (1:=(Nat.add data_start)).
          rewrite H6; eauto.
          split; apply Forall2_app; eauto;
          repeat constructor.
          rewrite H60, H91.
          erewrite addr_list_to_blocks_length_eq; eauto.
          do 2 rewrite map_length; apply H5.
          rewrite H63, H92; eauto.
        }
        {
          erewrite addr_list_to_blocks_length_eq in H32.
          2: do 2 rewrite map_length; apply H5. 
          setoid_rewrite H17 in H32.
          setoid_rewrite H6 in H32.
          instantiate (1:=(Nat.add data_start)) in H32.
          exfalso; eapply PeanoNat.Nat.lt_nge.
          apply H33. eauto.
        }
        {
          erewrite addr_list_to_blocks_length_eq in H32.
          2: do 2 rewrite map_length; apply H5. 
          setoid_rewrite H17 in H32.
          setoid_rewrite H6 in H32.
          instantiate (1:=(Nat.add data_start)) in H32.
          exfalso; eapply PeanoNat.Nat.lt_nge.
          apply H32. eauto.
        }
        {
          do 4 eexists; split; eauto.
          split; eauto.
          unfold 
          Log.log_header_rep, Log.log_rep_general, 
          Log.log_rep_explicit, Log.log_header_block_rep,
          Log.log_rep_inner, Log.header_part_is_valid,
          Log.txns_valid in *;
          cleanup; simpl in *; eauto.
          rewrite <- H40, <- H53 in *.
          repeat rewrite map_app; simpl.
          inversion H41; inversion H54; subst.
          unfold Log.txn_well_formed in *; cleanup.
          rewrite <- H40, <- H53 in *.
          split.
          erewrite addr_list_to_blocks_length_eq.
          2: do 2 rewrite map_length; apply H5. 
          instantiate (1:=(Nat.add data_start)); eauto.
          split; eauto;
          repeat constructor.
          rewrite H60, H91.
          erewrite addr_list_to_blocks_length_eq; eauto.
          do 2 rewrite map_length; apply H5.
          rewrite H63, H92; eauto.
        }
      }
    }
    {
      exfalso; eapply H9; eauto.
    }
  }
  {
    repeat invert_exec; do 4 eexists; intuition eauto.
  }
  {
    repeat invert_exec.
    repeat rewrite <- app_assoc in *.
    repeat split_ors; cleanup; repeat unify_execs_prefix;
    cleanup; repeat unify_execs; cleanup.
    exfalso; eapply finished_not_crashed_oracle_prefix in H4; 
    [eauto | eauto];
    rewrite <- app_assoc; eauto.

    exfalso; eapply finished_not_crashed_oracle_prefix in H4; eauto;
    rewrite <- app_assoc; eauto.
    rewrite H13; eauto.
    instantiate (1 := nil); rewrite app_nil_r; eauto.

    exfalso; eapply finished_not_crashed_oracle_prefix in H5; eauto;
    rewrite <- app_assoc; eauto.
    rewrite H19; eauto.
    rewrite app_nil_r; eauto.

    eapply_fresh exec_finished_deterministic_prefix in H4; eauto; cleanup.
    eapply_fresh exec_finished_deterministic_prefix in H5; eauto; cleanup.
    2: erewrite H19; eauto.
    repeat unify_execs; cleanup.

    eapply_fresh ATCD_exec_lift_finished in H4; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      eapply_fresh ATCD_exec_lift_finished in H5; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      simpl in *; cleanup.

    eapply_fresh ATCD_oracle_refines_impl_eq in H5.
    6: apply H4.
    all: eauto.
    2: apply TC_oracle_refines_operation_eq.
    cleanup; eauto.
    repeat unify_execs; cleanup.

    edestruct IHp1.
    5: eauto.
    5: eauto.
    5: eauto.
    all: eauto.
    logic_clean.
    eauto.

    Unshelve.
    all: constructor.
  }
Qed.


Lemma ATCD_oracle_refines_impl_eq_crashed:
forall u T p1 T' p2 s1 s2 s1' s2' s1a s2a o1 o2 o3 o4 oa1 oa2 
selector hdr1 hdr2 merged_disk1 merged_disk2, (* oa3 oa4, *)
oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement
  T u s1 p1 (ATCD_reboot_f selector) o1 oa1 ->
oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement
  T' u s2 p2 (ATCD_reboot_f selector) o2 oa2 ->

  (* Change this *)
  (exists txns1,
      fst (snd (snd s1)) = Mem.list_upd_batch empty_mem (map Log.addr_list txns1) (map Log.data_blocks txns1) /\
      Log.log_header_rep hdr1 txns1 (snd (snd (snd s1))) /\
      merged_disk1 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd (snd (snd s1)))) (map Log.addr_list txns1) (map Log.data_blocks txns1))) /\
      (forall a, a >= data_start -> snd ((snd (snd (snd (snd s1)))) a) = [])) ->
  (exists txns2, 
      fst (snd (snd s2)) = Mem.list_upd_batch empty_mem (map Log.addr_list txns2) (map Log.data_blocks txns2) /\
      Log.log_header_rep hdr2 txns2 (snd (snd (snd s2))) /\
      merged_disk2 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd (snd (snd s2)))) (map Log.addr_list txns2) (map Log.data_blocks txns2))) /\
      (forall a, a >= data_start -> snd ((snd(snd (snd (snd s2)))) a) = [])) ->

  @HC_refines _ _ _ _ _ ATCLang TCD_CoreRefinement s1 s1a ->
  @HC_refines _ _ _ _ _ ATCLang TCD_CoreRefinement s2 s2a ->

  exec ATCDLang u o1 s1 (ATCD_Refinement.(Simulation.Definitions.compile) p1) (Crashed s1') ->
  exec ATCDLang u o2 s2 (ATCD_Refinement.(Simulation.Definitions.compile) p2) (Crashed s2') ->
  ATC_have_same_structure p1 p2 u s1a s2a ->

  (forall u T (o1: operation TransactionCacheOperation T) T' (o2 : operation TransactionCacheOperation T') x x0 x1 x2 x3 x4 x5 x6 s1 s2 s1' s2' r1 r2,
  TCD_CoreRefinement.(Simulation.Definitions.token_refines) u s1 o1 x5 x4 x0 ->
  TCD_CoreRefinement.(Simulation.Definitions.token_refines) u s2 o2 x2 x1 x6 ->
  exec TCDLang u x4 s1
  (TCD_CoreRefinement.(Simulation.Definitions.compile_core) o1)
  (Finished s1' r1) ->
  exec TCDLang u x1 s2
  (TCD_CoreRefinement.(Simulation.Definitions.compile_core) o2)
  (Finished s2' r2) ->
  TC_have_same_structure o1 o2 ->
(exists s1a0 : state Definitions.abs, refines (snd s1) s1a0) ->
(exists s2a0 : state Definitions.abs, refines (snd s2) s2a0) ->
  x1 ++ x = x4 ++ x3 ->
  x1 = x4 /\ x0 = x6) ->

  (forall (u0 : user) (T : Type) (o1 : operation TransactionCacheOperation T)
  (T' : Type) (o2 : operation TransactionCacheOperation T')
  x16 x17 x18 x20 x21 x23 s0 s3 s1' s2' hdr1 hdr2 selector merged_disk1 merged_disk2,
  TCD_CoreRefinement.(Simulation.Definitions.token_refines) u0 s0 o1 
  (fun s => ([], (empty_mem, (fst (snd (snd s)), select_total_mem selector (snd (snd (snd s))))))) x21
  x17 ->
  TCD_CoreRefinement.(Simulation.Definitions.token_refines) u0 s3 o2 
  (fun s => ([], (empty_mem, (fst (snd (snd s)), select_total_mem selector (snd (snd (snd s))))))) x18
  x23 ->
  exec (TCDLang) u0 x21 s0
  (TCD_CoreRefinement.(Simulation.Definitions.compile_core) o1) 
  (Crashed s1') ->
  exec (TCDLang) u0 x18 s3
  (TCD_CoreRefinement.(Simulation.Definitions.compile_core) o2)
  (Crashed s2') ->
  TC_have_same_structure o1 o2 -> 
  (exists txns1,
      fst (snd s0) = Mem.list_upd_batch empty_mem (map Log.addr_list txns1) (map Log.data_blocks txns1) /\
      Log.log_header_rep hdr1 txns1 (snd (snd s0)) /\
      merged_disk1 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd (snd s0))) (map Log.addr_list txns1) (map Log.data_blocks txns1))) /\
      (forall a, a >= data_start -> snd ((snd (snd (snd s0))) a) = [])) ->
  (exists txns2, 
      fst (snd s3) = Mem.list_upd_batch empty_mem (map Log.addr_list txns2) (map Log.data_blocks txns2) /\
      Log.log_header_rep hdr2 txns2 (snd (snd s3)) /\
      merged_disk2 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd (snd s3))) (map Log.addr_list txns2) (map Log.data_blocks txns2))) /\
      (forall a, a >= data_start -> snd ((snd(snd (snd s3))) a) = [])) ->
  Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
  Forall2 (fun rec1 rec2 => Log.addr_count rec1 = Log.addr_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
  Forall2 (fun rec1 rec2 => Log.data_count rec1 = Log.data_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
  no_accidental_overlap selector (snd (snd (snd s1'))) ->
  no_accidental_overlap selector (snd (snd (snd s2'))) ->
  x18 ++ x16 = x21 ++ x20 -> x17 = x23) ->

  Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
  Forall2 (fun rec1 rec2 => Log.addr_count rec1 = Log.addr_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
  Forall2 (fun rec1 rec2 => Log.data_count rec1 = Log.data_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
  no_accidental_overlap selector (snd (snd (snd (snd s1')))) ->
  no_accidental_overlap selector (snd (snd (snd (snd s2')))) -> 
  o1 ++ o3 = o2 ++ o4 ->
  not_init p1 /\ not_init p2 ->
  oa1 = oa2.
Proof.
  induction p1; destruct p2; simpl; intros; try tauto; 
  cleanup_no_match; try tauto.
  {
    clear H16 H17.
    cleanup_no_match; try tauto;
    unfold HC_token_refines in *; cleanup;
    simpl in *; cleanup_no_match; try tauto; eauto.

    specialize (H17 tt).
    specialize (H22 tt).
    eapply_fresh HC_map_ext_eq_prefix in H15; eauto; cleanup_no_match.
    eapply lift2_invert_exec_crashed in H5; cleanup.
    eapply lift2_invert_exec_crashed in H6; cleanup.
    eapply_fresh HC_map_ext_eq in H6; eauto; subst.
    eapply_fresh HC_map_ext_eq in H0; eauto; subst.

    assert (x5 = x3). {
      eapply H9. 
      5: eauto.
      all: simpl in *; eauto.
      destruct o5; simpl in *; 
      cleanup; try tauto; eauto;
      repeat (simpl in *; cleanup); eauto.
      destruct o6; simpl in *; 
      cleanup; try tauto; eauto;
      repeat (simpl in *; cleanup); eauto.
    }
    cleanup; eauto.
  }
  {
    repeat invert_exec; eauto.
    repeat split_ors; cleanup; 
    simpl in *; cleanup; 
    try congruence; eauto.
    repeat invert_exec.
    repeat invert_exec.
  }
  {
    repeat invert_exec.
    repeat rewrite <- app_assoc in *.
    repeat split_ors; cleanup; 
    repeat unify_execs_prefix;
    cleanup; repeat unify_execs; cleanup.
    eapply_fresh ATCD_exec_lift_crashed in H6; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply_fresh ATCD_exec_lift_crashed in H7; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    simpl in *; cleanup.
    eapply IHp1; eauto.

    all: try match goal with
    | [H: exec _ _ ?x ?s2 ?p (Finished _ _),
      H0: exec _ _ (?x ++ _) ?s2 ?p (Crashed _) |- _] =>
    exfalso; eapply finished_not_crashed_oracle_prefix in H; [
      eapply H; eauto | rewrite <- app_assoc; eauto ]
    end.

    rewrite <- app_assoc in *.

    eapply exec_finished_deterministic_prefix in H30; eauto; cleanup.
    eapply_fresh ATCD_exec_lift_crashed in H7; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply_fresh ATCD_exec_lift_finished in H8; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    simpl in *; cleanup.
    exfalso; eapply ATCD_oracle_refines_prefix_one_crashed.
    4: eauto.
    6: eauto.
    8: eauto.
    all: eauto.

    rewrite <- app_assoc in *.
    eapply exec_finished_deterministic_prefix in H28; eauto; cleanup.
    eapply_fresh ATCD_exec_lift_crashed in H6; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply_fresh ATCD_exec_lift_finished in H8; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    simpl in *; cleanup.
    exfalso; eapply ATCD_oracle_refines_prefix_one_crashed.
    4: apply H6.
    3: apply H8.
    5: eapply ATC_have_same_structure_sym; eauto.
    all: eauto.

    eapply exec_finished_deterministic_prefix in H36; eauto; cleanup.
    eapply exec_finished_deterministic_prefix in H31; eauto; cleanup.
    repeat unify_execs; cleanup.
    repeat rewrite <- app_assoc in *.
    eapply_fresh ATCD_exec_lift_finished in H8; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply_fresh ATCD_exec_lift_finished in H25; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    simpl in *; cleanup.
    eapply_fresh ATCD_oracle_refines_impl_eq in H33.
    7: eauto.
    all: eauto.
    cleanup.

    eapply_fresh equivalence_preserved in H11; eauto.
    logic_clean.
    unfold HC_refines in H6, H7; simpl in *.
    unfold HC_refines in H6, H7; simpl in *.
    unfold refines, LogCache.cached_log_rep,
    Log.log_rep in H6, H7; simpl in *.
    cleanup.
    eapply H in H16.
    8: eauto.
    9: eauto.
    8: eauto.
    2: eauto.
    2: eauto.
    all: eauto.
    cleanup; eauto.
    unfold HC_refines; simpl in *.
    unfold HC_refines; simpl in *.
    unfold refines, LogCache.cached_log_rep,
    Log.log_rep; simpl in *.
    intuition eauto.
    eexists; intuition eauto.
    unfold HC_refines; simpl in *.
    unfold HC_refines; simpl in *.
    unfold refines, LogCache.cached_log_rep,
    Log.log_rep; simpl in *.
    intuition eauto.
    eexists; intuition eauto. 
    {
      clear H24 H27. 
      unfold Log.log_rep_general, 
      Log.log_rep_explicit, Log.log_header_block_rep,
      Log.log_rep_inner, Log.header_part_is_valid,
      Log.txns_valid in *;
      cleanup; simpl in *; eauto.
      unfold Log.log_header_rep, Log.log_rep_general, 
      Log.log_rep_explicit, Log.log_header_block_rep,
      Log.log_rep_inner, Log.header_part_is_valid,
      Log.txns_valid in *;
      cleanup; simpl in *; eauto.
    }
    {
      clear H24 H27. 
      unfold Log.log_rep_general, 
      Log.log_rep_explicit, Log.log_header_block_rep,
      Log.log_rep_inner, Log.header_part_is_valid,
      Log.txns_valid in *;
      cleanup; simpl in *; eauto.
      unfold Log.log_header_rep, Log.log_rep_general, 
      Log.log_rep_explicit, Log.log_header_block_rep,
      Log.log_rep_inner, Log.header_part_is_valid,
      Log.txns_valid in *;
      cleanup; simpl in *; eauto.
    }
    {
      clear H24 H27. 
      unfold Log.log_rep_general, 
      Log.log_rep_explicit, Log.log_header_block_rep,
      Log.log_rep_inner, Log.header_part_is_valid,
      Log.txns_valid in *;
      cleanup; simpl in *; eauto.
      unfold Log.log_header_rep, Log.log_rep_general, 
      Log.log_rep_explicit, Log.log_header_block_rep,
      Log.log_rep_inner, Log.header_part_is_valid,
      Log.txns_valid in *;
      cleanup; simpl in *; eauto.
    }
  }
Unshelve.
all: eauto.
Qed.



Lemma ATCD_ORS_transfer:
forall (l_selector: list (@total_mem addr addr_dec nat)) 
T (p1 p2: AD.(prog) T)  u u' ex l_o_imp l_o_abs l_o_abs' (s1 s2: state ATCDLang),

ATC_Simulation.not_init p1 ->
ATC_Simulation.not_init p2 ->
(forall s1a s2a o_abs l_o_abs_rest o_abs' l_o_abs_rest' o1 o2 o3 o4 selector,
  l_o_abs = o_abs :: l_o_abs_rest ->
  l_o_abs' = o_abs' :: l_o_abs_rest' ->

(refines_related ATC_Refinement (AD_related_states u' ex)) s1a s2a ->

((exists s1' s2' r1 r2,
exec ATCLang u o_abs s1a (Simulation.Definitions.compile ATC_Refinement p1) (Finished s1' r1) /\
exec ATCLang u o_abs' s2a (Simulation.Definitions.compile ATC_Refinement p2) (Finished s2' r2)) \/
(exists s1' s2',
exec ATCLang u o_abs s1a (Simulation.Definitions.compile ATC_Refinement p1) (Crashed s1') /\
exec ATCLang u o_abs' s2a (Simulation.Definitions.compile ATC_Refinement p2) (Crashed s2'))) ->

oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement
  T u s1 (Simulation.Definitions.compile ATC_Refinement p1) (ATCD_reboot_f selector) o1 o_abs ->
oracle_refines _ _ ATCDLang ATCLang ATCD_CoreRefinement
  T u s2 (Simulation.Definitions.compile ATC_Refinement p2) (ATCD_reboot_f selector) o2 o_abs' ->

  (exists hdr1 hdr2 merged_disk1 merged_disk2,
  (exists txns1,
        fst (snd (snd s1)) = Mem.list_upd_batch empty_mem (map Log.addr_list txns1) (map Log.data_blocks txns1) /\
        Log.log_header_rep hdr1 txns1 (snd (snd (snd s1))) /\
        merged_disk1 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd (snd (snd s1)))) (map Log.addr_list txns1) (map Log.data_blocks txns1))) /\
        (forall a, a >= data_start -> snd ((snd (snd (snd (snd s1)))) a) = [])) /\
    (exists txns2, 
        fst (snd (snd s2)) = Mem.list_upd_batch empty_mem (map Log.addr_list txns2) (map Log.data_blocks txns2) /\
        Log.log_header_rep hdr2 txns2 (snd (snd (snd s2))) /\
        merged_disk2 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd (snd (snd s2)))) (map Log.addr_list txns2) (map Log.data_blocks txns2))) /\
        (forall a, a >= data_start -> snd ((snd(snd (snd (snd s2)))) a) = [])) /\
    Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) /\
    Forall2 (fun rec1 rec2 => Log.addr_count rec1 = Log.addr_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) /\
    Forall2 (fun rec1 rec2 => Log.data_count rec1 = Log.data_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2))) ->

o1 ++ o2 = o3 ++ o4 ->

ATC_have_same_structure (Simulation.Definitions.compile ATC_Refinement p1)
(Simulation.Definitions.compile ATC_Refinement p2) u s1a s2a) ->

(exists hdr1 hdr2 merged_disk1 merged_disk2,
(exists txns1,
      fst (snd (snd s1)) = Mem.list_upd_batch empty_mem (map Log.addr_list txns1) (map Log.data_blocks txns1) /\
      Log.log_header_rep hdr1 txns1 (snd (snd (snd s1))) /\
      merged_disk1 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd (snd (snd s1)))) (map Log.addr_list txns1) (map Log.data_blocks txns1))) /\
      (forall a, a >= data_start -> snd ((snd (snd (snd (snd s1)))) a) = [])) /\
  (exists txns2, 
      fst (snd (snd s2)) = Mem.list_upd_batch empty_mem (map Log.addr_list txns2) (map Log.data_blocks txns2) /\
      Log.log_header_rep hdr2 txns2 (snd (snd (snd s2))) /\
      merged_disk2 = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd (snd (snd s2)))) (map Log.addr_list txns2) (map Log.data_blocks txns2))) /\
      (forall a, a >= data_start -> snd ((snd(snd (snd (snd s2)))) a) = [])) /\
  Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) /\
  Forall2 (fun rec1 rec2 => Log.addr_count rec1 = Log.addr_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) /\
  Forall2 (fun rec1 rec2 => Log.data_count rec1 = Log.data_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2))) ->

  (forall o_imp l_o_imp_rest selector l_selector_rest s1', 
  l_o_imp = o_imp :: l_o_imp_rest ->
  l_selector = selector :: l_selector_rest ->
  exec ATCDLang u o_imp s1 (Simulation.Definitions.compile ATCD_Refinement 
    (Simulation.Definitions.compile ATC_Refinement p1)) (Crashed s1') ->
  no_accidental_overlap selector
  (snd (snd (snd (snd s1'))))) ->

  (forall o_imp l_o_imp_rest selector l_selector_rest s2', 
  l_o_imp = o_imp :: l_o_imp_rest ->
  l_selector = selector :: l_selector_rest ->
  exec ATCDLang u o_imp s2 (Simulation.Definitions.compile ATCD_Refinement 
    (Simulation.Definitions.compile ATC_Refinement p2)) (Crashed s2') ->
  no_accidental_overlap selector
  (snd (snd (snd (snd s2'))))) ->

oracle_refines_same_from_related_explicit ATCD_Refinement u
(Simulation.Definitions.compile ATC_Refinement p1)
(Simulation.Definitions.compile ATC_Refinement p2)
(Simulation.Definitions.compile ATC_Refinement File.recover)
(ATCD_reboot_list l_selector)
(refines_related ATC_Refinement (AD_related_states u' ex))
l_o_imp l_o_abs l_o_abs' s1 s2.
Proof.
  unfold ATCD_reboot_list, TCD_reboot_list; induction l_selector; intros.
  {
    unfold oracle_refines_same_from_related_explicit; intros.
    simpl in *.
    destruct l_o_imp; simpl in *; try tauto.
    cleanup; try tauto.
    simpl in *; repeat split_ors; cleanup; try tauto.
    unfold refines_related at 1 in H5; cleanup; eauto.
    simpl in *.
    eapply_fresh ATCD_exec_lift_finished in H8; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    eapply_fresh ATCD_exec_lift_finished in H9; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    simpl in *; cleanup. 
    eapply ATCD_oracle_refines_impl_eq in H8.
    6: apply H9.
    all: eauto.
    3: apply TC_oracle_refines_operation_eq.
    cleanup; eauto.
    all: shelve.
  }
  {
    unfold oracle_refines_same_from_related_explicit; intros.
    simpl in *.
    destruct l_o_imp; simpl in *; try tauto.
    cleanup; try tauto.
    unfold refines_related at 1 in H5; cleanup; eauto.
    simpl in *; repeat split_ors; cleanup; try tauto.
    {
      simpl in *.
      eapply_fresh ATCD_exec_lift_finished in H8; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    eapply_fresh ATCD_exec_lift_finished in H9; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed]. 
      eapply ATCD_oracle_refines_impl_eq in H8.
      6: apply H9.
      all: eauto.
      3: apply TC_oracle_refines_operation_eq.
      cleanup; eauto.
      all: shelve.
    }
    {
      simpl in *.
      eapply_fresh ATCD_exec_lift_finished in H8; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    eapply_fresh ATCD_exec_lift_crashed in H9; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      exfalso; eapply ATCD_oracle_refines_prefix_one_crashed.
      3: eauto.
      3: eauto.
      all: eauto.
      all: shelve.
    }
    {
      simpl in *.
      eapply_fresh ATCD_exec_lift_crashed in H8; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    eapply_fresh ATCD_exec_lift_finished in H9; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      exfalso; eapply ATCD_oracle_refines_prefix_one_crashed.
      3: eauto.
      3: eauto.
      all: eauto.
      all: shelve.
    }
    {
      simpl in *. 
      eapply_fresh ATCD_exec_lift_crashed in H8; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    eapply_fresh ATCD_exec_lift_crashed in H9; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      eapply_fresh ATCD_oracle_refines_impl_eq_crashed in H8.
      8: apply H9.
      all: eauto.
      3: apply TC_oracle_refines_operation_eq.
      3: apply TC_oracle_refines_operation_eq_crashed; eauto.
      eapply ATCD_ORS_recover in H21.
      apply H21 in H23; 
      subst; eauto.
      all: shelve.
    }
  }
  Unshelve.
  all: eauto.
  all: try split.
  all: try solve [eapply not_init_compile; eauto].
  all: try solve[
    try logic_clean;
    eapply H1 in H18; eauto;[
    left; do 4 eexists; intuition eauto|
    do 4 eexists; intuition eauto] ].
    exact (fun _ => 0).
  {
    cleanup.
    eapply ATC_have_same_structure_sym.
    eapply H1 in H18; eauto.
    right; do 2 eexists; intuition eauto.
    do 4 eexists; intuition eauto.
  }
  exact (fun _ _ => True).
  {
    unfold refines_related_reboot in *; cleanup; simpl in *.
    eapply ATCD_exec_lift_crashed in H8; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    eapply ATCD_exec_lift_crashed in H9; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.


    unfold ATCD_refines_reboot in *; simpl in *.
    unfold HC_refines_reboot; simpl;
    unfold HC_refines_reboot; simpl.
    eexists (_, (_, _)), (_, (_, _)).
    simpl; intuition eauto.
    all: eapply not_init_compile; eauto.
  }
    {
    cleanup.
    eapply H1 in H18; eauto.
    do 4 eexists; intuition eauto.
  }
  Unshelve. 
  all: eauto.
  all: try tauto.
  exact (fun _ => 0).
Qed.


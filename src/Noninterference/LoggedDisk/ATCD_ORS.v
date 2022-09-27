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
      | ListLayer.Put _, ListLayer.Put _ => True
      | ListLayer.Delete _, ListLayer.Delete _ => True
      | _, _ => False
      end
    | P2 p1, P2 p2 =>
      LD_have_same_structure p1 p2
    | _, _ => False
    end.

Fixpoint ATC_have_same_structure {T T'} (p1: ATCLang.(prog) T) (p2: ATCLang.(prog) T') u s1 s2:=
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
    (forall o s1' r1 s2' r2,
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

(**
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
*)


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

Lemma lt_exists:
forall n m,
n < m ->
exists k, m = n + S k.
Proof.
  induction n; destruct m; 
  intros; cleanup; try lia.
  simpl; intuition eauto.
  edestruct (IHn m); try lia.
  exists x; subst; lia.
Qed.

Lemma rec_oracle_finished_crypto_op1_crypto_one_sided_exfalso :
forall len1 len2 l,
BatchOperations.rec_oracle_finished_crypto len2 ++ l = BatchOperations.rec_oracle_op1_crypto len1 ->
False.
Proof.
    unfold BatchOperations.rec_oracle_finished_crypto,
    BatchOperations.rec_oracle_op1_crypto; intros.
    destruct (Compare_dec.lt_dec len1 len2).
    eapply lt_exists in l0; cleanup.
    rewrite <- repeat_app in H.
    rewrite <- (app_nil_r (repeat
    (OpToken
      (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
      (Token1 CryptoOperation
          (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size))
          CryptoLayer.Cont)) len1)) in H at 2.
    repeat rewrite <- app_assoc in H; cleanup; 
    simpl in *; try congruence.
    eapply PeanoNat.Nat.nlt_ge in n.
    eapply PeanoNat.Nat.le_lteq in n.
    intuition.
    {
    eapply lt_exists in H0; cleanup.
    rewrite <- repeat_app in H.
    repeat rewrite <- app_assoc in H; cleanup; 
    simpl in *; try congruence.
    }
    {
      subst.
      rewrite <- (app_nil_r (repeat
    (OpToken
      (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
      (Token1 CryptoOperation
          (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size))
          CryptoLayer.Cont)) len1)) in H at 2.
    repeat rewrite <- app_assoc in H; cleanup; 
    simpl in *; try congruence.
    }
Qed.

Lemma rec_oracle_finished_crypto_op1_crypto_ne_exfalso :
forall len1 len2 l1 l2 t,
len1 <> len2 ->
t <> OpToken
(HorizontalComposition CryptoOperation
    (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
(Token1 CryptoOperation
    (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size))
    CryptoLayer.Cont) ->
BatchOperations.rec_oracle_finished_crypto len2 ++ l1 = BatchOperations.rec_oracle_op1_crypto len1 ++
t :: l2 ->
False.
Proof.
    unfold BatchOperations.rec_oracle_finished_crypto,
    BatchOperations.rec_oracle_op1_crypto; intros.
    apply PeanoNat.Nat.lt_gt_cases in H.
    split_ors;
    eapply lt_exists in H; cleanup;
    rewrite <- repeat_app in H1;
    repeat rewrite <- app_assoc in H1; cleanup; 
    simpl in *; try congruence.
Qed.

Lemma map_transform_token_ext :
forall l1 l2, 
map LogCache.transform_token l1 = map LogCache.transform_token l2 ->
l1 = l2.
Proof.
  induction l1; destruct l2; intros; simpl in *; try congruence.
  inversion H; simpl in *.
  erewrite IHl1; eauto.
  unfold LogCache.transform_token in *; cleanup; eauto; congruence.
Qed.

Lemma map_transform_token_ext_prefix :
forall l1 l2 l3 l4, 
map LogCache.transform_token l1 ++ l3 = map LogCache.transform_token l2 ++ l4 ->
exists l3' l4', l1 ++ l3' = l2 ++ l4'.
Proof.
  induction l1; destruct l2; intros; simpl in *; 
  try congruence; intuition eauto.
  inversion H; simpl in *.
  eapply IHl1 in H2; cleanup.
  exists x, x0; 
  unfold LogCache.transform_token in *; cleanup; 
  intuition eauto; try congruence.
  Unshelve.
  all: constructor.
Qed.

Lemma commit_crashed_oracle_is_1_4_exfalso:
forall o1 o2 len1 len2 l1 l2, 
o1 ++ l1 =
o2 ++ l2 ->
Specs.commit_crashed_oracle_is_1 o1 len1 ->
Specs.commit_crashed_oracle_is_4 o2 len2 ->
False.
Proof.
  unfold Specs.commit_crashed_oracle_is_1,
  Specs.commit_crashed_oracle_is_4; intros.
  cleanup; repeat split_ors; cleanup; 
  simpl in *; cleanup.
  unfold Specs.commit_txn_crashed_oracle_is_1 in *.
  cleanup; repeat split_ors; cleanup;
  simpl in *; cleanup.

  {
    unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *.
    simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup;
    repeat rewrite map_app in *; simpl in *;
    repeat rewrite <- app_assoc in *.
    {
      destruct (PeanoNat.Nat.eq_dec x3 len2); subst.
      {
      unfold BatchOperations.rec_oracle_finished_crypto in *;
      rewrite <- app_assoc in *; cleanup.
      simpl in *; cleanup.
      }
      {
        unfold BatchOperations.rec_oracle_finished_crypto,
        BatchOperations.rec_oracle_op1_crypto in *;
        repeat rewrite <- app_assoc in *;
        apply PeanoNat.Nat.lt_gt_cases in n.
        split_ors;
        eapply lt_exists in H0; cleanup;
        rewrite <- repeat_app in H3;
        repeat rewrite <- app_assoc in * ; cleanup; 
        simpl in *; try congruence.
      }
    }
    {
      destruct (PeanoNat.Nat.eq_dec len1 len2); subst.
      {
      unfold BatchOperations.rec_oracle_finished_crypto in *;
      rewrite <- app_assoc in *; cleanup.
      simpl in *; cleanup.
      }
      {
          unfold BatchOperations.rec_oracle_finished_crypto,
          BatchOperations.rec_oracle_op1_crypto in *;
          repeat rewrite <- app_assoc in *;
          apply PeanoNat.Nat.lt_gt_cases in n.
          split_ors;
          eapply lt_exists in H; cleanup;
          rewrite <- repeat_app in H3;
          repeat rewrite <- app_assoc in * ; cleanup; 
          simpl in *; try congruence.
      }
    }
    {
      destruct (PeanoNat.Nat.eq_dec len1 len2); subst.
      {
        unfold BatchOperations.rec_oracle_finished_crypto in *;
        rewrite <- app_assoc in *; cleanup.
        simpl in *; cleanup.
        eapply lt_exists in H; cleanup.
        unfold BatchOperations.rec_oracle_op2 in *.
        rewrite <- repeat_app in H1;
        repeat rewrite <- app_assoc in H1; cleanup; 
        simpl in *; try congruence.
      }
      {
          unfold BatchOperations.rec_oracle_finished_crypto,
          BatchOperations.rec_oracle_op1_crypto in *;
          repeat rewrite <- app_assoc in *;
          apply PeanoNat.Nat.lt_gt_cases in n.
          split_ors;
          eapply lt_exists in H0; cleanup;
          rewrite <- repeat_app in H3;
          repeat rewrite <- app_assoc in * ; cleanup; 
          simpl in *; try congruence.
      }
    }
  }
  {
    unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *.
    simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup;
    repeat rewrite <- app_assoc in *.
    {
      destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
      destruct (PeanoNat.Nat.eq_dec x3 len2); subst; cleanup.
      {
        unfold BatchOperations.rec_oracle_finished_crypto in *;
        rewrite <- app_assoc in *; cleanup.
        simpl in *; cleanup.
      }
      {
        unfold BatchOperations.rec_oracle_finished_crypto,
        BatchOperations.rec_oracle_op1_crypto in *;
        repeat rewrite <- app_assoc in *;
        apply PeanoNat.Nat.lt_gt_cases in n.
        split_ors; try lia;
        eapply lt_exists in H0; cleanup;
        rewrite <- repeat_app in H3;
        repeat rewrite <- app_assoc in * ; cleanup; 
        simpl in *; try congruence.
      }
      {
        unfold BatchOperations.rec_oracle_finished_crypto,
        BatchOperations.rec_oracle_op1_crypto in *;
        repeat rewrite <- app_assoc in *;
        apply PeanoNat.Nat.lt_gt_cases in n.
        split_ors; try lia;
        eapply lt_exists in H0; cleanup;
        rewrite <- repeat_app in H3;
        repeat rewrite <- app_assoc in * ; cleanup; 
        simpl in *; try congruence.
      }
    }
    {
      destruct (PeanoNat.Nat.eq_dec len1 len2); subst.
      repeat rewrite <- app_assoc in *; cleanup; 
      simpl in *; try congruence.
      {
        unfold BatchOperations.rec_oracle_finished_crypto in *;
        rewrite <- app_assoc in *; cleanup.
        simpl in *; cleanup.
      }
      {
        unfold BatchOperations.rec_oracle_finished_crypto,
        BatchOperations.rec_oracle_op1_crypto in *;
        repeat rewrite <- app_assoc in *;
        apply PeanoNat.Nat.lt_gt_cases in n.
        split_ors; try lia;
        eapply lt_exists in H; cleanup;
        rewrite <- repeat_app in H3;
        repeat rewrite <- app_assoc in * ; cleanup; 
        simpl in *; try congruence.
      }
    }
    {
      destruct (PeanoNat.Nat.eq_dec len1 len2); subst.
      repeat rewrite <- app_assoc in *; cleanup; 
      simpl in *; try congruence.
      {
        unfold BatchOperations.rec_oracle_finished_crypto in *;
        repeat rewrite <- app_assoc in *; cleanup.
        simpl in *; cleanup.
        unfold BatchOperations.rec_oracle_op2 in *.
        eapply lt_exists in H; cleanup;
        rewrite <- repeat_app in H1;
        repeat rewrite <- app_assoc in * ; cleanup; 
        simpl in *; try congruence.
      }
      {
        unfold BatchOperations.rec_oracle_finished_crypto,
        BatchOperations.rec_oracle_op1_crypto in *;
        repeat rewrite <- app_assoc in *;
        apply PeanoNat.Nat.lt_gt_cases in n.
        split_ors; try lia;
        eapply lt_exists in H0; cleanup;
        rewrite <- repeat_app in H3;
        repeat rewrite <- app_assoc in * ; cleanup; 
        simpl in *; try congruence.
      }
    }
  }
Qed.  

Lemma commit_finished_crashed_1_exfalso :
    forall o1 o2 l1 l2 len1 len2,
    o1 ++ l1 = o2 ++ l2 ->
    Specs.commit_crashed_oracle_is_1 o1 len1 ->
    Specs.commit_finished_oracle_is_true o2 len2 ->
    False.
      Proof.
        unfold Specs.commit_finished_oracle_is_true, 
        Specs.commit_crashed_oracle_is_1; intros.
        cleanup; simpl in *; cleanup.
        repeat split_ors; cleanup; simpl in *; cleanup.

        unfold Specs.commit_txn_crashed_oracle_is_1 in *.
        repeat split_ors; cleanup; simpl in *; cleanup.
        {
          unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *.
          repeat split_ors; cleanup; simpl in *; cleanup;
          repeat rewrite <- app_assoc in *.
          {
            destruct (PeanoNat.Nat.eq_dec x3 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto in *;
              rewrite <- app_assoc in *; cleanup.
              simpl in *; cleanup.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H0; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
          {
            destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto in *;
              rewrite <- app_assoc in *; cleanup;
              simpl in *; cleanup.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
          {
            destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto in *;
              rewrite <- app_assoc in *; cleanup;
              simpl in *; cleanup.

              unfold BatchOperations.rec_oracle_op2 in *;
              repeat rewrite <- app_assoc in *;
              eapply lt_exists in H; cleanup;
              rewrite <- repeat_app in H1;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H0; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
        }
        {
          unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *.
          repeat split_ors; cleanup; simpl in *; cleanup;
          repeat rewrite <- app_assoc in *.
          {
            destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
            destruct (PeanoNat.Nat.eq_dec x3 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto, 
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *; cleanup.
              simpl in *; cleanup.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H0; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H0; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
          {
            destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto in *;
              rewrite <- app_assoc in *; cleanup;
              simpl in *; cleanup.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
          {
            destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto in *;
              rewrite <- app_assoc in *; cleanup;
              simpl in *; cleanup.

              unfold BatchOperations.rec_oracle_op2 in *;
              repeat rewrite <- app_assoc in *;
              eapply lt_exists in H; cleanup;
              rewrite <- repeat_app in H1;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H0; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
        }
  Qed.

  Lemma commit_crashed_oracle_is_1_3_exfalso :
    forall o1 o2 l1 l2 len1 len2,
    o1 ++ l1 = o2 ++ l2 ->
    Specs.commit_crashed_oracle_is_1 o1 len1 ->
    Specs.commit_crashed_oracle_is_3 o2 len2 ->
    False.
    Proof.
      unfold Specs.commit_crashed_oracle_is_1,
      Specs.commit_crashed_oracle_is_3; intros;
      repeat (intuition; cleanup;
      simpl in *; cleanup).
      {
        unfold Specs.commit_txn_crashed_oracle_is_3 in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup).
      }
      {
        unfold Specs.commit_txn_crashed_oracle_is_1,
        Specs.commit_txn_crashed_oracle_is_3 in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup).
        {
          unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *;
          repeat (intuition; cleanup;
          simpl in *; cleanup);
          repeat rewrite <- app_assoc in *.
          {
            destruct (PeanoNat.Nat.eq_dec x3 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto, 
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *; cleanup;
              simpl in *; cleanup.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
          {
            destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto, 
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *; cleanup;
              simpl in *; cleanup.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
          {
            destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto, 
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *; cleanup;
              simpl in *; cleanup.

              unfold BatchOperations.rec_oracle_op2 in *;
              repeat rewrite <- app_assoc in *;
              eapply lt_exists in H; cleanup;
              rewrite <- repeat_app in H1;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H0; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
        }
        {
          unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *.
          repeat split_ors; cleanup; simpl in *; cleanup;
          repeat rewrite <- app_assoc in *.
          {
            destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
            destruct (PeanoNat.Nat.eq_dec x3 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto, 
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *; cleanup.
              simpl in *; cleanup.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H0; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H0; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
          {
            destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto in *;
              rewrite <- app_assoc in *; cleanup;
              simpl in *; cleanup.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
          {
            destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
            {
              unfold BatchOperations.rec_oracle_finished_crypto in *;
              rewrite <- app_assoc in *; cleanup;
              simpl in *; cleanup.

              unfold BatchOperations.rec_oracle_op2 in *;
              repeat rewrite <- app_assoc in *;
              eapply lt_exists in H; cleanup;
              rewrite <- repeat_app in H1;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
            {
              unfold BatchOperations.rec_oracle_finished_crypto,
              BatchOperations.rec_oracle_op1_crypto in *;
              repeat rewrite <- app_assoc in *;
              apply PeanoNat.Nat.lt_gt_cases in n;
              split_ors; try lia;
              eapply lt_exists in H0; cleanup;
              rewrite <- repeat_app in H3;
              repeat rewrite <- app_assoc in * ; cleanup; 
              simpl in *; try congruence.
            }
          }
        }
      }
  Qed.

    
Lemma write_crashed_oracle_is_4_commit_crashed_oracle_is_1_exfalso :
forall o len1 len2 hdr,
LogCache.write_crashed_oracle_is_4 (map LogCache.transform_token o) hdr len1 ->
Specs.commit_crashed_oracle_is_1 o len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_4,
  Specs.commit_crashed_oracle_is_1,
    Specs.commit_txn_crashed_oracle_is_1; intros; 
    repeat (intuition; cleanup;
  simpl in *; cleanup).
Qed.

Lemma write_crashed_oracle_is_3_commit_crashed_oracle_is_1_exfalso :
forall o len1 len2 hdr,
LogCache.write_crashed_oracle_is_3 (map LogCache.transform_token o) hdr len1 ->
Specs.commit_crashed_oracle_is_1 o len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_3,
  Specs.commit_crashed_oracle_is_1,
    Specs.commit_txn_crashed_oracle_is_1; intros; 
    repeat (intuition; cleanup;
  simpl in *; cleanup).
Qed.
Lemma write_crashed_oracle_is_1_commit_crashed_oracle_is_4_exfalso :
forall o len1 len2 hdr,
LogCache.write_crashed_oracle_is_1 (map LogCache.transform_token o) hdr len1 ->
Specs.commit_crashed_oracle_is_4 o len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_1,
  Specs.commit_crashed_oracle_is_4,
    Specs.commit_txn_crashed_oracle_is_1; intros; 
    repeat (intuition; cleanup;
  simpl in *; cleanup).
Qed.
Lemma write_crashed_oracle_is_1_commit_finished_exfalso :
forall o o' len1 len2 hdr,
LogCache.write_crashed_oracle_is_1 (map LogCache.transform_token o ++ o') hdr len1 ->
Specs.commit_finished_oracle_is_true o len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_1,
  Specs.commit_finished_oracle_is_true,
    Specs.commit_txn_crashed_oracle_is_1; intros; 
    repeat (intuition; cleanup;
  simpl in *; cleanup).
Qed.

Lemma rec_oracle_finished_disk_op1_disk_exfalso:
forall len1 len2 l1 l2 t,
t <> LayerImplementation.Cont CryptoDiskOperation ->
t <> OpToken
(HorizontalComposition CryptoOperation
  (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
(Token2 CryptoOperation
  (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size))
  DiskLayer.Cont) ->
BatchOperations.rec_oracle_finished_disk len1 ++ l1 =
BatchOperations.rec_oracle_op1_disk len2 ++ t :: l2 ->
False.
Proof.
unfold BatchOperations.rec_oracle_finished_disk,
BatchOperations.rec_oracle_op1_disk in *; intros.
repeat rewrite <- app_assoc in *.
repeat rewrite repeat_map in *; simpl in *.
destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup; try congruence.

apply PeanoNat.Nat.lt_gt_cases in n;
split_ors; try lia;
eapply lt_exists in H2; cleanup;
rewrite <- repeat_app in H1;
repeat rewrite <- app_assoc in * ; cleanup; 
simpl in *; try congruence.
Qed.

Lemma rec_oracle_op_2_2_le_exfalso:
forall len1 len2 l1 l2 t,
len1 < len2 ->
t <> LayerImplementation.Cont
(HorizontalComposition CryptoOperation
  (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size))) ->
BatchOperations.rec_oracle_op2 len2 ++ l2 =
BatchOperations.rec_oracle_op2 len1 ++ t :: l1 ->
False.
Proof.
  unfold BatchOperations.rec_oracle_op2 in *; intros.
  eapply lt_exists in H; cleanup;
  rewrite <- repeat_app in H1;
  repeat rewrite <- app_assoc in * ; cleanup; 
  simpl in *; try congruence.
Qed.

Lemma rec_oracle_op_1_disk_ne_exfalso:
forall len1 len2 l1 l2 t,
len1 < len2 ->
t <> OpToken
(HorizontalComposition CryptoOperation
    (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
(Token2 CryptoOperation
    (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size))
    DiskLayer.Cont)->
BatchOperations.rec_oracle_op1_disk len2 ++ l2 =
BatchOperations.rec_oracle_op1_disk len1 ++ t :: l1 ->
False.
Proof.
  unfold BatchOperations.rec_oracle_op1_disk in *; intros.
  eapply lt_exists in H; cleanup;
    rewrite <- repeat_app in H1;
    repeat rewrite <- app_assoc in * ; cleanup; 
    simpl in *; try congruence.
Qed.

Lemma rec_oracle_op_1_crypto_ne_exfalso:
forall len1 len2 l1 l2 t,
len1 < len2 ->
t <> OpToken
(HorizontalComposition CryptoOperation
   (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
(Token1 CryptoOperation
   (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size))
   CryptoLayer.Cont) ->
BatchOperations.rec_oracle_op1_crypto len2 ++ l2 =
BatchOperations.rec_oracle_op1_crypto len1 ++ t :: l1 ->
False.
Proof.
  unfold BatchOperations.rec_oracle_op1_crypto in *; intros.
  eapply lt_exists in H; cleanup;
    rewrite <- repeat_app in H1;
    repeat rewrite <- app_assoc in * ; cleanup; 
    simpl in *; try congruence.
Qed.

Lemma rec_oracle_finished_disk_ne_exfalso:
forall len1 len2 l1 l2,
len1 <> len2 ->
BatchOperations.rec_oracle_finished_disk len2 ++ l2 =
BatchOperations.rec_oracle_finished_disk len1 ++ l1 ->
False.
Proof.
  unfold BatchOperations.rec_oracle_finished_disk in *; intros.
  apply PeanoNat.Nat.lt_gt_cases in H;
  split_ors; 
  repeat rewrite <- app_assoc in *; simpl in *;
  eapply rec_oracle_op_1_disk_ne_exfalso; eauto; congruence.
Qed.

Lemma rec_oracle_finished_crypto_ne_exfalso:
forall len1 len2 l1 l2,
len1 <> len2 ->
BatchOperations.rec_oracle_finished_crypto len2 ++ l2 =
BatchOperations.rec_oracle_finished_crypto len1 ++ l1 ->
False.
Proof.
  unfold BatchOperations.rec_oracle_finished_crypto in *; intros.
  apply PeanoNat.Nat.lt_gt_cases in H;
  split_ors; 
  repeat rewrite <- app_assoc in *; simpl in *;
  eapply rec_oracle_op_1_crypto_ne_exfalso; eauto; congruence.
Qed.

Lemma fold_right_app_length:
forall T (l: list (list T)),
length (fold_right (@app T) [] l) = fold_right (PeanoNat.Nat.add) 0 (map (@length T) l).
Proof.
  induction l; simpl; intros; eauto.
  rewrite app_length; lia.
Qed.

Lemma log_lengths_eq_then_oracle_lengths_same_map:
  forall txns1 txns2 l1 l2,
    fold_left PeanoNat.Nat.add (map
      (fun x : Log.txn =>  Log.addr_count (Log.record x) + Log.data_count (Log.record x)) txns1) 0 =
    fold_left PeanoNat.Nat.add (map
      (fun x : Log.txn => Log.addr_count (Log.record x) + Log.data_count (Log.record x)) txns2) 0 ->
  Forall (fun x : Log.txn =>  Log.addr_count (Log.record x) > 0) txns1 ->
  Forall (fun x : Log.txn =>  Log.addr_count (Log.record x) > 0) txns2 ->
  map LogCache.transform_token
  (fold_right
      (app
        (A:=LayerImplementation.token'
              (HorizontalComposition CryptoOperation
                  (DiskOperation addr_dec value
                    (fun a0 : addr => a0 < disk_size))))) []
      (map
        (fun x : Log.txn =>
          Specs.apply_txn_finished_oracle_is
            (Log.addr_count (Log.record x) +
            Log.data_count (Log.record x))
            (Log.data_count (Log.record x))) txns1)) ++ l1 =
    map LogCache.transform_token
      (fold_right
          (app
            (A:=LayerImplementation.token'
                  (HorizontalComposition CryptoOperation
                      (DiskOperation addr_dec value
                        (fun a0 : addr => a0 < disk_size))))) []
          (map
            (fun x : Log.txn =>
              Specs.apply_txn_finished_oracle_is
                (Log.addr_count (Log.record x) +
                Log.data_count (Log.record x))
                (Log.data_count (Log.record x))) txns2)) ++ l2 ->
  l1 = l2.
  Proof.
    induction txns1; destruct txns2; intros.
    rewrite fold_symmetric in H; simpl in *; try lia; eauto.
    rewrite fold_symmetric in H; simpl in *; try lia; eauto.
    inversion H1; subst.
    rewrite Specs.fold_left_add_remove_start in H; simpl in *; try lia.
    rewrite fold_symmetric in H; simpl in *; try lia; eauto.
    inversion H0; subst; lia.

    inversion H0; inversion H1; subst.
    simpl in *.
    rewrite Specs.fold_left_add_remove_start in H; simpl in *; try lia.
    setoid_rewrite Specs.fold_left_add_remove_start in H at 2; simpl in *; try lia.
    repeat rewrite map_app in *.

    unfold Specs.apply_txn_finished_oracle_is in *;
    repeat rewrite map_app in *;
    repeat rewrite <- app_assoc in *;
    simpl in *;
    destruct (PeanoNat.Nat.eq_dec (Log.addr_count (Log.record a) + Log.data_count (Log.record a)) 
    (Log.addr_count (Log.record t) + Log.data_count (Log.record t))); subst; cleanup.
    {
      destruct (PeanoNat.Nat.eq_dec (Log.data_count (Log.record a)) (Log.data_count (Log.record t))); subst; cleanup.
      {
        eapply IHtxns1 in H4; eauto.
        lia.
      }
      {
        eapply map_transform_token_ext_prefix in H4; cleanup.
        exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      eapply map_transform_token_ext_prefix in H2; cleanup.
      exfalso; eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
    }
  Qed.

Lemma apply_txns_finished_oracle_is_length_eq_map:
  forall hdr1 hdr2 txns1 txns2 s1 s2 l1 l2,
  Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
  Log.log_header_rep hdr1 txns1 s1 ->
  Log.log_header_rep hdr2 txns2 s2 ->
  map LogCache.transform_token
    (Specs.apply_txns_finished_oracle_is
      (Log.records (Log.current_part hdr1))) ++ l1 =
  map LogCache.transform_token
      (Specs.apply_txns_finished_oracle_is
        (Log.records (Log.current_part hdr2))) ++ l2 ->
  l1 = l2.
Proof.
  unfold Log.log_header_rep, Log.log_rep_general, 
  Log.log_rep_explicit, 
  Log.log_rep_inner,
  Log.header_part_is_valid,
  Log.txns_valid; intros; logic_clean.
  unfold Specs.apply_txns_finished_oracle_is in *.
  repeat rewrite <- H9, <- H21 in *.
  repeat rewrite map_map in *; 
  repeat rewrite map_app in *;
  repeat rewrite <- app_assoc in *.
  cleanup.
  eapply log_lengths_eq_then_oracle_lengths_same_map in H2; eauto.
  simpl in *; cleanup; eauto.

  eapply Forall_forall; intros.
  eapply Forall_forall in H22; eauto.
  unfold Log.txn_well_formed,
  Log.record_is_valid in *; cleanup; eauto.

  eapply Forall_forall; intros.
  eapply Forall_forall in H10; eauto.
  unfold Log.txn_well_formed,
  Log.record_is_valid in *; cleanup; eauto.
Qed.

Lemma log_lengths_eq_then_oracle_lengths_same:
  forall txns1 txns2 l1 l2,
    fold_left PeanoNat.Nat.add (map
      (fun x : Log.txn =>  Log.addr_count (Log.record x) + Log.data_count (Log.record x)) txns1) 0 =
    fold_left PeanoNat.Nat.add (map
      (fun x : Log.txn => Log.addr_count (Log.record x) + Log.data_count (Log.record x)) txns2) 0 ->
  Forall (fun x : Log.txn =>  Log.addr_count (Log.record x) > 0) txns1 ->
  Forall (fun x : Log.txn =>  Log.addr_count (Log.record x) > 0) txns2 ->
  (fold_right
      (app
        (A:=LayerImplementation.token'
              (HorizontalComposition CryptoOperation
                  (DiskOperation addr_dec value
                    (fun a0 : addr => a0 < disk_size))))) []
      (map
        (fun x : Log.txn =>
          Specs.apply_txn_finished_oracle_is
            (Log.addr_count (Log.record x) +
            Log.data_count (Log.record x))
            (Log.data_count (Log.record x))) txns1)) ++ l1 =
      (fold_right
          (app
            (A:=LayerImplementation.token'
                  (HorizontalComposition CryptoOperation
                      (DiskOperation addr_dec value
                        (fun a0 : addr => a0 < disk_size))))) []
          (map
            (fun x : Log.txn =>
              Specs.apply_txn_finished_oracle_is
                (Log.addr_count (Log.record x) +
                Log.data_count (Log.record x))
                (Log.data_count (Log.record x))) txns2)) ++ l2 ->
  l1 = l2.
  Proof.
    induction txns1; destruct txns2; intros.
    rewrite fold_symmetric in H; simpl in *; try lia; eauto.
    rewrite fold_symmetric in H; simpl in *; try lia; eauto.
    inversion H1; subst.
    rewrite Specs.fold_left_add_remove_start in H; simpl in *; try lia.
    rewrite fold_symmetric in H; simpl in *; try lia; eauto.
    inversion H0; subst; lia.

    inversion H0; inversion H1; subst.
    simpl in *.
    rewrite Specs.fold_left_add_remove_start in H; simpl in *; try lia.
    setoid_rewrite Specs.fold_left_add_remove_start in H at 2; simpl in *; try lia.
    repeat rewrite map_app in *.

    unfold Specs.apply_txn_finished_oracle_is in *;
    repeat rewrite map_app in *;
    repeat rewrite <- app_assoc in *;
    simpl in *;
    destruct (PeanoNat.Nat.eq_dec (Log.addr_count (Log.record a) + Log.data_count (Log.record a)) 
    (Log.addr_count (Log.record t) + Log.data_count (Log.record t))); subst; cleanup.
    {
      destruct (PeanoNat.Nat.eq_dec (Log.data_count (Log.record a)) (Log.data_count (Log.record t))); subst; cleanup.
      {
        eapply IHtxns1 in H4; eauto.
        lia.
      }
      {
        exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      exfalso; eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
    }
  Qed.

Lemma apply_txns_finished_oracle_is_length_eq:
  forall hdr1 hdr2 txns1 txns2 s1 s2 l1 l2,
  Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
  Log.log_header_rep hdr1 txns1 s1 ->
  Log.log_header_rep hdr2 txns2 s2 ->
    (Specs.apply_txns_finished_oracle_is
      (Log.records (Log.current_part hdr1))) ++ l1 =
      (Specs.apply_txns_finished_oracle_is
        (Log.records (Log.current_part hdr2))) ++ l2 ->
  l1 = l2.
Proof.
  unfold Log.log_header_rep, Log.log_rep_general, 
  Log.log_rep_explicit, 
  Log.log_rep_inner,
  Log.header_part_is_valid,
  Log.txns_valid; intros; logic_clean.
  unfold Specs.apply_txns_finished_oracle_is in *.
  repeat rewrite <- H9, <- H21 in *.
  repeat rewrite map_map in *; 
  repeat rewrite map_app in *;
  repeat rewrite <- app_assoc in *.
  cleanup.
  eapply log_lengths_eq_then_oracle_lengths_same in H2; eauto.
  simpl in *; cleanup; eauto.

  eapply Forall_forall; intros.
  eapply Forall_forall in H22; eauto.
  unfold Log.txn_well_formed,
  Log.record_is_valid in *; cleanup; eauto.

  eapply Forall_forall; intros.
  eapply Forall_forall in H10; eauto.
  unfold Log.txn_well_formed,
  Log.record_is_valid in *; cleanup; eauto.
Qed.

Lemma write_crashed_oracle_is_1_4_exfalso :
forall o len1 len2 hdr1 hdr2 s1 s2 txns1 txns2,
Log.log_header_rep hdr1 txns1 s1 ->
Log.log_header_rep hdr2 txns2 s2 ->
LogCache.write_crashed_oracle_is_1 o hdr1 len1 ->
LogCache.write_crashed_oracle_is_4 o hdr2 len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_1,
  LogCache.write_crashed_oracle_is_4; intros.
  split_ors; cleanup.
  split_ors; cleanup.
  split_ors; cleanup.
  {
    unfold Specs.read_encrypted_log_crashed_oracle_is in *;
    repeat (intuition; cleanup;
    simpl in *; cleanup); try congruence; try lia;
    repeat rewrite <- app_assoc in *;
    fold LogCache.transform_token in *;
    rewrite <- app_nil_r in *;
    try eapply_fresh map_transform_token_ext_prefix in H4; cleanup;
    repeat rewrite <- app_assoc in *.
    {
      unfold BatchOperations.batch_operations_disk_crashed_oracle_is in *;
      repeat (intuition; cleanup;
      simpl in *; cleanup).
      {
        
        repeat rewrite <- app_assoc in *; simpl in *;
        eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto;
        congruence.
      }
      {
        repeat rewrite <- app_assoc in *; simpl in *;
        eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto;
        congruence.
      }
      {
        unfold BatchOperations.rec_oracle_finished_disk in *.
        repeat rewrite <- app_assoc in *;
        repeat rewrite repeat_map in *; simpl in *.
        destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
        {
          repeat rewrite <- app_assoc in *; simpl in *;
          eapply rec_oracle_op_2_2_le_exfalso; eauto; congruence.
        }
        {
          apply PeanoNat.Nat.lt_gt_cases in n;
          split_ors; try lia;
          repeat rewrite <- app_assoc in *; simpl in *;
          eapply rec_oracle_op_1_disk_ne_exfalso; eauto; congruence.
        }
      }
    }
    {
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup);
        repeat rewrite <- app_assoc in *.
        {
          destruct (PeanoNat.Nat.eq_dec x1 (Log.count (Log.current_part hdr2))); subst; cleanup.
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
          repeat rewrite repeat_map in *; simpl in *; cleanup.
          eapply rec_oracle_finished_crypto_op1_crypto_ne_exfalso; eauto; congruence.
        }
        {
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
          repeat rewrite repeat_map in *; simpl in *; cleanup.
        }
        {
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
          repeat rewrite repeat_map in *; simpl in *; cleanup.
          repeat rewrite <- app_assoc in *.
          eapply rec_oracle_op_2_2_le_exfalso; eauto; congruence.
        }
      }
      {
          eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      eapply_fresh map_transform_token_ext_prefix in H2; cleanup;
      repeat rewrite <- app_assoc in *; simpl  in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
    {
      eapply_fresh map_transform_token_ext_prefix in H2; cleanup;
      repeat rewrite <- app_assoc in *; simpl  in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  {
    unfold Specs.apply_log_crashed_oracle_is_2,
    Specs.flush_txns_crashed_oracle_is_2 in *;
    repeat (intuition; cleanup;
    simpl in *; cleanup); try congruence; try lia.
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.
        eapply apply_txns_finished_oracle_is_length_eq_map in H4; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H4; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.

        eapply apply_txns_finished_oracle_is_length_eq_map in H4; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H4; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.

        eapply apply_txns_finished_oracle_is_length_eq_map in H4; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H4; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
      
    }
  }
  {
    fold LogCache.transform_token in *.
    repeat rewrite map_app in *; 
    repeat rewrite <- app_assoc in *; cleanup.
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); 
    subst; cleanup.
    {
      unfold Specs.flush_txns_finished_oracle_is in *;
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *; cleanup. 
      eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto;
      simpl in *; cleanup.
      eapply_fresh map_transform_token_ext in H4 ; subst;
      eapply commit_crashed_oracle_is_1_4_exfalso; eauto.
    }
    {
      eapply map_transform_token_ext_prefix in H5; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  split_ors; cleanup.
  split_ors; cleanup.
  split_ors; cleanup.
  {
    unfold Specs.read_encrypted_log_crashed_oracle_is in *;
    repeat (intuition; cleanup;
    simpl in *; cleanup); try congruence; try lia;
    repeat rewrite <- app_assoc in *;
    fold LogCache.transform_token in *;
    rewrite <- app_nil_r in *;
    try eapply_fresh map_transform_token_ext_prefix in H4; cleanup;
    repeat rewrite <- app_assoc in *.
    {
      unfold BatchOperations.batch_operations_disk_crashed_oracle_is in *;
      repeat (intuition; cleanup;
      simpl in *; cleanup).
      {
        
        repeat rewrite <- app_assoc in *; simpl in *;
        eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto;
        congruence.
      }
      {
        repeat rewrite <- app_assoc in *; simpl in *;
        eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto;
        congruence.
      }
      {
        unfold BatchOperations.rec_oracle_finished_disk in *.
        repeat rewrite <- app_assoc in *;
        repeat rewrite repeat_map in *; simpl in *.
        destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
        {
          repeat rewrite <- app_assoc in *; simpl in *;
          eapply rec_oracle_op_2_2_le_exfalso; eauto; congruence.
        }
        {
          apply PeanoNat.Nat.lt_gt_cases in n;
          split_ors; try lia;
          repeat rewrite <- app_assoc in *; simpl in *;
          eapply rec_oracle_op_1_disk_ne_exfalso; eauto; congruence.
        }
      }
    }
    {
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup);
        repeat rewrite <- app_assoc in *.
        {
          destruct (PeanoNat.Nat.eq_dec x1 (Log.count (Log.current_part hdr2))); subst; cleanup.
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
          repeat rewrite repeat_map in *; simpl in *; cleanup.
          eapply rec_oracle_finished_crypto_op1_crypto_ne_exfalso; eauto; congruence.
        }
        {
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
          repeat rewrite repeat_map in *; simpl in *; cleanup.
        }
        {
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
          repeat rewrite repeat_map in *; simpl in *; cleanup.
          repeat rewrite <- app_assoc in *.
          eapply rec_oracle_op_2_2_le_exfalso; eauto; congruence.
        }
      }
      {
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      eapply_fresh map_transform_token_ext_prefix in H2; cleanup;
      repeat rewrite <- app_assoc in *; simpl  in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
    {
      eapply_fresh map_transform_token_ext_prefix in H2; cleanup;
      repeat rewrite <- app_assoc in *; simpl  in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  {
    unfold Specs.apply_log_crashed_oracle_is_2,
    Specs.flush_txns_crashed_oracle_is_2 in *;
    repeat (intuition; cleanup;
    simpl in *; cleanup); try congruence; try lia.
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.

        eapply apply_txns_finished_oracle_is_length_eq_map in H4; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H4; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.

        eapply apply_txns_finished_oracle_is_length_eq_map in H4; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H4; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.

        eapply apply_txns_finished_oracle_is_length_eq_map in H4; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H4; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
      
    }
  }
  {
    fold LogCache.transform_token in *.
    repeat rewrite map_app in *; simpl in *;
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
    {
      unfold Specs.flush_txns_finished_oracle_is in *;
      repeat (intuition; cleanup;
      simpl in *; cleanup); try congruence; try lia.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.

      eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto;
      simpl in *; cleanup.
      erewrite <- app_nil_r in H4.
      eapply_fresh map_transform_token_ext_prefix in H4; cleanup.
      symmetry in H1;
      eapply commit_finished_crashed_1_exfalso; eauto.
    }
    {
      eapply map_transform_token_ext_prefix in H5; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  split_ors; cleanup.
  split_ors; cleanup.
  {
    unfold Specs.read_encrypted_log_crashed_oracle_is in *;
    repeat (intuition; cleanup;
    simpl in *; cleanup); try congruence; try lia;
    repeat rewrite <- app_assoc in *;
    fold LogCache.transform_token in *;
    rewrite <- app_nil_r in *;
    try eapply_fresh map_transform_token_ext_prefix in H5; cleanup;
    repeat rewrite <- app_assoc in *.
    {
      unfold BatchOperations.batch_operations_disk_crashed_oracle_is in *;
      repeat (intuition; cleanup;
      simpl in *; cleanup).
      {
        
        repeat rewrite <- app_assoc in *; simpl in *;
        eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto;
        congruence.
      }
      {
        repeat rewrite <- app_assoc in *; simpl in *;
        eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto;
        congruence.
      }
      {
        unfold BatchOperations.rec_oracle_finished_disk in *.
        repeat rewrite <- app_assoc in *;
        repeat rewrite repeat_map in *; simpl in *.
        destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
        {
          repeat rewrite <- app_assoc in *; simpl in *;
          eapply rec_oracle_op_2_2_le_exfalso; eauto; congruence.
        }
        {
          apply PeanoNat.Nat.lt_gt_cases in n;
          split_ors; try lia;
          repeat rewrite <- app_assoc in *; simpl in *;
          eapply rec_oracle_op_1_disk_ne_exfalso; eauto; congruence.
        }
      }
    }
    {
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup);
        repeat rewrite <- app_assoc in *.
        {
          destruct (PeanoNat.Nat.eq_dec x3 (Log.count (Log.current_part hdr2))); subst; cleanup.
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
          repeat rewrite repeat_map in *; simpl in *; cleanup.
          eapply rec_oracle_finished_crypto_op1_crypto_ne_exfalso; eauto; congruence.
        }
        {
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
          repeat rewrite repeat_map in *; simpl in *; cleanup.
        }
        {
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
          repeat rewrite repeat_map in *; simpl in *; cleanup.
          repeat rewrite <- app_assoc in *.
          eapply rec_oracle_op_2_2_le_exfalso; eauto; congruence.
        }
      }
      {
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      eapply_fresh map_transform_token_ext_prefix in H2; cleanup;
      repeat rewrite <- app_assoc in *; simpl  in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
    {
      eapply_fresh map_transform_token_ext_prefix in H2; cleanup;
      repeat rewrite <- app_assoc in *; simpl  in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  {
    unfold Specs.apply_log_crashed_oracle_is_2,
    Specs.flush_txns_crashed_oracle_is_2 in *;
    repeat (intuition; cleanup;
    simpl in *; cleanup); try congruence; try lia.
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.

        eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H5; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.

        eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H5; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.

        eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H5; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
      
    }
  }
  {
    fold LogCache.transform_token in *.
    repeat rewrite map_app in *; simpl in *;
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
    {
      unfold Specs.flush_txns_finished_oracle_is in *;
      repeat (intuition; cleanup;
      simpl in *; cleanup); try congruence; try lia.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      eapply apply_txns_finished_oracle_is_length_eq_map in H6; eauto;
      simpl in *; cleanup.
      erewrite <- app_nil_r in H5.
      eapply_fresh map_transform_token_ext_prefix in H5; cleanup.
      symmetry in H1;
      eapply commit_finished_crashed_1_exfalso; eauto.
    }
    {
      eapply map_transform_token_ext_prefix in H6; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  Unshelve.
  constructor.
  Qed. 
  Lemma map_transform_token_ext_one_sided:
  forall l1 l2 l3,
  map LogCache.transform_token l1 = map LogCache.transform_token l2 ++ l3 ->
  exists l4, l1 = l2 ++ l4.
  Proof.
    induction l1; destruct l2; simpl; intros; eauto; try congruence.
    inversion H. eapply IHl1 in H2.
    cleanup.
    unfold LogCache.transform_token in *; cleanup; try congruence;
    intuition eauto.
    inversion H1;
    intuition eauto.
  Qed.
          
Lemma write_crashed_oracle_is_1_3_exfalso :
forall o len1 len2 hdr1 hdr2 s1 s2 txns1 txns2,
Log.log_header_rep hdr1 txns1 s1 ->
Log.log_header_rep hdr2 txns2 s2 ->
LogCache.write_crashed_oracle_is_1 o hdr1 len1 ->
LogCache.write_crashed_oracle_is_3 o hdr2 len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_1,
  LogCache.write_crashed_oracle_is_3; intros.
  split_ors; cleanup.
  split_ors; cleanup.
  {
    unfold Specs.read_encrypted_log_crashed_oracle_is in *;
    repeat (intuition; cleanup;
    simpl in *; cleanup); try congruence; try lia;
    repeat rewrite <- app_assoc in *;
    fold LogCache.transform_token in *;
    try eapply_fresh map_transform_token_ext_one_sided in H4; cleanup;
    repeat rewrite <- app_assoc in *.
    {
      unfold BatchOperations.batch_operations_disk_crashed_oracle_is in *;
      repeat (intuition; cleanup;
      simpl in *; cleanup).
      {
        repeat rewrite <- app_assoc in *; simpl in *;
        eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto;
        congruence.
      }
      {
        repeat rewrite <- app_assoc in *; simpl in *;
        eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto;
        congruence.
      }
      {
        unfold BatchOperations.rec_oracle_finished_disk in *.
        repeat rewrite <- app_assoc in *;
        repeat rewrite repeat_map in *; simpl in *.
        destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
        {
          repeat rewrite <- app_assoc in *; simpl in *;
          eapply rec_oracle_op_2_2_le_exfalso; eauto; congruence.
        }
        {
          apply PeanoNat.Nat.lt_gt_cases in n;
          split_ors; try lia;
          repeat rewrite <- app_assoc in *; simpl in *;
          eapply rec_oracle_op_1_disk_ne_exfalso; eauto; congruence.
        }
      }
    }
    {
      
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup);
        repeat rewrite <- app_assoc in *.
        {
          destruct (PeanoNat.Nat.eq_dec x1 (Log.count (Log.current_part hdr2))); subst; cleanup.
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
        repeat rewrite repeat_map in *; simpl in *; cleanup.
        eapply rec_oracle_finished_crypto_op1_crypto_ne_exfalso; eauto; congruence.
        }
        {
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
        repeat rewrite repeat_map in *; simpl in *; cleanup.
        }
        {
          unfold BatchOperations.rec_oracle_finished_crypto in *; 
          repeat rewrite <- app_assoc in *;
          repeat rewrite repeat_map in *; simpl in *; cleanup.
          repeat rewrite <- app_assoc in *.
          eapply rec_oracle_op_2_2_le_exfalso; eauto; congruence.
        }
      }
      {
          eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      eapply_fresh map_transform_token_ext_one_sided in H2; cleanup;
      repeat rewrite <- app_assoc in *; simpl  in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
    {
      eapply_fresh map_transform_token_ext_one_sided in H2; cleanup;
      repeat rewrite <- app_assoc in *; simpl  in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  {
    unfold Specs.apply_log_crashed_oracle_is_2,
    Specs.flush_txns_crashed_oracle_is_2 in *;
    repeat (intuition; cleanup;
    simpl in *; cleanup); try congruence; try lia.
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.        
        eapply apply_txns_finished_oracle_is_length_eq_map in H4; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H4; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.
        eapply apply_txns_finished_oracle_is_length_eq_map in H4; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H4; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
      {
        unfold Specs.flush_txns_finished_oracle_is in *;
        repeat (intuition; cleanup;
        simpl in *; cleanup); try congruence; try lia.
        repeat rewrite map_app in *; simpl in *;
        repeat rewrite <- app_assoc in *.
        eapply apply_txns_finished_oracle_is_length_eq_map in H4; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H4; cleanup.
        eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
      
    }
  }
  {
    fold LogCache.transform_token in *.
    repeat rewrite map_app in *; 
    repeat rewrite <- app_assoc in *; cleanup.
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); 
    subst; cleanup.
    {
      unfold Specs.flush_txns_finished_oracle_is in *;
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *; cleanup. 
      eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto;
      simpl in *; cleanup.
      eapply_fresh map_transform_token_ext in H2; subst;
      eapply commit_crashed_oracle_is_1_3_exfalso; eauto.
    }
    {
      eapply map_transform_token_ext_prefix in H5; cleanup.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  Unshelve. 
  constructor.
Qed.


Lemma write_crashed_oracle_is_1_commit_crashed_oracle_is_3_exfalso :
forall o len1 len2 hdr,
LogCache.write_crashed_oracle_is_1 (map LogCache.transform_token o) hdr len1 ->
Specs.commit_crashed_oracle_is_3 o len2 ->
False.
Proof.
unfold LogCache.write_crashed_oracle_is_1,
Specs.commit_crashed_oracle_is_3,
Specs.commit_txn_crashed_oracle_is_3; intros; 
repeat (intuition; cleanup;
simpl in *; cleanup).
Qed.

Lemma write_crashed_oracle_is_3_commit_crashed_oracle_is_3_exfalso :
forall o len1 len2 hdr,
LogCache.write_crashed_oracle_is_3 (map LogCache.transform_token o) hdr len1 ->
Specs.commit_crashed_oracle_is_3 o len2 ->
False.
Proof.
unfold LogCache.write_crashed_oracle_is_3,
Specs.commit_crashed_oracle_is_3,
Specs.commit_txn_crashed_oracle_is_3; intros; 
  repeat (intuition; cleanup;
simpl in *; cleanup).
Qed.

Lemma commit_finished_crashed_2_exfalso :
forall o1 o2 l1 l2 len1 len2,
o1 ++ l1 = o2 ++ l2 ->
Specs.commit_crashed_oracle_is_2 o1 len1 ->
Specs.commit_finished_oracle_is_true o2 len2 ->
False.
  Proof.
    unfold Specs.commit_finished_oracle_is_true, 
    Specs.commit_crashed_oracle_is_2; intros.
    cleanup; simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup.

    unfold Specs.commit_txn_crashed_oracle_is_2 in *.
    repeat split_ors; cleanup; simpl in *; cleanup.
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
    {
      unfold BatchOperations.batch_operations_disk_crashed_oracle_is in *.
      repeat split_ors; cleanup; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *.
      {
        destruct (PeanoNat.Nat.eq_dec x3 len2); subst; cleanup.
        {
          unfold BatchOperations.rec_oracle_finished_disk in *;
          rewrite <- app_assoc in *; cleanup.
          simpl in *; cleanup.
        }
        {
          eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; congruence.
        }
      }
      {
        
          unfold BatchOperations.rec_oracle_finished_disk in *;
          rewrite <- app_assoc in *; cleanup;
          simpl in *; cleanup.
      }
      {
        
          unfold BatchOperations.rec_oracle_finished_disk in *;
          repeat rewrite <- app_assoc in *; cleanup;
          simpl in *; cleanup.
          repeat rewrite <- app_assoc in *.
          eapply rec_oracle_op_2_2_le_exfalso; eauto; congruence.
      }
      {
        cleanup; simpl in *; cleanup.
      }
      {
        cleanup; simpl in *; cleanup.
      }
      {
        cleanup; simpl in *; cleanup.
      }
    }
    {
      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
    }
  Qed.

Lemma commit_finished_crashed_3_exfalso :
forall o1 o2 l1 l2 len1 len2,
o1 ++ l1 = o2 ++ l2 ->
Specs.commit_crashed_oracle_is_3 o1 len1 ->
Specs.commit_finished_oracle_is_true o2 len2 ->
False.
  Proof.
    unfold Specs.commit_finished_oracle_is_true, 
    Specs.commit_crashed_oracle_is_3; intros.
    cleanup; simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup.

    unfold Specs.commit_txn_crashed_oracle_is_3 in *.
    repeat split_ors; cleanup; simpl in *; cleanup.
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
    {
      unfold BatchOperations.batch_operations_disk_crashed_oracle_is in *.
      repeat split_ors; cleanup; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *.
    }
    {
      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
    }
  Qed.

Lemma write_crashed_oracle_is_4_5_exfalso :
forall o len1 hdr1 hdr2 s1 s2 txns1 txns2,
Log.log_header_rep hdr1 txns1 s1 ->
Log.log_header_rep hdr2 txns2 s2 ->
LogCache.write_crashed_oracle_is_4 o hdr1 len1 ->
LogCache.write_crashed_oracle_is_5 o hdr2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_4,
  LogCache.write_crashed_oracle_is_5; intros.
  split_ors; cleanup;
  fold LogCache.transform_token in *.
  {
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
    {
      unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *;
      repeat (intuition; cleanup;
      simpl in *; cleanup);
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *;
      cleanup.
      unfold Specs.flush_txns_finished_oracle_is in *; cleanup.
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *.
      eapply apply_txns_finished_oracle_is_length_eq_map in H4; eauto.
      simpl in *; cleanup.
    }
    {
      eapply map_transform_token_ext_prefix in H4; cleanup.
      repeat rewrite <- app_assoc in *.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  split_ors; cleanup;
  fold LogCache.transform_token in *.
  {
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
    {
      unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *;
      repeat (intuition; cleanup;
      simpl in *; cleanup);
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *;
      cleanup.
      unfold Specs.flush_txns_finished_oracle_is in *; cleanup.
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *.
      eapply apply_txns_finished_oracle_is_length_eq_map in H4; eauto.
      simpl in *; cleanup.
    }
    {
      eapply map_transform_token_ext_prefix in H4; cleanup.
      repeat rewrite <- app_assoc in *.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  {
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
    {
      unfold BatchOperations.batch_operations_crypto_crashed_oracle_is in *;
      repeat (intuition; cleanup;
      simpl in *; cleanup);
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *;
      cleanup.
      unfold Specs.flush_txns_finished_oracle_is in *; cleanup.
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *.
      eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto.
      simpl in *; cleanup.
    }
    {
      repeat rewrite <- app_assoc in *.
      eapply map_transform_token_ext_prefix in H5; cleanup.
      repeat rewrite <- app_assoc in *.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  Qed.

Lemma commit_crashed_oracle_is_2_4_exfalso:
forall o1 o2 len1 len2 l1 l2, 
o1 ++ l1 =
o2 ++ l2 ->
Specs.commit_crashed_oracle_is_2 o1 len1 ->
Specs.commit_crashed_oracle_is_4 o2 len2 ->
False.
Proof.
  unfold Specs.commit_crashed_oracle_is_2,
  Specs.commit_crashed_oracle_is_4; intros.
  cleanup; repeat split_ors; cleanup; 
  simpl in *; cleanup.
  unfold Specs.commit_txn_crashed_oracle_is_2 in *.
  cleanup; repeat split_ors; cleanup;
  simpl in *; cleanup.
  {
    unfold BatchOperations.batch_operations_disk_crashed_oracle_is in *.
    simpl in *; cleanup.
    repeat rewrite map_app in *; simpl in *;
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
    {
      repeat split_ors; cleanup; simpl in *; cleanup;
      rewrite <- app_assoc in *; cleanup;
      simpl in *; cleanup.
      {
        destruct (PeanoNat.Nat.eq_dec x3 len2); subst.
        {
          unfold BatchOperations.rec_oracle_finished_disk in *;
          rewrite <- app_assoc in *; cleanup.
          simpl in *; cleanup.
        }
        {
          eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; congruence.
        }
      }
      {
        unfold BatchOperations.rec_oracle_finished_disk in *;
        rewrite <- app_assoc in *; cleanup.
        simpl in *; cleanup.
      }
      {
        unfold BatchOperations.rec_oracle_finished_disk in *;
        repeat rewrite <- app_assoc in *; cleanup.
        simpl in *; cleanup.
        eapply rec_oracle_op_2_2_le_exfalso; eauto; congruence.
      }
    }
    {
      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
    }
  }
  {
    repeat rewrite map_app in *; simpl in *;
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec len1 len2); subst; simpl in *; cleanup.
    eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
  }
  {
    repeat rewrite map_app in *; simpl in *;
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec len1 len2); subst; simpl in *; cleanup.
    eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
  }
  {
    repeat rewrite map_app in *; simpl in *;
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec len1 len2); subst; simpl in *; cleanup.
    eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
  }
  Qed.


Lemma write_crashed_oracle_is_2_4_exfalso :
forall o len1 len2 hdr1 hdr2 s1 s2 txns1 txns2,
Log.log_header_rep hdr1 txns1 s1 ->
Log.log_header_rep hdr2 txns2 s2 ->
LogCache.write_crashed_oracle_is_2 o hdr1 len1 ->
LogCache.write_crashed_oracle_is_4 o hdr2 len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_2,
  LogCache.write_crashed_oracle_is_4; intros.
  split_ors; cleanup;
  fold LogCache.transform_token in *.
  {
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
    {
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *;
      cleanup.
      unfold Specs.flush_txns_finished_oracle_is in *; cleanup.
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *.
      eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto.
      simpl in *; cleanup.
      eapply map_transform_token_ext in H2; subst.
      eapply commit_crashed_oracle_is_2_4_exfalso; eauto.
    }
    {
      eapply map_transform_token_ext_prefix in H5; cleanup.
      repeat rewrite <- app_assoc in *.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  split_ors; cleanup;
  fold LogCache.transform_token in *.
  {
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
    {
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *;
      cleanup.
      unfold Specs.flush_txns_finished_oracle_is in *; cleanup.
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *.
      eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto.
      simpl in *; cleanup.
      rewrite <- app_nil_r in H4 at 1.
      eapply map_transform_token_ext_prefix in H4; cleanup.
      eapply commit_finished_crashed_2_exfalso; eauto.
    }
    {
      eapply map_transform_token_ext_prefix in H5; cleanup.
      repeat rewrite <- app_assoc in *.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  {
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
    {
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *;
      cleanup.
      unfold Specs.flush_txns_finished_oracle_is in *; cleanup.
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *.
      eapply apply_txns_finished_oracle_is_length_eq_map in H6; eauto.
      simpl in *; cleanup.
      repeat rewrite <- app_assoc in *;
      rewrite <- app_nil_r in H5 at 1.
      eapply map_transform_token_ext_prefix in H5; cleanup.
      eapply commit_finished_crashed_2_exfalso; eauto.
    }
    {
      repeat rewrite <- app_assoc in *.
      eapply map_transform_token_ext_prefix in H6; cleanup.
      repeat rewrite <- app_assoc in *.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  Unshelve.
  constructor.
  Qed.

Lemma commit_crashed_oracle_is_3_4_exfalso:
  forall o1 o2 len1 len2 l1 l2, 
  o1 ++ l1 = o2 ++ l2 ->
  Specs.commit_crashed_oracle_is_3 o1 len1 ->
  Specs.commit_crashed_oracle_is_4 o2 len2 ->
  False.
  Proof.
    unfold Specs.commit_crashed_oracle_is_3,
    Specs.commit_crashed_oracle_is_4; intros.
    cleanup; repeat split_ors; cleanup; 
    simpl in *; cleanup.
    unfold Specs.commit_txn_crashed_oracle_is_3 in *.
    cleanup; repeat split_ors; cleanup;
    simpl in *; cleanup.
    {
      unfold BatchOperations.batch_operations_disk_crashed_oracle_is in *.
      simpl in *; cleanup.
      repeat rewrite map_app in *; simpl in *;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
      {
        repeat split_ors; cleanup; simpl in *; cleanup;
        rewrite <- app_assoc in *; cleanup;
        simpl in *; cleanup.
      }
      {
        eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
      }
    }
    Qed.

Lemma write_crashed_oracle_is_3_4_exfalso :
forall o len1 len2 hdr1 hdr2 s1 s2 txns1 txns2,
Log.log_header_rep hdr1 txns1 s1 ->
Log.log_header_rep hdr2 txns2 s2 ->
LogCache.write_crashed_oracle_is_3 o hdr1 len1 ->
LogCache.write_crashed_oracle_is_4 o hdr2 len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_3,
  LogCache.write_crashed_oracle_is_4; intros.
  split_ors; cleanup;
  fold LogCache.transform_token in *.
  {
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
    {
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *;
      cleanup.
      unfold Specs.flush_txns_finished_oracle_is in *; cleanup.
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *.
      eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto.
      simpl in *; cleanup.
      eapply map_transform_token_ext in H2; subst.
      eapply commit_crashed_oracle_is_3_4_exfalso; eauto.
    }
    {
      eapply map_transform_token_ext_prefix in H5; cleanup.
      repeat rewrite <- app_assoc in *.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  split_ors; cleanup;
  fold LogCache.transform_token in *.
  {
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
    {
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *;
      cleanup.
      unfold Specs.flush_txns_finished_oracle_is in *; cleanup.
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *.
      eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto.
      simpl in *; cleanup.
      rewrite <- app_nil_r in H4 at 1.
      eapply map_transform_token_ext_prefix in H4; cleanup.
      eapply commit_finished_crashed_3_exfalso; eauto.
    }
    {
      eapply map_transform_token_ext_prefix in H5; cleanup.
      repeat rewrite <- app_assoc in *.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  {
    destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
    {
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *;
      cleanup.
      unfold Specs.flush_txns_finished_oracle_is in *; cleanup.
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *.
      eapply apply_txns_finished_oracle_is_length_eq_map in H6; eauto.
      simpl in *; cleanup.
      repeat rewrite <- app_assoc in *;
      rewrite <- app_nil_r in H5 at 1.
      eapply map_transform_token_ext_prefix in H5; cleanup.
      eapply commit_finished_crashed_3_exfalso; eauto.
    }
    {
      repeat rewrite <- app_assoc in *.
      eapply map_transform_token_ext_prefix in H6; cleanup.
      repeat rewrite <- app_assoc in *.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
  }
  Unshelve.
  constructor.
  Qed.

Lemma write_crashed_oracle_is_4_commit_crashed_oracle_is_3_exfalso :
forall o len1 len2 hdr,
LogCache.write_crashed_oracle_is_4 (map LogCache.transform_token o) hdr len1 ->
Specs.commit_crashed_oracle_is_3 o len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_4,
  Specs.commit_crashed_oracle_is_3,
    Specs.commit_txn_crashed_oracle_is_3; intros; 
    repeat (intuition; cleanup;
  simpl in *; cleanup).
Qed.

Lemma write_crashed_oracle_is_4_commit_crashed_oracle_is_2_exfalso :
forall o len1 len2 hdr,
LogCache.write_crashed_oracle_is_4 (map LogCache.transform_token o) hdr len1 ->
Specs.commit_crashed_oracle_is_2 o len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_4,
  Specs.commit_crashed_oracle_is_2,
    Specs.commit_txn_crashed_oracle_is_2; intros; 
    repeat (intuition; cleanup;
  simpl in *; cleanup).
Qed.

Lemma commit_crashed_oracle_is_2_3_exfalso:
forall o1 o2 len1 len2 l1 l2, 
o1 ++ l1 =
o2 ++ l2 ->
Specs.commit_crashed_oracle_is_2 o1 len1 ->
Specs.commit_crashed_oracle_is_3 o2 len2 ->
False.
Proof.
  unfold Specs.commit_crashed_oracle_is_2,
  Specs.commit_crashed_oracle_is_3; intros.
  cleanup; repeat split_ors; cleanup; 
  simpl in *; cleanup.
  unfold Specs.commit_txn_crashed_oracle_is_2,
  Specs.commit_txn_crashed_oracle_is_3 in *.
  cleanup; repeat split_ors; cleanup;
  simpl in *; cleanup.
  {
    unfold BatchOperations.batch_operations_disk_crashed_oracle_is in *.
    simpl in *; cleanup.
    repeat rewrite map_app in *; simpl in *;
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec len1 len2); subst; cleanup.
    {
      repeat split_ors; cleanup; simpl in *; cleanup;
      rewrite <- app_assoc in *; cleanup;
      simpl in *; cleanup.
      {
        destruct (PeanoNat.Nat.eq_dec x4 len2); subst.
        {
          unfold BatchOperations.rec_oracle_finished_disk in *;
          rewrite <- app_assoc in *; cleanup.
          simpl in *; cleanup.
        }
        {
          eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; congruence.
        }
      }
      {
        unfold BatchOperations.rec_oracle_finished_disk in *;
        rewrite <- app_assoc in *; cleanup.
        simpl in *; cleanup.
      }
      {
        unfold BatchOperations.rec_oracle_finished_disk in *;
        repeat rewrite <- app_assoc in *; cleanup.
        simpl in *; cleanup.
        eapply rec_oracle_op_2_2_le_exfalso; eauto; congruence.
      }
    }
    {
      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
    }
  }
  {
    repeat rewrite map_app in *; simpl in *;
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec len1 len2); subst; simpl in *; cleanup.
    eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
  }
  {
    repeat rewrite map_app in *; simpl in *;
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec len1 len2); subst; simpl in *; cleanup.
    eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
  }
  {
    repeat rewrite map_app in *; simpl in *;
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec len1 len2); subst; simpl in *; cleanup.
    eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
  }
  Qed.

Lemma write_crashed_oracle_is_3_commit_crashed_oracle_is_2_exfalso :
forall o len1 len2 hdr,
LogCache.write_crashed_oracle_is_3 (map LogCache.transform_token o) hdr len1 ->
Specs.commit_crashed_oracle_is_2 o len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_3,
  Specs.commit_crashed_oracle_is_2,
    Specs.commit_txn_crashed_oracle_is_2; intros; 
    repeat (intuition; cleanup;
  simpl in *; cleanup).
Qed.

Lemma write_crashed_oracle_is_2_commit_crashed_oracle_is_4_exfalso :
forall o len1 len2 hdr,
LogCache.write_crashed_oracle_is_2 (map LogCache.transform_token o) hdr len1 ->
Specs.commit_crashed_oracle_is_4 o len2 ->
False.
Proof.
  unfold LogCache.write_crashed_oracle_is_2,
  Specs.commit_crashed_oracle_is_4,
    Specs.commit_txn_crashed_oracle_is_2; intros; 
    repeat (intuition; cleanup;
  simpl in *; cleanup).
Qed.

Lemma write_crashed_oracle_is_3_commit_crashed_oracle_is_4_exfalso :
  forall o len1 len2 hdr,
  LogCache.write_crashed_oracle_is_3 (map LogCache.transform_token o) hdr len1 ->
  Specs.commit_crashed_oracle_is_4 o len2 ->
  False.
  Proof.
    unfold LogCache.write_crashed_oracle_is_3,
    Specs.commit_crashed_oracle_is_4,
      Specs.commit_txn_crashed_oracle_is_3; intros; 
      repeat (intuition; cleanup;
    simpl in *; cleanup).
  Qed.

  Lemma write_crashed_oracle_is_2_commit_crashed_oracle_is_3_exfalso :
  forall o len1 len2 hdr,
  LogCache.write_crashed_oracle_is_2 (map LogCache.transform_token o) hdr len1 ->
  Specs.commit_crashed_oracle_is_3 o len2 ->
  False.
  Proof.
    unfold LogCache.write_crashed_oracle_is_2,
    Specs.commit_crashed_oracle_is_3,
      Specs.commit_txn_crashed_oracle_is_3; intros; 
      repeat (intuition; cleanup;
    simpl in *; cleanup).
  Qed.

Lemma write_crashed_oracle_is_2_3_exfalso :
forall o len1 len2 hdr1 hdr2 s1 s2 txns1 txns2,
Log.log_header_rep hdr1 txns1 s1 ->
Log.log_header_rep hdr2 txns2 s2 ->
LogCache.write_crashed_oracle_is_2 o hdr1 len1 ->
LogCache.write_crashed_oracle_is_3 o hdr2 len2 ->
False.
Proof.
unfold LogCache.write_crashed_oracle_is_3,
LogCache.write_crashed_oracle_is_2; intros.
cleanup;
fold LogCache.transform_token in *.
{
destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; cleanup.
{
  repeat rewrite map_app in *;
  repeat rewrite <- app_assoc in *;
  cleanup.
  unfold Specs.flush_txns_finished_oracle_is in *; cleanup.
  repeat rewrite map_app in *;
  repeat rewrite <- app_assoc in *.
  eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto.
  simpl in *; cleanup.
  eapply map_transform_token_ext in H2; subst.
  eapply commit_crashed_oracle_is_2_3_exfalso; eauto.
}
{
  eapply map_transform_token_ext_prefix in H5; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply rec_oracle_finished_disk_ne_exfalso; eauto.
}
}
Unshelve.
constructor.
Qed.

Lemma write_crashed_oracle_is_3_5_exfalso :
forall o len1 hdr1 hdr2 s1 s2 txns1 txns2,
Log.log_header_rep hdr1 txns1 s1 ->
Log.log_header_rep hdr2 txns2 s2 ->
LogCache.write_crashed_oracle_is_3 o hdr1 len1 ->
LogCache.write_crashed_oracle_is_5 o hdr2 ->
False.
Proof.
    intros;
    unfold LogCache.write_crashed_oracle_is_3 ,
    LogCache.write_crashed_oracle_is_5 ,
    Specs.commit_crashed_oracle_is_3,
    Specs.commit_txn_crashed_oracle_is_3  in *; cleanup;
    repeat split_ors; simpl in *; cleanup;
    fold LogCache.transform_token in *;
    repeat rewrite <- app_assoc in *; 
    simpl in *; cleanup.
    {
      repeat rewrite <- app_assoc in *;
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
      subst; cleanup; try lia.
      {
        repeat rewrite map_app in *; simpl in *; 
        repeat rewrite <- app_assoc in *; simpl in *;
        cleanup.
        unfold Specs.flush_txns_crashed_oracle_is_3,
        Specs.flush_txns_finished_oracle_is  in *;
        repeat rewrite map_app in *;
        repeat rewrite <- app_assoc in *;
        cleanup.
        eapply apply_txns_finished_oracle_is_length_eq_map in H2; eauto;
        simpl in *; cleanup.
      }
      {
        eapply map_transform_token_ext_prefix in H3; cleanup.
        repeat rewrite <- app_assoc in *.
        exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    Qed.

    Lemma fold_right_apply_txn_finished_oracle_is_txns_same_structure:
    forall l1 l2 l3 l4,
    fold_right
   (app
       (A:=LayerImplementation.token'
             (HorizontalComposition CryptoOperation
               (DiskOperation addr_dec value
                   (fun a0 : addr => a0 < disk_size))))) []
   (map
       (fun rec : Log.txn_record =>
       Specs.apply_txn_finished_oracle_is
         (Log.addr_count rec + Log.data_count rec) 
         (Log.data_count rec))
       l1) ++ l3 =
    fold_right
      (app
          (A:=LayerImplementation.token'
                (HorizontalComposition CryptoOperation
                  (DiskOperation addr_dec value
                      (fun a0 : addr => a0 < disk_size))))) []
      (map
          (fun txn : Log.txn_record =>
          Specs.apply_txn_finished_oracle_is
            (Log.addr_count txn + Log.data_count txn) 
            (Log.data_count txn)) l2) ++ l4 ->
    (*
    Forall (fun a => Log.addr_count a > 0) l1 ->
    Forall (fun a => Log.addr_count a > 0) l2 -> 
    *)
    Forall2 (fun r1 r2 => (Log.addr_count r1 = Log.addr_count r2 /\
    Log.data_count r1 = Log.data_count r2 ))
    (firstn (Nat.min (length l1) (length l2)) l1)
    (firstn (Nat.min (length l1) (length l2)) l2).
    Proof.
    induction l1; simpl; intros; try congruence.
    econstructor.
    destruct l2; simpl in *.
    econstructor.
    unfold Specs.apply_txn_finished_oracle_is in *.
    repeat rewrite <- app_assoc in *.
    destruct (PeanoNat.Nat.eq_dec (Log.addr_count a + Log.data_count a) (Log.addr_count t + Log.data_count t));
    subst; cleanup.
    {
    destruct (PeanoNat.Nat.eq_dec (Log.data_count a) (Log.data_count t));
    subst; cleanup.
    econstructor; try lia.
    eapply IHl1; eauto.
    exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    }
    {
    exfalso; eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
    }
    Qed.

    Lemma fold_right_apply_txn_finished_oracle_is_exfalso:
           forall l1 l2 l3 x,
           fold_right
       (app
          (A:=LayerImplementation.token'
                (HorizontalComposition CryptoOperation
                   (DiskOperation addr_dec value
                      (fun a0 : addr => a0 < disk_size))))) []
       (map
          (fun rec : Log.txn_record =>
           Specs.apply_txn_finished_oracle_is
             (Log.addr_count rec + Log.data_count rec) 
             (Log.data_count rec))
          l1) =
     fold_right
       (app
          (A:=LayerImplementation.token'
                (HorizontalComposition CryptoOperation
                   (DiskOperation addr_dec value
                      (fun a0 : addr => a0 < disk_size))))) []
       (map
          (fun txn : Log.txn_record =>
           Specs.apply_txn_finished_oracle_is
             (Log.addr_count txn + Log.data_count txn) 
             (Log.data_count txn)) l2) ++ x :: l3 ->
     Forall (fun a => Log.addr_count a > 0) l1 ->
     Forall (fun a => Log.addr_count a > 0) l2 ->
     x <> (OpToken
     (HorizontalComposition CryptoOperation
        (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
     (Token1 CryptoOperation
        (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size))
        CryptoLayer.Cont)) ->
     False.
     induction l1; simpl; intros; try congruence.
     eapply app_cons_not_nil; eauto.
     inversion H0; subst.
     destruct l2; simpl in *.
     unfold Specs.apply_txn_finished_oracle_is,
     BatchOperations.rec_oracle_finished_crypto,
     BatchOperations.rec_oracle_op1_crypto in *.
     destruct (Log.addr_count a); simpl in *; try lia; cleanup;try congruence.

     inversion H1; cleanup.
     unfold Specs.apply_txn_finished_oracle_is in *.
     repeat rewrite <- app_assoc in *.
     destruct (PeanoNat.Nat.eq_dec (Log.addr_count a + Log.data_count a) (Log.addr_count t + Log.data_count t));
     subst; cleanup.
     {
      destruct (PeanoNat.Nat.eq_dec (Log.data_count a) (Log.data_count t));
      subst; cleanup.
      eapply IHl1; eauto.
      eapply rec_oracle_finished_disk_ne_exfalso; eauto.
     }
     {
      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
     }
     Qed.

     Lemma fold_right_app_app:
      forall T (l1 l2: (list (list T))) l,
      fold_right (@app T) l (l1++l2) = fold_right (@app T) [] l1 ++ fold_right (@app T) l l2.
      Proof.
        induction l1; simpl in *; intros; eauto.
        rewrite <- app_assoc, IHl1; eauto.
      Qed.

      Lemma fold_right_app_length_eq:
      forall l1 l2,
      Forall2
      (fun r1 r2  =>
      Log.addr_count r1 = Log.addr_count r2 /\ Log.data_count r1 = Log.data_count r2)
      l1 l2 ->
      length
      (fold_right
      (app
      (A:=LayerImplementation.token'
            (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size))))) []
      (map
      (fun txn : Log.txn_record =>
      Specs.apply_txn_finished_oracle_is (Log.addr_count txn + Log.data_count txn)
        (Log.data_count txn)) l1)) =
      length
      (fold_right
      (app
      (A:=LayerImplementation.token'
            (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size))))) []
      (map
      (fun rec : Log.txn_record =>
      Specs.apply_txn_finished_oracle_is (Log.addr_count rec + Log.data_count rec)
        (Log.data_count rec))
      l2)).
      Proof.
        induction l1; destruct l2; simpl in *; intros; eauto;
        inversion H; cleanup.
        repeat rewrite app_length; eauto.
      Qed.

    Lemma write_crashed_oracle_is_4_apply_log_crashed_oracle_is_1_exfalso:
    forall o len hdr1 hdr2 s1 s2 txns1 txns2 n,
    Log.log_header_rep hdr1 txns1 s1 ->
    Log.log_header_rep hdr2 txns2 s2 ->
    LogCache.write_crashed_oracle_is_4
      (OpToken
         (HorizontalComposition (CacheOperation addr_dec value)
            CryptoDiskOperation)
         (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
            (Token2 CryptoOperation
               (DiskOperation addr_dec value (fun a : addr => a < disk_size))
               DiskLayer.Cont))
       :: LayerImplementation.Cont
            (HorizontalComposition (CacheOperation addr_dec value)
               CryptoDiskOperation)
          :: LayerImplementation.Cont
               (HorizontalComposition (CacheOperation addr_dec value)
                  CryptoDiskOperation) :: map LogCache.transform_token o)
      hdr1 len ->
      Specs.apply_log_crashed_oracle_is_1 o hdr2 n ->
    False.
    Proof.
    (*LogCache.write_crashed_oracle_is_4
    Specs.apply_log_crashed_oracle_is_1*)
    intros;
    unfold LogCache.write_crashed_oracle_is_4 in *; cleanup.
    split_ors; cleanup; 
    repeat rewrite <- app_assoc in *;
    simpl in *; cleanup.
    {
      unfold Specs.apply_log_crashed_oracle_is_1 in *; cleanup;
      repeat split_ors; cleanup;
      simpl in *; cleanup;
      fold LogCache.transform_token in *.
      {
        eapply_fresh map_transform_token_ext_one_sided in H4; cleanup;
        repeat rewrite <- app_assoc in *.
        destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
        subst; simpl in *; cleanup; try lia.
        {
          repeat rewrite map_app in *; simpl in *; 
          repeat rewrite <- app_assoc in *; simpl in *;
          cleanup.
          unfold Specs.flush_txns_crashed_oracle_is_1,
          Specs.flush_txns_finished_oracle_is  in *;
          repeat rewrite <- app_assoc in *;
          cleanup.
          split_ors; cleanup.
          repeat rewrite map_app in *;
          repeat rewrite <- app_assoc in *;
          eapply apply_txns_finished_oracle_is_length_eq in H1; eauto;
          simpl in *; cleanup.

          repeat rewrite map_app in *;
          repeat rewrite <- app_assoc in *;
          eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto;
          simpl in *; cleanup.
          unfold Specs.apply_txns_crashed_oracle_is,
          Specs.apply_txns_finished_oracle_is in *; cleanup; simpl in *;
          repeat rewrite <- app_assoc in *.
          eapply_fresh fold_right_apply_txn_finished_oracle_is_txns_same_structure in H1.
          destruct (Compare_dec.lt_dec (length (Log.records (Log.current_part hdr1)))
          (length (firstn x0 (Log.records (Log.current_part hdr2))))).
          {
            rewrite min_l in Hx; eauto; try lia.
            rewrite firstn_exact in *.
            rewrite firstn_firstn in Hx.
            rewrite min_l in Hx.
            2: rewrite firstn_length in l; lia.
            rewrite <- firstn_skipn with (n:= length (Log.records (Log.current_part hdr1))) 
            (l:= (firstn x0 (Log.records (Log.current_part hdr2)))) in H1.
            rewrite map_app, fold_right_app_app in H1; simpl in *;
            repeat rewrite <- app_assoc in *.
            eapply app_split_length_eq_l in H1.
            cleanup.
            admit. (*Solvable*)
            rewrite firstn_firstn.
            rewrite min_l.
            2: rewrite firstn_length in l; lia.
            apply fold_right_app_length_eq; eauto.
          }
          {
            eapply PeanoNat.Nat.nlt_ge in n0.
            rewrite min_r in Hx; eauto; try lia.
            rewrite firstn_exact in *.
            eapply PeanoNat.Nat.le_lteq in n0.
            split_ors; subst; cleanup.
            {
              rewrite <- firstn_skipn with (n:= length (firstn x0 (Log.records (Log.current_part hdr2)))) 
              (l:= Log.records (Log.current_part hdr1)) in H1.

              rewrite map_app, fold_right_app_app in H1; simpl in *;
              repeat rewrite <- app_assoc in *.
              eapply app_split_length_eq_l in H1.
              cleanup.
              split_ors; cleanup.
              {
                unfold Specs.apply_txn_crashed_oracle_is in *; simpl in *;
                repeat split_ors; cleanup.
                {
                  unfold BatchOperations.batch_operations_crypto_crashed_oracle_is,
                  BatchOperations.rec_oracle_op1_crypto in *;
                  repeat rewrite <- app_assoc in *; simpl in *; 
                  repeat (try split_ors; cleanup).
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                    (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct x2; simpl in *; cleanup.
                    repeat rewrite <- app_assoc in *.
                    unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_crypto,
                      BatchOperations.rec_oracle_op1_crypto in *;
                      repeat rewrite <- app_assoc in *; simpl in *.

                    destruct (PeanoNat.Nat.eq_dec x2 (Log.addr_count t + Log.data_count t)); subst; cleanup.
                    admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H8; eauto.
                      congruence.
                        admit. (*Solvable*)
                  }
                }
                {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_disk in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                        destruct (PeanoNat.Nat.eq_dec (Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                           {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H7; eauto; try congruence.
                      eapply PeanoNat.Nat.lt_gt_cases in n;
                      split_ors;
                      eapply rec_oracle_op_1_disk_ne_exfalso in H6; eauto; try lia;
                      try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
              }
              {
                unfold Specs.apply_txn_crashed_oracle_is in *; simpl in *;
                repeat split_ors; cleanup.
                {
                  unfold BatchOperations.batch_operations_crypto_crashed_oracle_is,
                  BatchOperations.rec_oracle_op1_crypto in *;
                  repeat rewrite <- app_assoc in *; simpl in *; 
                  repeat (try split_ors; cleanup).
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                    (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct n; simpl in *; cleanup.
                    repeat rewrite <- app_assoc in *.
                    unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_crypto,
                      BatchOperations.rec_oracle_op1_crypto in *;
                      repeat rewrite <- app_assoc in *; simpl in *.

                    destruct (PeanoNat.Nat.eq_dec n (Log.addr_count t + Log.data_count t)); subst; cleanup.
                    admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H8; eauto.
                      congruence.
                        admit. (*Solvable*)
                  }
                }
                {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_disk in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                        destruct (PeanoNat.Nat.eq_dec (Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                           {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H7; eauto; try congruence.
                      eapply PeanoNat.Nat.lt_gt_cases in n;
                      split_ors;
                      eapply rec_oracle_op_1_disk_ne_exfalso in H6; eauto; try lia;
                      try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
              }
              eapply fold_right_app_length_eq; eauto.
            }
            {
              rewrite firstn_exact in Hx.
              eapply_fresh fold_right_app_length_eq in Hx.
              unfold Log.log_header_rep, Log.log_rep_general,
              Log.log_rep_explicit, Log.log_rep_inner,
              Log.header_part_is_valid, Log.txns_valid in *; logic_clean.
              repeat rewrite <- H12, <- H24 in *.
              rewrite firstn_map in *.
              repeat rewrite map_map in *.
              repeat rewrite fold_right_app_length in Hx0.
              repeat rewrite map_map in Hx0.
              eapply log_lengths_eq_then_oracle_lengths_same in H1; simpl in *; try congruence.
            }
          }
        }
        {
          eapply rec_oracle_finished_disk_ne_exfalso; eauto.
        }
      }
    }
    split_ors; cleanup; 
    repeat rewrite <- app_assoc in *;
    simpl in *; cleanup.
    {
      unfold Specs.apply_log_crashed_oracle_is_1 in *; cleanup;
      repeat split_ors; cleanup;
      simpl in *; cleanup;
      fold LogCache.transform_token in *.
      {
        eapply_fresh map_transform_token_ext_one_sided in H4; cleanup;
        repeat rewrite <- app_assoc in *.
        destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
        subst; simpl in *; cleanup; try lia.
        {
          repeat rewrite map_app in *; simpl in *; 
          repeat rewrite <- app_assoc in *; simpl in *;
          cleanup.
          unfold Specs.flush_txns_crashed_oracle_is_1,
          Specs.flush_txns_finished_oracle_is  in *;
          repeat rewrite <- app_assoc in *;
          cleanup.
          split_ors; cleanup.
          repeat rewrite map_app in *;
          repeat rewrite <- app_assoc in *;
          eapply apply_txns_finished_oracle_is_length_eq in H1; eauto;
          simpl in *; cleanup.

          repeat rewrite map_app in *;
          repeat rewrite <- app_assoc in *;
          eapply apply_txns_finished_oracle_is_length_eq_map in H5; eauto;
          simpl in *; cleanup.
          unfold Specs.apply_txns_crashed_oracle_is,
          Specs.apply_txns_finished_oracle_is in *; cleanup; simpl in *;
          repeat rewrite <- app_assoc in *.
          eapply_fresh fold_right_apply_txn_finished_oracle_is_txns_same_structure in H1.
          destruct (Compare_dec.lt_dec (length (Log.records (Log.current_part hdr1)))
          (length (firstn x0 (Log.records (Log.current_part hdr2))))).
          {
            rewrite min_l in Hx; eauto; try lia.
            rewrite firstn_exact in *.
            rewrite firstn_firstn in Hx.
            rewrite min_l in Hx.
            2: rewrite firstn_length in l; lia.
            rewrite <- firstn_skipn with (n:= length (Log.records (Log.current_part hdr1))) 
            (l:= (firstn x0 (Log.records (Log.current_part hdr2)))) in H1.
            rewrite map_app, fold_right_app_app in H1; simpl in *;
            repeat rewrite <- app_assoc in *.
            eapply app_split_length_eq_l in H1.
            cleanup.
            admit. (*Solvable*)
            rewrite firstn_firstn.
            rewrite min_l.
            2: rewrite firstn_length in l; lia.
            apply fold_right_app_length_eq; eauto.
          }
          {
            eapply PeanoNat.Nat.nlt_ge in n0.
            rewrite min_r in Hx; eauto; try lia.
            rewrite firstn_exact in *.
            eapply PeanoNat.Nat.le_lteq in n0.
            split_ors; subst; cleanup.
            {
              rewrite <- firstn_skipn with (n:= length (firstn x0 (Log.records (Log.current_part hdr2)))) 
              (l:= Log.records (Log.current_part hdr1)) in H1.

              rewrite map_app, fold_right_app_app in H1; simpl in *;
              repeat rewrite <- app_assoc in *.
              eapply app_split_length_eq_l in H1.
              cleanup.
              split_ors; cleanup.
              {
                unfold Specs.apply_txn_crashed_oracle_is in *; simpl in *;
                repeat split_ors; cleanup.
                {
                  unfold BatchOperations.batch_operations_crypto_crashed_oracle_is,
                  BatchOperations.rec_oracle_op1_crypto in *;
                  repeat rewrite <- app_assoc in *; simpl in *; 
                  repeat (try split_ors; cleanup).
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                    (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct x2; simpl in *; cleanup.
                    repeat rewrite <- app_assoc in *.
                    unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_crypto,
                      BatchOperations.rec_oracle_op1_crypto in *;
                      repeat rewrite <- app_assoc in *; simpl in *.

                    destruct (PeanoNat.Nat.eq_dec x2 (Log.addr_count t + Log.data_count t)); subst; cleanup.
                    admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H8; eauto.
                      congruence.
                        admit. (*Solvable*)
                  }
                }
                {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_disk in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                        destruct (PeanoNat.Nat.eq_dec (Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                           {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H7; eauto; try congruence.
                      eapply PeanoNat.Nat.lt_gt_cases in n;
                      split_ors;
                      eapply rec_oracle_op_1_disk_ne_exfalso in H6; eauto; try lia;
                      try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
              }
              {
                unfold Specs.apply_txn_crashed_oracle_is in *; simpl in *;
                repeat split_ors; cleanup.
                {
                  unfold BatchOperations.batch_operations_crypto_crashed_oracle_is,
                  BatchOperations.rec_oracle_op1_crypto in *;
                  repeat rewrite <- app_assoc in *; simpl in *; 
                  repeat (try split_ors; cleanup).
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                    (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct n; simpl in *; cleanup.
                    repeat rewrite <- app_assoc in *.
                    unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_crypto,
                      BatchOperations.rec_oracle_op1_crypto in *;
                      repeat rewrite <- app_assoc in *; simpl in *.

                    destruct (PeanoNat.Nat.eq_dec n (Log.addr_count t + Log.data_count t)); subst; cleanup.
                    admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H8; eauto.
                      congruence.
                        admit. (*Solvable*)
                  }
                }
                {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x0 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x0
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_disk in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                        destruct (PeanoNat.Nat.eq_dec (Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x0
                           {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H7; eauto; try congruence.
                      eapply PeanoNat.Nat.lt_gt_cases in n;
                      split_ors;
                      eapply rec_oracle_op_1_disk_ne_exfalso in H6; eauto; try lia;
                      try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
              }
              eapply fold_right_app_length_eq; eauto.
            }
            {
              rewrite firstn_exact in Hx.
              eapply_fresh fold_right_app_length_eq in Hx.
              unfold Log.log_header_rep, Log.log_rep_general,
              Log.log_rep_explicit, Log.log_rep_inner,
              Log.header_part_is_valid, Log.txns_valid in *; logic_clean.
              repeat rewrite <- H12, <- H24 in *.
              rewrite firstn_map in *.
              repeat rewrite map_map in *.
              repeat rewrite fold_right_app_length in Hx0.
              repeat rewrite map_map in Hx0.
              eapply log_lengths_eq_then_oracle_lengths_same in H1; simpl in *; try congruence.
            }
          }
        }
        {
          eapply rec_oracle_finished_disk_ne_exfalso; eauto.
        }
      }
    }
    {
      unfold Specs.apply_log_crashed_oracle_is_1 in *; cleanup;
      repeat split_ors; cleanup;
      simpl in *; cleanup;
      fold LogCache.transform_token in *.
      {
        eapply_fresh map_transform_token_ext_one_sided in H5; cleanup;
        repeat rewrite <- app_assoc in *.
        destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
        subst; simpl in *; cleanup; try lia.
        {
          repeat rewrite map_app in *; simpl in *; 
          repeat rewrite <- app_assoc in *; simpl in *;
          cleanup.
          unfold Specs.flush_txns_crashed_oracle_is_1,
          Specs.flush_txns_finished_oracle_is  in *;
          repeat rewrite <- app_assoc in *;
          cleanup.
          split_ors; cleanup.
          repeat rewrite map_app in *;
          repeat rewrite <- app_assoc in *;
          eapply apply_txns_finished_oracle_is_length_eq in H1; eauto;
          simpl in *; cleanup.

          repeat rewrite map_app in *;
          repeat rewrite <- app_assoc in *;
          eapply apply_txns_finished_oracle_is_length_eq_map in H6; eauto;
          simpl in *; cleanup.
          unfold Specs.apply_txns_crashed_oracle_is,
          Specs.apply_txns_finished_oracle_is in *; cleanup; simpl in *;
          repeat rewrite <- app_assoc in *.
          eapply_fresh fold_right_apply_txn_finished_oracle_is_txns_same_structure in H1.
          destruct (Compare_dec.lt_dec (length (Log.records (Log.current_part hdr1)))
          (length (firstn x2 (Log.records (Log.current_part hdr2))))).
          {
            rewrite min_l in Hx; eauto; try lia.
            rewrite firstn_exact in *.
            rewrite firstn_firstn in Hx.
            rewrite min_l in Hx.
            2: rewrite firstn_length in l; lia.
            rewrite <- firstn_skipn with (n:= length (Log.records (Log.current_part hdr1))) 
            (l:= (firstn x2 (Log.records (Log.current_part hdr2)))) in H1.
            rewrite map_app, fold_right_app_app in H1; simpl in *;
            repeat rewrite <- app_assoc in *.
            eapply app_split_length_eq_l in H1.
            cleanup.
            admit. (*Solvable*)
            rewrite firstn_firstn.
            rewrite min_l.
            2: rewrite firstn_length in l; lia.
            apply fold_right_app_length_eq; eauto.
          }
          {
            eapply PeanoNat.Nat.nlt_ge in n0.
            rewrite min_r in Hx; eauto; try lia.
            rewrite firstn_exact in *.
            eapply PeanoNat.Nat.le_lteq in n0.
            split_ors; subst; cleanup.
            {
              rewrite <- firstn_skipn with (n:= length (firstn x2 (Log.records (Log.current_part hdr2)))) 
              (l:= Log.records (Log.current_part hdr1)) in H1.

              rewrite map_app, fold_right_app_app in H1; simpl in *;
              repeat rewrite <- app_assoc in *.
              eapply app_split_length_eq_l in H1.
              cleanup.
              split_ors; cleanup.
              {
                unfold Specs.apply_txn_crashed_oracle_is in *; simpl in *;
                repeat split_ors; cleanup.
                {
                  unfold BatchOperations.batch_operations_crypto_crashed_oracle_is,
                  BatchOperations.rec_oracle_op1_crypto in *;
                  repeat rewrite <- app_assoc in *; simpl in *; 
                  repeat (try split_ors; cleanup).
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                    (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct x4; simpl in *; cleanup.
                    repeat rewrite <- app_assoc in *.
                    unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_crypto,
                      BatchOperations.rec_oracle_op1_crypto in *;
                      repeat rewrite <- app_assoc in *; simpl in *.

                    destruct (PeanoNat.Nat.eq_dec x2 (Log.addr_count t + Log.data_count t)); subst; cleanup.
                    admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H9; eauto.
                      congruence.
                      admit. (*Solvable*)
                  }
                }
                {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_disk in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                        destruct (PeanoNat.Nat.eq_dec (Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                           {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H8; eauto; try congruence.
                      eapply PeanoNat.Nat.lt_gt_cases in n;
                      split_ors;
                      eapply rec_oracle_op_1_disk_ne_exfalso in H7; eauto; try lia;
                      try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
              }
              {
                unfold Specs.apply_txn_crashed_oracle_is in *; simpl in *;
                repeat split_ors; cleanup.
                {
                  unfold BatchOperations.batch_operations_crypto_crashed_oracle_is,
                  BatchOperations.rec_oracle_op1_crypto in *;
                  repeat rewrite <- app_assoc in *; simpl in *; 
                  repeat (try split_ors; cleanup).
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                    (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct n; simpl in *; cleanup.
                    repeat rewrite <- app_assoc in *.
                    unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_crypto,
                      BatchOperations.rec_oracle_op1_crypto in *;
                      repeat rewrite <- app_assoc in *; simpl in *.

                    destruct (PeanoNat.Nat.eq_dec n (Log.addr_count t + Log.data_count t)); subst; cleanup.
                    admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      admit. (*Solvable*)
                  }
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                        BatchOperations.rec_oracle_finished_crypto,
                        BatchOperations.rec_oracle_op1_crypto in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H9; eauto.
                      congruence.
                        admit. (*Solvable*)
                  }
                }
                {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_finished_disk_op1_disk_exfalso; eauto; try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
                  {
                    destruct_fresh (skipn (length (firstn x2 (Log.records (Log.current_part hdr2))))
                          (Log.records (Log.current_part hdr1))); simpl in *; cleanup.
                    destruct (Log.addr_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                    Log.data_count
                    (seln (Log.records (Log.current_part hdr2)) x2
                      {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}));
                      simpl in *; cleanup; try lia.

                      unfold Specs.apply_txn_finished_oracle_is,
                      BatchOperations.rec_oracle_finished_disk in *;
                        repeat rewrite <- app_assoc in *; simpl in *.

                      destruct (PeanoNat.Nat.eq_dec (Log.addr_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |}) +
                      Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                        {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.addr_count t + Log.data_count t)); subst; cleanup.
                        destruct (PeanoNat.Nat.eq_dec (Log.data_count
                      (seln (Log.records (Log.current_part hdr2)) x2
                           {| Log.key := key0; Log.start := 0; Log.addr_count := 0; Log.data_count := 0 |})) (Log.data_count t)); subst; cleanup.
                      eapply rec_oracle_op_2_2_le_exfalso in H8; eauto; try congruence.
                      eapply PeanoNat.Nat.lt_gt_cases in n;
                      split_ors;
                      eapply rec_oracle_op_1_disk_ne_exfalso in H7; eauto; try lia;
                      try congruence.
                      eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
                  }
              }
              eapply fold_right_app_length_eq; eauto.
            }
            {
              rewrite firstn_exact in Hx.
              eapply_fresh fold_right_app_length_eq in Hx.
              unfold Log.log_header_rep, Log.log_rep_general,
              Log.log_rep_explicit, Log.log_rep_inner,
              Log.header_part_is_valid, Log.txns_valid in *; logic_clean.
              repeat rewrite <- H13, <- H25 in *.
              rewrite firstn_map in *.
              repeat rewrite map_map in *.
              repeat rewrite fold_right_app_length in Hx0.
              repeat rewrite map_map in Hx0.
              eapply log_lengths_eq_then_oracle_lengths_same in H1; simpl in *; try congruence.
            }
          }
        }
        {
          eapply rec_oracle_finished_disk_ne_exfalso; eauto.
        }
      }
    }
  Admitted.

Ltac strip_transform_token:=
  match goal with
  | [H: map LogCache.transform_token _ = map LogCache.transform_token _ |- _] =>
      apply map_transform_token_ext in H; subst
  | [H: map LogCache.transform_token _ = map LogCache.transform_token _ ++ _|- _] =>
    rewrite <- app_nil_r in H at 1;  
    apply map_transform_token_ext_prefix in H; logic_clean
  | [H: map LogCache.transform_token _ ++ _ = map LogCache.transform_token _|- _] =>
    rewrite <- app_nil_r in H;  
    apply map_transform_token_ext_prefix in H; logic_clean
  | [H: map LogCache.transform_token _ ++ _ = map LogCache.transform_token _ ++ _|- _] =>
    apply map_transform_token_ext_prefix in H; logic_clean
end.

Ltac solve_write_write_crash_cases :=
  match goal with
  (*| [H: LogCache.write_crashed_oracle_is_1 ?o _ _,
    H0: LogCache.write_crashed_oracle_is_2 ?o _ _,
    H1: Log.log_header_rep _ _ _,
    H2: Log.log_header_rep _ _ _ |- _] =>
      exfalso; eapply write_crashed_oracle_is_1_2_exfalso in H1; eauto*)
  | [H: LogCache.write_crashed_oracle_is_1 ?o _ _,
    H0: LogCache.write_crashed_oracle_is_3 ?o _ _,
    H1: Log.log_header_rep _ _ _,
    H2: Log.log_header_rep _ _ _ |- _] =>
      exfalso; eapply write_crashed_oracle_is_1_3_exfalso in H1; eauto
  | [H: LogCache.write_crashed_oracle_is_1 ?o _ _,
    H0: LogCache.write_crashed_oracle_is_4 ?o _ _,
    H1: Log.log_header_rep _ _ _,
    H2: Log.log_header_rep _ _ _ |- _] =>
      exfalso; eapply write_crashed_oracle_is_1_4_exfalso in H1; eauto  
  (*| [H: LogCache.write_crashed_oracle_is_1 ?o _ _,
    H0: LogCache.write_crashed_oracle_is_5 ?o _ _,
    H1: Log.log_header_rep _ _ _,
    H2: Log.log_header_rep _ _ _ |- _] =>
      exfalso; eapply write_crashed_oracle_is_1_5_exfalso in H1; eauto
  
    | [H: LogCache.write_crashed_oracle_is_2 ?o _ _,
    H0: LogCache.write_crashed_oracle_is_3 ?o _ _,
    H1: Log.log_header_rep _ _ _,
    H2: Log.log_header_rep _ _ _ |- _] =>
     exfalso; eapply write_crashed_oracle_is_2_3_exfalso in H1; eauto*)
  | [H: LogCache.write_crashed_oracle_is_2 ?o _ _,
    H0: LogCache.write_crashed_oracle_is_4 ?o _ _,
    H1: Log.log_header_rep _ _ _,
    H2: Log.log_header_rep _ _ _ |- _] =>
      exfalso; eapply write_crashed_oracle_is_2_4_exfalso in H1; eauto  
  (*| [H: LogCache.write_crashed_oracle_is_2 ?o _ _,
    H0: LogCache.write_crashed_oracle_is_5 ?o _ _,
    H1: Log.log_header_rep _ _ _,
    H2: Log.log_header_rep _ _ _ |- _] =>
      exfalso; eapply write_crashed_oracle_is_2_5_exfalso in H1; eauto*)

  | [H: LogCache.write_crashed_oracle_is_3 ?o _ _,
      H0: LogCache.write_crashed_oracle_is_4 ?o _ _,
      H1: Log.log_header_rep _ _ _,
      H2: Log.log_header_rep _ _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_3_4_exfalso in H1; eauto  
  | [H: LogCache.write_crashed_oracle_is_3 ?o _ _,
      H0: LogCache.write_crashed_oracle_is_5 ?o _ ,
      H1: Log.log_header_rep _ _ _,
      H2: Log.log_header_rep _ _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_3_5_exfalso in H1; eauto

  | [H: LogCache.write_crashed_oracle_is_4 ?o _ _,
      H0: LogCache.write_crashed_oracle_is_5 ?o _,
      H1: Log.log_header_rep _ _ _,
      H2: Log.log_header_rep _ _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_4_5_exfalso in H1; eauto
  end.

Ltac solve_write_commit_crash_cases :=
      match goal with
      (*| [H: Specs.commit_crashed_oracle_is_1 ?o _,
        H0: LogCache.write_crashed_oracle_is_1 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_1_commit_crashed_oracle_is_1_exfalso; eauto
      | [H: Specs.commit_crashed_oracle_is_2 ?o _,
        H0: LogCache.write_crashed_oracle_is_1 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_1_commit_crashed_oracle_is_2_exfalso; eauto*)
      | [H: Specs.commit_crashed_oracle_is_3 ?o _,
        H0: LogCache.write_crashed_oracle_is_1 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_1_commit_crashed_oracle_is_3_exfalso; eauto
      | [H: Specs.commit_crashed_oracle_is_4 ?o _,
        H0: LogCache.write_crashed_oracle_is_1 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_1_commit_crashed_oracle_is_4_exfalso; eauto

      (*| [H: Specs.commit_crashed_oracle_is_1 ?o _,
        H0: LogCache.write_crashed_oracle_is_2 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_2_commit_crashed_oracle_is_1_exfalso; eauto
        | [H: Specs.commit_crashed_oracle_is_2 ?o _,
        H0: LogCache.write_crashed_oracle_is_2 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_2_commit_crashed_oracle_is_2_exfalso; eauto*)
      | [H: Specs.commit_crashed_oracle_is_3 ?o _,
        H0: LogCache.write_crashed_oracle_is_2 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_2_commit_crashed_oracle_is_3_exfalso; eauto
      | [H: Specs.commit_crashed_oracle_is_4 ?o _,
        H0: LogCache.write_crashed_oracle_is_2 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_2_commit_crashed_oracle_is_4_exfalso; eauto
      
      | [H: Specs.commit_crashed_oracle_is_1 ?o _,
        H0: LogCache.write_crashed_oracle_is_3 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_3_commit_crashed_oracle_is_1_exfalso; eauto
      | [H: Specs.commit_crashed_oracle_is_2 ?o _,
        H0: LogCache.write_crashed_oracle_is_3 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_3_commit_crashed_oracle_is_2_exfalso; eauto
      | [H: Specs.commit_crashed_oracle_is_3 ?o _,
        H0: LogCache.write_crashed_oracle_is_3 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_3_commit_crashed_oracle_is_3_exfalso; eauto
      | [H: Specs.commit_crashed_oracle_is_4 ?o _,
        H0: LogCache.write_crashed_oracle_is_3 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_3_commit_crashed_oracle_is_4_exfalso; eauto


      | [H: Specs.commit_crashed_oracle_is_1 ?o _,
        H0: LogCache.write_crashed_oracle_is_4 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_4_commit_crashed_oracle_is_1_exfalso; eauto
      | [H: Specs.commit_crashed_oracle_is_2 ?o _,
        H0: LogCache.write_crashed_oracle_is_4 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_4_commit_crashed_oracle_is_2_exfalso; eauto
      | [H: Specs.commit_crashed_oracle_is_3 ?o _,
        H0: LogCache.write_crashed_oracle_is_4 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_4_commit_crashed_oracle_is_3_exfalso; eauto
      (*| [H: Specs.commit_crashed_oracle_is_4 ?o _,
        H0: LogCache.write_crashed_oracle_is_4 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_4_commit_crashed_oracle_is_4_exfalso; eauto

        | [H: Specs.commit_crashed_oracle_is_1 ?o _,
        H0: LogCache.write_crashed_oracle_is_5 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_5_commit_crashed_oracle_is_1_exfalso; eauto
        | [H: Specs.commit_crashed_oracle_is_2 ?o _,
        H0: LogCache.write_crashed_oracle_is_5 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_5_commit_crashed_oracle_is_2_exfalso; eauto
        | [H: Specs.commit_crashed_oracle_is_3 ?o _,
        H0: LogCache.write_crashed_oracle_is_5 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_5_commit_crashed_oracle_is_3_exfalso; eauto
        | [H: Specs.commit_crashed_oracle_is_4 ?o _,
        H0: LogCache.write_crashed_oracle_is_5 (map LogCache.transform_token ?o) _ _ |- _] =>
        exfalso; eapply write_crashed_oracle_is_5_commit_crashed_oracle_is_4_exfalso; eauto*)
    end.

Ltac solve_commit_commit_crash_cases :=
  match goal with
      (*| [H: Specs.commit_crashed_oracle_is_1 ?o _,
        H0: Specs.commit_crashed_oracle_is_2 ?o _ |- _] =>
        exfalso; eapply commit_crashed_oracle_is_1_2_exfalso; eauto *)
      | [H: Specs.commit_crashed_oracle_is_1 _ _,
        H0: Specs.commit_crashed_oracle_is_3 _ _ |- _] =>
        exfalso; eapply commit_crashed_oracle_is_1_3_exfalso; eauto
      | [H: Specs.commit_crashed_oracle_is_1 _ _,
        H0: Specs.commit_crashed_oracle_is_4 _ _ |- _] =>
        exfalso; eapply commit_crashed_oracle_is_1_4_exfalso; eauto
      
      | [H: Specs.commit_crashed_oracle_is_2 _ _,
        H0: Specs.commit_crashed_oracle_is_3 _ _ |- _] =>
        exfalso; eapply commit_crashed_oracle_is_2_3_exfalso; eauto
      | [H: Specs.commit_crashed_oracle_is_2 _ _,
        H0: Specs.commit_crashed_oracle_is_4 _ _ |- _] =>
        exfalso; eapply commit_crashed_oracle_is_2_4_exfalso; eauto
      
      | [H: Specs.commit_crashed_oracle_is_3 _ _,
        H0: Specs.commit_crashed_oracle_is_4 _ _ |- _] =>
        exfalso; eapply commit_crashed_oracle_is_3_4_exfalso; eauto

      | [H: Specs.commit_finished_oracle_is_true _ _,
        H0: Specs.commit_crashed_oracle_is_1 _ _ |- _] =>
        exfalso; eapply commit_finished_crashed_1_exfalso; eauto
      | [H: Specs.commit_finished_oracle_is_true _ _,
        H0: Specs.commit_crashed_oracle_is_2 _ _ |- _] =>
        exfalso; eapply commit_finished_crashed_2_exfalso; eauto
      | [H: Specs.commit_finished_oracle_is_true _ _,
        H0: Specs.commit_crashed_oracle_is_3 _ _ |- _] =>
        exfalso; eapply commit_finished_crashed_3_exfalso; eauto
end.

Ltac solve_crash_cases:= 
  repeat strip_transform_token; 
  try solve solve_write_write_crash_cases; 
  try solve solve_write_commit_crash_cases;
  try solve solve_commit_commit_crash_cases.

Ltac split_case :=
  split_ors; cleanup; repeat unify_execs;
  repeat unify_execs_prefix; cleanup; eauto; try lia;
  try solve_crash_cases.

Definition valid_selector (selector: @total_mem addr addr_dec nat) 
  (s: @total_mem addr addr_dec (value * list value)) :=
    forall i, selector i <= length (snd (s i)).

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

(*
Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
Forall2 (fun rec1 rec2 => Log.addr_count rec1 = Log.addr_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
Forall2 (fun rec1 rec2 => Log.data_count rec1 = Log.data_count rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
*)
valid_selector selector (snd (snd s1')) ->
valid_selector selector (snd (snd s2')) ->
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
  repeat match goal with
  |[H: exists _, _ |- _] => destruct H
  end.
  specialize H with (1:= H4).
  specialize H0 with (1:= H5).
  
  logic_clean; subst.
  eapply_fresh write_crashed_oracle_eq in H10.
  6: eauto.
  6: eauto.
  all: try solve [intuition eauto].
  cleanup.

  split_case.
  split_case.

  split_case.

  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold Specs.commit_crashed_oracle_is_4 in *; cleanup;
    simpl in *; cleanup.
  }
  split_case.
  { 
    unfold Specs.commit_finished_oracle_is_true in *; cleanup; simpl in *;
    cleanup.
  }
  { 
    unfold Specs.commit_finished_oracle_is_true in *; cleanup;
    simpl in *; cleanup. 
  }
  {
    unfold LogCache.write_crashed_oracle_is_4 in *; cleanup;
    simpl in *; repeat split_ors; cleanup.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold Specs.commit_crashed_oracle_is_3 in *; cleanup;
    simpl in *; cleanup.
  }
  {
    unfold LogCache.write_crashed_oracle_is_3 in *; cleanup;
    simpl in *; cleanup.
  }
  split_case.
  split_case. 
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    exfalso; eapply write_crashed_oracle_is_1_commit_finished_exfalso; eauto.
  }
  {
    exfalso; eapply write_crashed_oracle_is_1_commit_finished_exfalso; eauto.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold Specs.commit_crashed_oracle_is_4 in *; cleanup;
    simpl in *; cleanup.
  }
  split_case.
  {
    unfold Specs.commit_finished_oracle_is_true in *; cleanup;
    simpl in *; cleanup.
  }
  {
    unfold Specs.commit_finished_oracle_is_true in *; cleanup;
    simpl in *; cleanup.
  }
  { (*LogCache.write_crashed_oracle_is_4,
    Specs.apply_log_crashed_oracle_is_3 *)
    unfold LogCache.write_crashed_oracle_is_4,
    Specs.apply_log_crashed_oracle_is_3  in *; cleanup;
    repeat split_ors; cleanup;
    simpl in *; cleanup;
    fold LogCache.transform_token in *.
    {
      eapply_fresh map_transform_token_ext_one_sided in H25; cleanup;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
      subst; cleanup; try lia.
      {
        repeat rewrite map_app in *; simpl in *; 
        repeat rewrite <- app_assoc in *; simpl in *;
        cleanup.
        unfold Specs.flush_txns_crashed_oracle_is_3,
        Specs.flush_txns_finished_oracle_is  in *;
        repeat rewrite <- app_assoc in *;
        cleanup.
        eapply apply_txns_finished_oracle_is_length_eq in H23; eauto;
        simpl in *; cleanup.
      }
      {
        exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      eapply_fresh map_transform_token_ext_one_sided in H25; cleanup;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
      subst; cleanup; try lia.
      {
        repeat rewrite map_app in *; simpl in *; 
        repeat rewrite <- app_assoc in *; simpl in *;
        cleanup.
        unfold Specs.flush_txns_crashed_oracle_is_3,
        Specs.flush_txns_finished_oracle_is  in *;
        repeat rewrite <- app_assoc in *;
        cleanup.
        eapply apply_txns_finished_oracle_is_length_eq in H23; eauto;
        simpl in *; cleanup.
      }
      {
        exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      repeat rewrite <- app_assoc in *;
      eapply_fresh map_transform_token_ext_one_sided in H26; cleanup;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
      subst; cleanup; try lia.
      {
        repeat rewrite map_app in *; simpl in *; 
        repeat rewrite <- app_assoc in *; simpl in *;
        cleanup.
        unfold Specs.flush_txns_crashed_oracle_is_3,
        Specs.flush_txns_finished_oracle_is  in *;
        repeat rewrite <- app_assoc in *;
        cleanup.
        eapply apply_txns_finished_oracle_is_length_eq in H23; eauto;
        simpl in *; cleanup.
      }
      {
        exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold Specs.commit_crashed_oracle_is_3,
    Specs.commit_txn_crashed_oracle_is_3 in *; cleanup;
    repeat split_ors; simpl in *; cleanup. 
  }
  split_case.
  {
    (*unfold LogCache.write_crashed_oracle_is_3
      unfold Specs.apply_log_crashed_oracle_is_3 *)
    unfold LogCache.write_crashed_oracle_is_3 in *; cleanup;
    repeat split_ors; simpl in *; cleanup.
    unfold Specs.apply_log_crashed_oracle_is_3 in *;
    cleanup;
    repeat split_ors; simpl in *; cleanup.
    fold LogCache.transform_token in *.
    {
      repeat rewrite <- app_assoc in *;
      eapply_fresh map_transform_token_ext_one_sided in H33; cleanup;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
      subst; cleanup; try lia.
      {
        repeat rewrite map_app in *; simpl in *; 
        repeat rewrite <- app_assoc in *; simpl in *;
        cleanup.
        unfold Specs.flush_txns_crashed_oracle_is_3,
        Specs.flush_txns_finished_oracle_is  in *;
        repeat rewrite <- app_assoc in *;
        cleanup.
        eapply apply_txns_finished_oracle_is_length_eq in H15; eauto;
        simpl in *; cleanup.
      }
      {
        exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold Specs.commit_crashed_oracle_is_4,
    Specs.commit_txn_crashed_oracle_is_3  in *; cleanup;
    repeat split_ors; simpl in *; cleanup. 
  }
  split_case.
  {
    unfold Specs.commit_finished_oracle_is_true in *; cleanup;
    repeat split_ors; simpl in *; cleanup. 
  }
  {
    unfold Specs.commit_finished_oracle_is_true in *; cleanup;
    repeat split_ors; simpl in *; cleanup. 
  }
  {  
    exfalso; eapply write_crashed_oracle_is_4_apply_log_crashed_oracle_is_1_exfalso in H; eauto.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold Specs.commit_crashed_oracle_is_3,
    Specs.commit_txn_crashed_oracle_is_3  in *; cleanup;
    repeat split_ors; simpl in *; cleanup. 
  }
  split_case.
  { (*LogCache.write_crashed_oracle_is_3
      Specs.apply_log_crashed_oracle_is_1*)
    clear H1 H2.
    unfold LogCache.write_crashed_oracle_is_3 in *; cleanup.
    repeat rewrite <- app_assoc in *;
    simpl in *; cleanup.
    {
      unfold Specs.apply_log_crashed_oracle_is_1 in *; cleanup;
      repeat split_ors; cleanup;
      simpl in *; cleanup;
      fold LogCache.transform_token in *.
      {
        eapply_fresh map_transform_token_ext_one_sided in H15; cleanup;
        repeat rewrite <- app_assoc in *.
        destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
        subst; simpl in *; cleanup; try lia.
        {
          repeat rewrite map_app in *; simpl in *; 
          repeat rewrite <- app_assoc in *; simpl in *;
          cleanup.
          unfold Specs.flush_txns_crashed_oracle_is_1,
          Specs.flush_txns_finished_oracle_is  in *;
          repeat rewrite <- app_assoc in *;
          cleanup.
          split_ors; cleanup.
          repeat rewrite map_app in *;
          repeat rewrite <- app_assoc in *;
          eapply apply_txns_finished_oracle_is_length_eq in H1; eauto;
          simpl in *; cleanup.

          repeat rewrite map_app in *;
          repeat rewrite <- app_assoc in *;
          eapply apply_txns_finished_oracle_is_length_eq_map in H28; eauto;
          simpl in *; cleanup.
          admit.
        }
        {
          exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
        }
      }
    }
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold LogCache.write_crashed_oracle_is_5 ,
    Specs.commit_crashed_oracle_is_4,
    Specs.commit_txn_crashed_oracle_is_3  in *; cleanup;
    repeat split_ors; simpl in *; cleanup. 
  }
  {
    unfold LogCache.write_crashed_oracle_is_5 ,
    Specs.commit_finished_oracle_is_true  in *; cleanup;
    repeat split_ors; simpl in *; cleanup;
    repeat rewrite map_app; simpl in *; cleanup. 
  }
  {
    exfalso; eapply write_crashed_oracle_is_4_5_exfalso in H; eauto.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold LogCache.write_crashed_oracle_is_3 ,
    LogCache.write_crashed_oracle_is_5 ,
    Specs.commit_crashed_oracle_is_3,
    Specs.commit_txn_crashed_oracle_is_3  in *; cleanup;
    repeat split_ors; simpl in *; cleanup. 
  }
  {
    exfalso; eapply write_crashed_oracle_is_3_5_exfalso in H28; eauto.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold Specs.commit_crashed_oracle_is_4 in *; cleanup;
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  {
    unfold Specs.commit_crashed_oracle_is_4 in *; cleanup;
    simpl in *; cleanup.
  }
  {
    unfold Specs.commit_crashed_oracle_is_4 in *; cleanup;
    simpl in *; cleanup.
  }
  {
    unfold LogCache.write_crashed_oracle_is_5, 
    Specs.commit_crashed_oracle_is_4 in *; cleanup;
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold Specs.commit_finished_oracle_is_true  in *; cleanup;
    simpl in *; cleanup.
  }
  split_case.
  {
    symmetry in H0;
    exfalso; eapply commit_finished_crashed_1_exfalso; eauto.
  }
  {
    unfold LogCache.write_crashed_oracle_is_1,
    Specs.commit_finished_oracle_is_true  in *; cleanup;
    simpl in *; cleanup.
    repeat split_ors; cleanup;
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  {
    unfold Specs.commit_finished_oracle_is_true  in *; cleanup;
    simpl in *; cleanup.
  }
  {
    unfold Specs.commit_finished_oracle_is_true  in *; cleanup;
    simpl in *; cleanup.
  }
  {
    unfold LogCache.write_crashed_oracle_is_5,
    Specs.commit_finished_oracle_is_true  in *; cleanup;
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  {
    symmetry in H0; exfalso; eapply commit_finished_crashed_2_exfalso; eauto.
  }
  {
    unfold LogCache.write_crashed_oracle_is_2,
    Specs.commit_finished_oracle_is_true ,
    Specs.commit_crashed_oracle_is_2,
    Specs.commit_txn_crashed_oracle_is_2 in *; cleanup.
    repeat split_ors; cleanup;
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  {
    symmetry in H0; exfalso; eapply commit_finished_crashed_3_exfalso; eauto.
  }
  {
    unfold LogCache.write_crashed_oracle_is_3,
    Specs.commit_finished_oracle_is_true in *; 
    simpl in *; cleanup.
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  {
    symmetry in H32; exfalso; eapply commit_finished_crashed_3_exfalso; eauto.
  }
  split_case.
  {
    unfold LogCache.write_crashed_oracle_is_3,
    Specs.commit_finished_oracle_is_true in *; 
    simpl in *; cleanup.
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold LogCache.write_crashed_oracle_is_3,
    Specs.commit_finished_oracle_is_true in *; 
    simpl in *; cleanup.
    simpl in *; cleanup.
  }
  split_case.
  {
    symmetry in H0; exfalso; eapply commit_finished_crashed_1_exfalso; eauto.
  }
  {
    unfold LogCache.write_crashed_oracle_is_1,
    Specs.commit_finished_oracle_is_true in *; 
    simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup.
  }
  split_case.
  split_case.
  {
    unfold Specs.apply_log_crashed_oracle_is_3,
    Specs.commit_finished_oracle_is_true in *; 
    simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup.
  }
  {
    unfold Specs.apply_log_crashed_oracle_is_1,
    Specs.commit_finished_oracle_is_true in *; 
    simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup.
  }
  {
    unfold LogCache.write_crashed_oracle_is_5, 
    Specs.commit_finished_oracle_is_true in *; 
    simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  {
    symmetry in H0; exfalso; eapply commit_finished_crashed_2_exfalso; eauto.
  }
  {
    unfold LogCache.write_crashed_oracle_is_2, 
    Specs.commit_finished_oracle_is_true in *; 
    simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup.
  }
  split_case.
  split_case.
  {
    symmetry in H0; exfalso; eapply commit_finished_crashed_3_exfalso; eauto.
  }
  {
    unfold LogCache.write_crashed_oracle_is_3, 
    Specs.commit_finished_oracle_is_true in *; 
    simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  {
    symmetry in H33; exfalso; eapply commit_finished_crashed_3_exfalso; eauto.
  }
  split_case.
  {
    unfold LogCache.write_crashed_oracle_is_3, 
    Specs.commit_finished_oracle_is_true in *; 
    simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold LogCache.write_crashed_oracle_is_4, 
    Specs.commit_finished_oracle_is_true in *; 
    simpl in *; cleanup.
    repeat split_ors; cleanup; simpl in *; cleanup.
  }
  split_case.
  {
    exfalso; eapply write_crashed_oracle_is_1_4_exfalso in H22; eauto.
  }
  split_case.
  split_case.
  { (*LogCache.write_crashed_oracle_is_4,
    Specs.apply_log_crashed_oracle_is_3 *)
    unfold LogCache.write_crashed_oracle_is_4,
    Specs.apply_log_crashed_oracle_is_3  in *; cleanup;
    repeat split_ors; cleanup;
    simpl in *; cleanup;
    fold LogCache.transform_token in *.
    {
      eapply_fresh map_transform_token_ext_one_sided in H25; cleanup;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
      subst; cleanup; try lia.
      {
        repeat rewrite map_app in *; simpl in *; 
        repeat rewrite <- app_assoc in *; simpl in *;
        cleanup.
        unfold Specs.flush_txns_crashed_oracle_is_3,
        Specs.flush_txns_finished_oracle_is  in *;
        repeat rewrite <- app_assoc in *;
        cleanup.
        eapply apply_txns_finished_oracle_is_length_eq in H23; eauto;
        simpl in *; cleanup.
      }
      {
        exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      eapply_fresh map_transform_token_ext_one_sided in H25; cleanup;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
      subst; cleanup; try lia.
      {
        repeat rewrite map_app in *; simpl in *; 
        repeat rewrite <- app_assoc in *; simpl in *;
        cleanup.
        unfold Specs.flush_txns_crashed_oracle_is_3,
        Specs.flush_txns_finished_oracle_is  in *;
        repeat rewrite <- app_assoc in *;
        cleanup.
        eapply apply_txns_finished_oracle_is_length_eq in H23; eauto;
        simpl in *; cleanup.
      }
      {
        exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
    {
      repeat rewrite <- app_assoc in *;
      eapply_fresh map_transform_token_ext_one_sided in H26; cleanup;
      repeat rewrite <- app_assoc in *.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2)));
      subst; cleanup; try lia.
      {
        repeat rewrite map_app in *; simpl in *; 
        repeat rewrite <- app_assoc in *; simpl in *;
        cleanup.
        unfold Specs.flush_txns_crashed_oracle_is_3,
        Specs.flush_txns_finished_oracle_is  in *;
        repeat rewrite <- app_assoc in *;
        cleanup.
        eapply apply_txns_finished_oracle_is_length_eq in H23; eauto;
        simpl in *; cleanup.
      }
      {
        exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
      }
    }
  }
  {
    admit. (* write_crashed_oracle_is_4 apply_log_crashed_oracle_is_1 *)
  }
  split_case.
  split_case.
  split_case. 
  {
    exfalso; eapply write_crashed_oracle_is_2_4_exfalso in H21; eauto.
  }
  split_case. 
  split_case.
  {
      exfalso; eapply write_crashed_oracle_is_3_4_exfalso in H21; eauto.
  }
  split_case.
  split_case.
  split_case.
  {
    exfalso; eapply write_crashed_oracle_is_3_4_exfalso in H21; eauto.
  }
  split_case.
  split_case.
  split_case.   
  split_case.
  split_case.
  split_case.
  split_case. 
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold LogCache.write_crashed_oracle_is_2,
    Specs.commit_finished_oracle_is_true in *; cleanup.
    simpl in *; cleanup.
  }
  {
    unfold LogCache.write_crashed_oracle_is_2,
    Specs.commit_finished_oracle_is_true in *; cleanup.
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    exfalso; eapply write_crashed_oracle_is_2_3_exfalso in H19; eauto.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold select_total_mem, select_for_addr in *; simpl in *.
    do 2 cleanup;
    match goal with
    | [H: Log.encode_header _ = Log.encode_header _ |- _] =>
    apply encode_header_extensional in H; congruence
    end.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold LogCache.write_crashed_oracle_is_3,
    Specs.commit_finished_oracle_is_true in *; cleanup.
    simpl in *; cleanup.
  }
  {
    unfold LogCache.write_crashed_oracle_is_3,
    Specs.commit_finished_oracle_is_true in *; cleanup.
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold select_total_mem, select_for_addr in *; simpl in *.
    do 2 cleanup;
    match goal with
    | [H: Log.encode_header _ = Log.encode_header _ |- _] =>
    apply encode_header_extensional in H; congruence
    end.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    Lemma commit_crashed_oracle_is_3_len_eq :
    forall o len1 len2,
    Specs.commit_crashed_oracle_is_3 o len1 ->
    Specs.commit_crashed_oracle_is_3 o len2 ->
    len1 = len2.
    Proof.
      unfold Specs.commit_crashed_oracle_is_3,
      Specs.commit_txn_crashed_oracle_is_3 ; intros; cleanup.
      destruct (PeanoNat.Nat.eq_dec len1 len2); eauto.
      exfalso; eapply rec_oracle_finished_crypto_ne_exfalso; eauto.
    Qed.

    Lemma write_crashed_oracle_is_3_len_eq :
    forall o hdr1 hdr2 len1 len2 txns1 txns2 s1 s2,
    Log.log_header_rep hdr1 txns1 s1 ->
    Log.log_header_rep hdr2 txns2 s2 ->
    LogCache.write_crashed_oracle_is_3 o hdr1 len1 ->
    LogCache.write_crashed_oracle_is_3 o hdr2 len2 ->
    
    len1 = len2 /\ Log.count(Log.current_part hdr1) = Log.count(Log.current_part hdr2).
    Proof.
      unfold LogCache.write_crashed_oracle_is_3; intros; cleanup.
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); 
      subst; cleanup.
      repeat rewrite map_app in *; 
      repeat rewrite <- app_assoc in *; 
      simpl in *; cleanup;
      fold LogCache.transform_token in *.
      repeat rewrite map_app in *; simpl in *; 
      repeat rewrite <- app_assoc in *; simpl in *;
      cleanup.
      unfold Specs.flush_txns_crashed_oracle_is_1,
      Specs.flush_txns_finished_oracle_is  in *;
      repeat rewrite <- app_assoc in *;
      cleanup.
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *;
      eapply apply_txns_finished_oracle_is_length_eq_map in H2; eauto;
      simpl in *; cleanup.
      eapply map_transform_token_ext in H5; subst.
      eapply commit_crashed_oracle_is_3_len_eq in H4; eauto.

      eapply map_transform_token_ext_prefix in H5; cleanup;
      repeat rewrite map_app in *;
      repeat rewrite <- app_assoc in *;
      exfalso; eapply rec_oracle_finished_disk_ne_exfalso; eauto.
    Qed.

      eapply commit_crashed_oracle_is_3_len_eq in H44; eauto.
      repeat rewrite app_length in *.
      erewrite addr_list_to_blocks_length_eq in H44; [| rewrite map_length; eauto].
      setoid_rewrite addr_list_to_blocks_length_eq in H44 at 2; [| rewrite map_length; eauto].
      cleanup; try lia.

      assert (selector (log_start + Log.count (Log.current_part hdr2) + x6) = 1). {
      unfold select_total_mem, select_for_addr in H28; simpl in *.
      edestruct H30; eauto.
      cleanup; eauto.
      
      exfalso; apply H28; eauto.

      destruct_fresh (snd (snd (snd x1) (log_start + Log.count (Log.current_part hdr2) + x6)));
      try setoid_rewrite D0 in H20; simpl in *; try lia.
      destruct l3; simpl in *; try lia.
      rewrite D0 in H28; simpl in *.
      destruct n; simpl in *; eauto.

      exfalso; apply H28; eauto.
      }
      destruct (PeanoNat.Nat.eq_dec (Log.count (Log.current_part hdr1)) (Log.count (Log.current_part hdr2))); subst; try lia.
      {
        edestruct H43; eauto.

        rewrite <- PeanoNat.Nat.add_assoc in H26.
        exfalso; eapply H6; eauto.
        eapply PeanoNat.Nat.lt_le_trans.
        2: apply H39.
        rewrite <- PeanoNat.Nat.add_assoc.
        apply Plus.plus_lt_compat_l.
        erewrite addr_list_to_blocks_length_eq; eauto.
        repeat rewrite map_length; eauto.
        eauto.

        setoid_rewrite PeanoNat.Nat.add_assoc.
        rewrite e; eauto.
        destruct_fresh (snd
        (snd (snd x7)
          (log_start + Log.count (Log.current_part hdr1) +
            x6))); 
        setoid_rewrite D in H45;
        simpl in *; try lia.
        destruct l3; simpl in *; try lia.
        setoid_rewrite D; simpl.
        setoid_rewrite H18.
        rewrite <- H41; eauto.
        unfold select_total_mem, select_for_addr; simpl in *.
        repeat rewrite <- PeanoNat.Nat.add_assoc.
        rewrite PeanoNat.Nat.add_assoc.
        rewrite e, H8.
        rewrite e in D;
        setoid_rewrite D.
        simpl; eauto.
      }
      {
        XXXXXX
        edestruct H43; eauto.

        rewrite <- PeanoNat.Nat.add_assoc in H26.
        exfalso; eapply H6; eauto.
        eapply PeanoNat.Nat.lt_le_trans.
        2: apply H24.
        rewrite <- PeanoNat.Nat.add_assoc.
        apply Plus.plus_lt_compat_l.
        erewrite addr_list_to_blocks_length_eq.
        rewrite H44; eauto.
        repeat rewrite map_length; eauto.
        eauto.
        eauto.

        setoid_rewrite PeanoNat.Nat.add_assoc.
        rewrite H18; eauto.
        destruct_fresh (snd
        (snd (snd x7)
          (log_start + Log.count (Log.current_part hdr1) +
            x6))); 
        setoid_rewrite D in H45;
        simpl in *; try lia.
        destruct l3; simpl in *; try lia.
        setoid_rewrite D; simpl.
        setoid_rewrite H18.
        rewrite <- H41; eauto.
        unfold select_total_mem, select_for_addr; simpl in *.
        repeat rewrite <- PeanoNat.Nat.add_assoc.
        rewrite PeanoNat.Nat.add_assoc.
        rewrite e, H8.
        rewrite e in D;
        setoid_rewrite D.
        simpl; eauto.
      }
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold LogCache.write_crashed_oracle_is_3,
    Specs.commit_finished_oracle_is_true in *; cleanup.
    simpl in *; cleanup.
  }
  {
    unfold LogCache.write_crashed_oracle_is_3,
    Specs.commit_finished_oracle_is_true in *; cleanup.
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    eapply write_crashed_oracle_is_3_len_eq in H26; eauto.
    cleanup.
    repeat rewrite app_length in *.
    erewrite addr_list_to_blocks_length_eq in H26; [| rewrite map_length; eauto].
    setoid_rewrite addr_list_to_blocks_length_eq in H26 at 2; [| rewrite map_length; eauto].
    cleanup; try lia.
     assert (selector (log_start + x6) = 1). {
      unfold select_total_mem, select_for_addr in H28; simpl in *.
      edestruct H28; eauto.
      cleanup; eauto.
      
      exfalso; apply H26; eauto.

      destruct_fresh (snd (snd (snd x1) (log_start + x6)));
      setoid_rewrite D0 in H46; simpl in *; try lia.
      destruct l3; simpl in *; try lia.
      rewrite D0 in H28; simpl in *.
      destruct n; simpl in *; eauto.
      exfalso; apply H28; eauto.
    }

    edestruct H45; eauto.

    exfalso; eapply H6; eauto.
    eapply PeanoNat.Nat.lt_le_trans; eauto.
    destruct_fresh (snd
    (snd (snd x7)
       (log_start + x6))); 
    setoid_rewrite D in H47;
    simpl in *; try lia.
    destruct l3; simpl in *; try lia.
    setoid_rewrite D; simpl.
    setoid_rewrite H46.
    rewrite <- H43; eauto.
    unfold select_total_mem, select_for_addr; simpl in *.
    rewrite H20.
    setoid_rewrite D.
    simpl; eauto.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold  Specs.commit_crashed_oracle_is_3 in *; cleanup;
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  {
    unfold  Specs.commit_crashed_oracle_is_3 in *; cleanup;
    simpl in *; cleanup.
    admit.
  }
  {
    unfold LogCache.write_crashed_oracle_is_5,
     Specs.commit_crashed_oracle_is_3,
     Specs.commit_txn_crashed_oracle_is_3  in *; cleanup;
    simpl in *; cleanup.
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold select_total_mem, select_for_addr in *; simpl in *.
    do 2 cleanup;
    match goal with
    | [H: Log.encode_header _ = Log.encode_header _ |- _] =>
    apply encode_header_extensional in H; congruence
    end.
  }
  split_case.
  split_case.
  split_case.
  {
    admit. (*
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
    *)
  }
  split_case.
  split_case.
  split_case.
  split_case.
  split_case.
  {
    unfold LogCache.write_crashed_oracle_is_3 in *; cleanup. 
  }
  split_case.
  {
    exfalso; eapply write_crashed_oracle_is_1_3_exfalso in H31; eauto. 
  }
  split_case.
  {
    admit.
  }
  
  split_case.
  split_case.
  split_case.
  {
    exfalso; eapply write_crashed_oracle_is_2_3_exfalso in H26; eauto.
  }
  split_case.
  split_case.
  {
    unfold select_total_mem, select_for_addr in *; simpl in *.
    do 2 cleanup;
    match goal with
    | [H: Log.encode_header _ = Log.encode_header _ |- _] =>
    apply encode_header_extensional in H; congruence
    end.
  }
  split_case.
  split_case.
  split_case.
  {
    eapply write_crashed_oracle_is_3_len_eq in H26; eauto.
    cleanup.
    repeat rewrite app_length in *.
    erewrite addr_list_to_blocks_length_eq in H26; [| rewrite map_length; eauto].
    setoid_rewrite addr_list_to_blocks_length_eq in H26 at 2; [| rewrite map_length; eauto].
    cleanup; try lia.

    assert (selector (log_start + x11) = 1). {
      unfold select_total_mem, select_for_addr in H43; simpl in *.
      edestruct H45; eauto.
      cleanup; eauto.
      
      exfalso; apply H43; eauto.
 
       destruct_fresh (snd (snd (snd x6) (log_start + x11)));
      setoid_rewrite D0 in H46; simpl in *; try lia.
      destruct l3; simpl in *; try lia.

      rewrite D0 in H43; simpl in *.
      destruct n; simpl in *; eauto.
      exfalso; apply H43; eauto.
    }

    edestruct H30; eauto.

    exfalso; eapply H9; eauto.
    eapply PeanoNat.Nat.lt_le_trans; eauto.
    destruct_fresh (snd
    (snd (snd x1)
       (log_start + x11))); 
    setoid_rewrite D in H47;
    simpl in *; try lia.
    destruct l3; simpl in *; try lia.
    setoid_rewrite D; simpl.
    setoid_rewrite H46.
    rewrite <- H28; eauto.
    unfold select_total_mem, select_for_addr; simpl in *.
    rewrite H20.
    setoid_rewrite D.
    simpl; eauto.
  }
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
  ATC_have_same_structure p1 p2 u s1a s2a oa1 oa2 ->

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

    eapply_fresh exec_finished_deterministic_prefix in H15; eauto; cleanup.
    eapply_fresh exec_finished_deterministic_prefix in H22; eauto; cleanup.
    repeat unify_execs; cleanup.
    eapply_fresh IHp1 in H8; eauto; subst; cleanup.
    
    repeat rewrite <- app_assoc in *.
    
    eapply_fresh ATCD_exec_lift_finished in H15; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply_fresh ATCD_exec_lift_finished in H22; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    simpl in *; cleanup.

    eapply H in H6; eauto.
    cleanup; eauto.

    repeat unify_execs.
    eapply H17; eauto.

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

ATC_have_same_structure p1 p2 u s1a s2a oa1 oa2 ->
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

    eapply exec_finished_deterministic_prefix in H16; eauto; cleanup.
    repeat unify_execs; cleanup.
    repeat rewrite <- app_assoc in *.
    eapply IHp1; eauto.
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

      eapply_fresh ATCD_oracle_refines_impl_eq in H19. 
      7: eauto.
      all: eauto.
      2: apply TC_oracle_refines_operation_eq.
      cleanup.
      
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


Set Nested Proofs Allowed.
Lemma ATC_have_same_structure_sym:
forall T1 (p1 : ATCLang.(prog) T1) 
T2 (p2 : ATCLang.(prog) T2) u s1 s2 o1 o2,
ATC_have_same_structure p1 p2 u s1 s2 o1 o2 ->
ATC_have_same_structure p2 p1 u s2 s1 o2 o1.
Proof.
induction p1; destruct p2; 
simpl; intros; 
simpl in *; cleanup; eauto.

destruct o3, o4;
simpl in *; cleanup; eauto.

destruct o, o0;
simpl in *; cleanup; eauto.

intuition eauto.
do 4 eexists; 
intuition eauto.
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
  ATC_have_same_structure p1 p2 u s1a s2a oa1 oa2 ->

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
    eapply IHp1; eauto.

    all: try match goal with
    | [H: exec _ _ ?x ?s2 ?p (Finished _ _),
      H0: exec _ _ (?x ++ _) ?s2 ?p (Crashed _) |- _] =>
    exfalso; eapply finished_not_crashed_oracle_prefix in H; [
      eapply H; eauto | rewrite <- app_assoc; eauto ]
    end.

    rewrite <- app_assoc in *.
    eapply exec_finished_deterministic_prefix in H30; eauto; cleanup.
    exfalso; eapply ATCD_oracle_refines_prefix_one_crashed.
    4: eauto.
    6: eauto.
    8: eauto.
    all: eauto.

    rewrite <- app_assoc in *.
    eapply exec_finished_deterministic_prefix in H28; eauto; cleanup.
    exfalso; eapply ATCD_oracle_refines_prefix_one_crashed.
    4: apply H6.
    3: apply H8.
    5: eapply ATC_have_same_structure_sym; eauto.
    all: eauto.

    eapply exec_finished_deterministic_prefix in H36; eauto; cleanup.
    eapply exec_finished_deterministic_prefix in H31; eauto; cleanup.
    repeat unify_execs; cleanup.
    repeat rewrite <- app_assoc in *.
    eapply_fresh ATCD_oracle_refines_impl_eq in H33.
    7: eauto.
    all: eauto.
    cleanup.

    eapply ATCD_exec_lift_finished in H8; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply ATCD_exec_lift_finished in H25; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    simpl in *; cleanup.

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
    all: admit. (* Need a preservation lemma. *)
  }
Unshelve.
all: eauto.
Admitted.



Lemma ATCD_ORS_transfer:
forall (l_selector: list (@total_mem addr addr_dec nat)) 
T (p1 p2: AD.(prog) T)  u u' ex l_o_imp l_o_abs l_o_abs' (s1 s2: state ATCDLang),

ATC_Simulation.not_init p1 ->
ATC_Simulation.not_init p2 ->
(forall s1a s2a o_abs l_o_abs_rest o_abs' l_o_abs_rest', 
  l_o_abs = o_abs :: l_o_abs_rest ->
  l_o_abs' = o_abs' :: l_o_abs_rest' ->
(refines_related ATC_Refinement (AD_related_states u' ex)) s1a s2a ->
((exists s1' s2' r1 r2,
exec ATCLang u o_abs s1a (Simulation.Definitions.compile ATC_Refinement p1) (Finished s1' r1) /\
exec ATCLang u o_abs' s2a (Simulation.Definitions.compile ATC_Refinement p2) (Finished s2' r2)) \/
(exists s1' s2',
exec ATCLang u o_abs s1a (Simulation.Definitions.compile ATC_Refinement p1) (Crashed s1') /\
exec ATCLang u o_abs' s2a (Simulation.Definitions.compile ATC_Refinement p2) (Crashed s2'))) ->
ATC_have_same_structure (Simulation.Definitions.compile ATC_Refinement p1)
(Simulation.Definitions.compile ATC_Refinement p2) u s1a s2a o_abs o_abs') ->

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
    eapply ATCD_oracle_refines_impl_eq in H8.
    6: apply H9.
    all: eauto.
    2: apply TC_oracle_refines_operation_eq.
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
      eapply ATCD_oracle_refines_impl_eq in H8.
      6: apply H9.
      all: eauto.
      2: apply TC_oracle_refines_operation_eq.
      cleanup; eauto.
      all: shelve.
    }
    {
      simpl in *.
      exfalso; eapply ATCD_oracle_refines_prefix_one_crashed.
      3: eauto.
      3: eauto.
      all: eauto.
      all: shelve.
    }
    {
      simpl in *.
      exfalso; eapply ATCD_oracle_refines_prefix_one_crashed.
      3: eauto.
      3: eauto.
      all: eauto.
      all: shelve.
    }
    {
      simpl in *. 
      eapply_fresh ATCD_oracle_refines_impl_eq_crashed in H8.
      8: apply H9.
      all: eauto.
      2: apply TC_oracle_refines_operation_eq.
      2: apply TC_oracle_refines_operation_eq_crashed; eauto.
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
  all: try solve [ 
    apply H1 in H18; eauto; apply ATC_have_same_structure_sym; eauto].
  exact (fun _ => 0).
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
Qed.

Theorem have_same_structure_Transaction_read:
forall u s1 s2 a1 a2 o1 o2 o3 o4,
((exists s1' s2' r1 r2,
exec ATCLang u o1 s1 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.read a1)) (Finished s1' r1) /\
exec ATCLang u o2 s2 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.read a2)) (Finished s2' r2)) \/
(exists s1' s2',
exec ATCLang u o1 s1 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.read a1)) (Crashed s1') /\
exec ATCLang u o2 s2 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.read a2)) (Crashed s2'))) ->
o1 ++ o3 = o2 ++ o4 ->
ATC_have_same_structure
  (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.read a1))
  (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.read a2)) u s1 s2 o1 o2.
Proof.
  unfold Transaction.read; intros.
  split_ors; cleanup.
  {
    repeat (repeat invert_exec; cleanup).
    all: try solve [simpl in *; cleanup].
    {
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat invert_exec; cleanup; simpl; eauto.
    }
    {
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat invert_exec; cleanup;
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      
      simpl; eauto.
      simpl; eauto.
    }
    {
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat invert_exec; cleanup;
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      
      simpl; eauto.
      simpl; eauto.
    }
    {
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat invert_exec; cleanup;
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      
      simpl; eauto.
      simpl; eauto.
    }
    {
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat invert_exec; cleanup;
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      
      simpl; eauto.
      simpl; eauto.
    }
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    eexists _, [], _, [].
    repeat rewrite app_nil_r;
    simpl; intuition eauto.
    repeat invert_exec.

    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].

    simpl; eauto.
    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].

    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].  
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].

    eexists _, [], _, [].
    repeat rewrite app_nil_r;
    simpl; intuition eauto.

    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup];
    simpl; eauto.
    simpl; eauto.
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    simpl; eauto.
    simpl; eauto.

    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    simpl; eauto.
    simpl; eauto.

    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    simpl; eauto.
    simpl; eauto.
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
  }
Qed.
  
Theorem have_same_structure_Transaction_write:
forall u s1 s2 a1 a2 v1 v2 o1 o2 o3 o4,
((exists s1' s2' r1 r2,
exec ATCLang u o1 s1 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.write a1 v1)) (Finished s1' r1) /\
exec ATCLang u o2 s2 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.write a2 v2)) (Finished s2' r2)) \/
(exists s1' s2',
exec ATCLang u o1 s1 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.write a1 v1)) (Crashed s1') /\
exec ATCLang u o2 s2 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.write a2 v2)) (Crashed s2'))) ->
o1 ++ o3 = o2 ++ o4 -> 
ATC_have_same_structure
  (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.write a1 v1))
  (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.write a2 v2)) u s1 s2 o1 o2.
Proof.
  unfold Transaction.write; intros.
  split_ors; cleanup.
  {
    repeat (repeat invert_exec; cleanup).
    all: try solve [simpl in *; cleanup].
    {
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat invert_exec; cleanup;
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      simpl; eauto.
    }
    {
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat invert_exec; cleanup;
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.      
    }
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    eexists _, [], _, [].
    repeat rewrite app_nil_r;
    simpl; intuition eauto.
    repeat invert_exec.

    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].

    eexists _, [], _, [].
    repeat rewrite app_nil_r;
    simpl; intuition eauto.

    
    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].

    
    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
     
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    do 4 eexists; intuition eauto.
    simpl; eauto.

    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup]. 
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
  }
Qed.

Theorem have_same_structure_Transaction_commit:
forall u u' ex s1 s2 o1 o2 o3 o4,
((exists s1' s2' r1 r2,
exec ATCLang u o1 s1 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.commit) (Finished s1' r1) /\
exec ATCLang u o2 s2 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.commit) (Finished s2' r2)) \/
(exists s1' s2',
exec ATCLang u o1 s1 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.commit) (Crashed s1') /\
exec ATCLang u o2 s2 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.commit) (Crashed s2'))) ->
o1 ++ o3 = o2 ++ o4 -> 
length (dedup_last addr_dec (rev (map fst (fst (snd s1))))) =
length (dedup_last addr_dec (rev (map fst (fst (snd s2))))) ->
refines_related ATC_Refinement (AD_related_states ex u') s1 s2 ->
ATC_have_same_structure
  (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.commit)
  (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.commit) u s1 s2 o1 o2.
Proof.
  unfold Transaction.commit; intros.
  split_ors; cleanup.
  {
    repeat (repeat invert_exec; cleanup).
    all: try solve [simpl in *; cleanup].
    {
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat invert_exec; cleanup;
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat cleanup_pairs.
      intuition eauto.
      repeat rewrite <- dedup_last_dedup_by_list_length_le; eauto.
      repeat rewrite rev_length, map_length; eauto.
      repeat rewrite rev_length, map_length; eauto.
      simpl; eauto.
    }
    {
      repeat split_ors; cleanup; try lia.
      exfalso; apply H0; apply Transaction.dedup_last_NoDup.
      repeat cleanup_pairs; cleanup.
      erewrite <- dedup_last_dedup_by_list_length_le in H0.
      exfalso; intuition eauto.
      repeat rewrite rev_length, map_length; eauto.

      unfold refines_related  in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *.
      logic_clean; eauto.
      repeat cleanup_pairs.
      exfalso; apply H0; eauto.
      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H.
      apply in_rev in H.
      eapply Forall_forall in H27; eauto.
      
      repeat cleanup_pairs.
      erewrite <- addr_list_to_blocks_length_eq in H21. 
      2: apply H1.
      erewrite <- dedup_last_dedup_by_list_length_le in H0; eauto.
      erewrite <- dedup_last_dedup_by_list_length_le in H21.
      lia.
      repeat rewrite rev_length, map_length; eauto.
      repeat rewrite rev_length, map_length; eauto.
    }
    {
      repeat split_ors; cleanup; try lia.
      exfalso; apply H0; apply Transaction.dedup_last_NoDup.
      repeat cleanup_pairs; cleanup.
      erewrite <- dedup_last_dedup_by_list_length_le in H0.
      exfalso; intuition eauto.
      repeat rewrite rev_length, map_length; eauto.

      unfold refines_related  in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *.
      logic_clean; eauto.
      repeat cleanup_pairs.
      exfalso; apply H0; eauto.
      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H.
      apply in_rev in H.
      eapply Forall_forall in H18; eauto.
      
      repeat cleanup_pairs.
      erewrite addr_list_to_blocks_length_eq in H27. 
      2: apply H1.
      erewrite <- dedup_last_dedup_by_list_length_le in H0; eauto.
      erewrite <- dedup_last_dedup_by_list_length_le in H27.
      lia.
      repeat rewrite rev_length, map_length; eauto.
      repeat rewrite rev_length, map_length; eauto.
    }
    {
      clear H15 H21. (* Clear or conditions *)
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat invert_exec; cleanup;
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat cleanup_pairs.
      intuition eauto.
      repeat rewrite <- dedup_last_dedup_by_list_length_le; eauto.
      repeat rewrite rev_length, map_length; eauto.
      repeat rewrite rev_length, map_length; eauto.

      apply Transaction.dedup_last_NoDup.
      apply Transaction.dedup_last_NoDup.

      unfold refines_related  in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *.
      logic_clean; eauto.
      repeat cleanup_pairs.
      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H0.
      apply in_rev in H0.
      eapply Forall_forall in H4; eauto.
      
      unfold refines_related  in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *.
      logic_clean; eauto.
      repeat cleanup_pairs.
      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H0.
      apply in_rev in H0.
      eapply Forall_forall in H9; eauto.

      repeat invert_exec; cleanup;
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
    }
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    eexists _, [], _, [].
    repeat rewrite app_nil_r;
    simpl; intuition eauto.
    repeat invert_exec.

    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].

    eexists _, [], _, [].
    repeat rewrite app_nil_r;
    simpl; intuition eauto.

    repeat cleanup_pairs.
    repeat rewrite <- dedup_last_dedup_by_list_length_le; eauto.
    repeat rewrite rev_length, map_length; eauto.
    repeat rewrite rev_length, map_length; eauto.

    
    apply Transaction.dedup_last_NoDup.
    apply Transaction.dedup_last_NoDup.

    repeat cleanup_pairs.
    unfold refines_related  in *; simpl in *.
    unfold HC_refines in *; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *.
    logic_clean; eauto.
    repeat cleanup_pairs.
    eapply Forall_forall; intros.
    apply Transaction.dedup_last_in in H0.
    apply in_rev in H0.
    eapply Forall_forall in H4; eauto.
    
    repeat cleanup_pairs.
    unfold refines_related  in *; simpl in *.
    unfold HC_refines in *; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *.
    logic_clean; eauto.
    repeat cleanup_pairs.
    eapply Forall_forall; intros.
    apply Transaction.dedup_last_in in H0.
    apply in_rev in H0.
    eapply Forall_forall in H9; eauto.

    eexists _, [], _, [].
    repeat rewrite app_nil_r;
    simpl; intuition eauto.

    repeat rewrite <- dedup_last_dedup_by_list_length_le; eauto.
    repeat rewrite rev_length, map_length; eauto.
    repeat rewrite rev_length, map_length; eauto.

    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].

    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat split_ors; cleanup;
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
     
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
    repeat rewrite <- dedup_last_dedup_by_list_length_le; eauto.
    repeat rewrite rev_length, map_length; eauto.
    repeat rewrite rev_length, map_length; eauto.

    {
      repeat split_ors; cleanup; try lia.
      exfalso; apply H; apply Transaction.dedup_last_NoDup.
      repeat cleanup_pairs; cleanup.
      erewrite <- dedup_last_dedup_by_list_length_le in H.
      exfalso; intuition eauto.
      repeat rewrite rev_length, map_length; eauto.

      unfold refines_related  in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *.
      logic_clean; eauto.
      repeat cleanup_pairs.
      exfalso; apply H; eauto.
      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H0.
      apply in_rev in H0.
      eapply Forall_forall in H5; eauto.
      
      repeat cleanup_pairs.
      erewrite addr_list_to_blocks_length_eq in H20. 
      2: apply H1.
      erewrite <- dedup_last_dedup_by_list_length_le in H; eauto.
      erewrite <- dedup_last_dedup_by_list_length_le in H20.
      lia.
      repeat rewrite rev_length, map_length; eauto.
      repeat rewrite rev_length, map_length; eauto.
    }    
    {
      repeat split_ors; cleanup; try lia.
      exfalso; apply H; apply Transaction.dedup_last_NoDup.
      repeat cleanup_pairs; cleanup.
      erewrite <- dedup_last_dedup_by_list_length_le in H.
      exfalso; intuition eauto.
      repeat rewrite rev_length, map_length; eauto.

      unfold refines_related  in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *.
      logic_clean; eauto.
      repeat cleanup_pairs.
      exfalso; apply H; eauto.
      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H0.
      apply in_rev in H0.
      eapply Forall_forall in H14; eauto.
      
      repeat cleanup_pairs.
      erewrite <- addr_list_to_blocks_length_eq in H20. 
      2: apply H1.
      erewrite <- dedup_last_dedup_by_list_length_le in H; eauto.
      erewrite <- dedup_last_dedup_by_list_length_le in H20.
      lia.
      repeat rewrite rev_length, map_length; eauto.
      repeat rewrite rev_length, map_length; eauto.
    }
    clear H11 H13. 

    repeat rewrite map_app;
    do 4 eexists; intuition eauto.

    repeat cleanup_pairs.
    repeat rewrite <- dedup_last_dedup_by_list_length_le; eauto.
    repeat rewrite rev_length, map_length; eauto.
    repeat rewrite rev_length, map_length; eauto.

    
    apply Transaction.dedup_last_NoDup.
    apply Transaction.dedup_last_NoDup.

    repeat cleanup_pairs.
    unfold refines_related  in *; simpl in *.
    unfold HC_refines in *; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *.
    logic_clean; eauto.
    repeat cleanup_pairs.
    eapply Forall_forall; intros.
    apply Transaction.dedup_last_in in H0.
    apply in_rev in H0.
    eapply Forall_forall in H4; eauto.
    
    repeat cleanup_pairs.
    unfold refines_related  in *; simpl in *.
    unfold HC_refines in *; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *.
    logic_clean; eauto.
    repeat cleanup_pairs.
    eapply Forall_forall; intros.
    apply Transaction.dedup_last_in in H0.
    apply in_rev in H0.
    eapply Forall_forall in H9; eauto.
  }
Qed.


Theorem have_same_structure_Transaction_recover:
forall u s1 s2 o1 o2 o3 o4,
((exists s1' s2' r1 r2,
exec ATCLang u o1 s1 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover) (Finished s1' r1) /\
exec ATCLang u o2 s2 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover) (Finished s2' r2)) \/
(exists s1' s2',
exec ATCLang u o1 s1 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover) (Crashed s1') /\
exec ATCLang u o2 s2 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover) (Crashed s2'))) ->
o1 ++ o3 = o2 ++ o4 -> 
ATC_have_same_structure
  (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover)
  (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover) u s1 s2 o1 o2.
Proof.
  unfold Transaction.recover; intros.
  split_ors; cleanup.
  {
    repeat (repeat invert_exec; cleanup).
    all: try solve [simpl in *; cleanup].
    {
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
      simpl; eauto.
      repeat invert_exec; cleanup;
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
    }
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    eexists _, [], _, [].
    repeat rewrite app_nil_r;
    simpl; intuition eauto.

    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
    repeat (repeat invert_exec; cleanup);
    try solve [simpl in *; cleanup].
    repeat rewrite map_app;
    do 4 eexists; intuition eauto.
  }
Qed.

Theorem ATC_HSS_transfer:
forall u u' ex T (p1 p2: AD.(prog) T) s1 s2 s1a s2a o1 o2 o3 o4,
HSS.have_same_structure p1 p2 u s1a s2a ->
ATC_Simulation.not_init p1 ->
ATC_Simulation.not_init p2 ->
((exists s1' s2' r1 r2,
exec ATCLang u o1 s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) /\
exec ATCLang u o2 s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2)) \/
(exists s1' s2',
exec ATCLang u o1 s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Crashed s1') /\
exec ATCLang u o2 s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Crashed s2'))) ->
o1 ++ o3 = o2 ++ o4 -> 
length (dedup_last addr_dec (rev (map fst (fst (snd s1))))) =
length (dedup_last addr_dec (rev (map fst (fst (snd s2))))) ->
refines_related ATC_Refinement (AD_related_states ex u') s1 s2 ->
ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2 o1 o2.
Proof.
  Opaque Transaction.read Transaction.write Transaction.commit Transaction.recover.
  induction p1; destruct p2; simpl in *; intros; try tauto.
  {
    cleanup; simpl in *; try tauto.
    unfold TD_have_same_structure in *.
    cleanup; simpl in *; try tauto.
    eapply have_same_structure_Transaction_read; eauto.
    eapply have_same_structure_Transaction_write; eauto.
    eapply have_same_structure_Transaction_commit; eauto.
    eapply have_same_structure_Transaction_recover; eauto.
    exfalso; intuition eauto.
  }
  {
    unfold refines_related in *; simpl in *.
    intuition; cleanup.
    repeat invert_exec.
    do 4 eexists; intuition; cleanup_no_match.
    eapply IHp1; eauto.
    repeat rewrite <- app_assoc in *.
    left; do 2 eexists;
    intuition eauto.
    repeat rewrite <- app_assoc in *.
    apply H4.

    repeat rewrite <- app_assoc in *.
    repeat unify_execs; cleanup.

    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H15; eauto; cleanup.
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H16; eauto; cleanup.
    
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H15; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H16; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.

    simpl in *.

    eapply_fresh ATC_ORS.ATC_oracle_refines_impl_eq in H8; eauto.
    4: apply TD_oracle_refines_operation_eq.
    cleanup.
    eapply H; eauto.
    eapply H12; eauto.
  }
  Unshelve.
  all: eauto.
Admitted.
Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import HSS ATCLayer ATC_Simulation ATC_AOE.
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
      
  Definition AD_related_states_reboot u ex:= refines_related_reboot _ _ _ _ FDRefinement (FD_related_states u ex).


  Lemma map_ext_eq_prefix:
  forall (A B : Type) (l1 l2 : list A) l3 l4 (f : A -> B),
  map f l1 ++ l3 = map f l2 ++ l4 -> 
  (forall a a' : A, f a = f a' -> a = a') -> 
  exists l3' l4', 
  l1 ++ l3' = l2 ++ l4'.
  Proof.
      induction l1; simpl; intros; eauto.
      destruct l2; simpl in *; cleanup; eauto.
      apply H0 in H2; rewrite H2; eauto.
      edestruct IHl1; eauto; cleanup; eauto.
      do 2 eexists; rewrite H; eauto.
      Unshelve.
      all: eauto.
  Qed.
  



  


  Lemma ATC_ORS_compositional:
  forall n u T (p1 p2: prog AD T) T' (p3 p4: T -> prog AD T') rec P RS RSR, 
  (forall n, oracle_refines_same_from_related ATC_Refinement u p1 p2 rec (ATC_reboot_list n) RS) ->
  
  (forall u o oa s1 s2 s1' s2' r1 r2,
  LayerImplementation.exec' u o s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
  LayerImplementation.exec' u o s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
  refines_related ATC_Refinement RS s1 s2 ->
  oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement) T u
        s1 p1 ATC_reboot_f o oa ->
      oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement) T u
        s2 p2 ATC_reboot_f o oa ->
  oracle_refines_same_from_related ATC_Refinement u (p3 r1) (p4 r2) rec (ATC_reboot_list n) P) ->
  
  (forall n, oracle_refines_same_from_related_reboot _ _ _ _ ATC_Refinement u rec rec rec (ATC_reboot_list n) RSR) ->
  
  (forall u o1 o2 o3 o4 oa1 oa2 s1 s2 s1' s2' r1 r2,
  LayerImplementation.exec' u o1 s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
  LayerImplementation.exec' u o2 s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
  oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement) T u
        s1 p1 ATC_reboot_f o1 oa1 ->
      oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement) T u
        s2 p2 ATC_reboot_f o2 oa2 ->
  o1 ++ o3 = o2 ++ o4 ->
  refines_related ATC_Refinement RS s1 s2 ->
  o1 = o2) ->
  
  (forall T (p: prog AD T) s s' r o o_abs grs, 
  LayerImplementation.exec' u o s (ATC_Refinement.(Simulation.Definitions.compile) p) (Finished s' r) ->
  oracle_refines _ _ _ _ ATC_CoreRefinement T u s p grs o o_abs ->
  forall grs', oracle_refines _ _ _ _ ATC_CoreRefinement T u s p grs' o o_abs) ->
  
  (forall u o oa1 oa2 s1 s2 s1' s2' r1 r2,
  LayerImplementation.exec' u o s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
  LayerImplementation.exec' u o s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
  refines_related ATC_Refinement RS s1 s2 ->
  oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore
              data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD
           Definitions.TDCoreRefinement) _ u s1 p1
        (fun
           s : HorizontalComposition.state'
                 AuthenticationOperation
                 TransactionCacheOperation =>
         (fst s, ([], snd (snd s)))) 
        o oa1 ->
  oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore
              data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD
           Definitions.TDCoreRefinement) _ u s2 p2
        (fun
           s : HorizontalComposition.state'
                 AuthenticationOperation
                 TransactionCacheOperation =>
         (fst s, ([], snd (snd s)))) 
        o oa2 ->
  refines_related ATC_Refinement P s1' s2') ->

  (forall u o1 o2 oa1 oa2 s1 s2 s1' s2' r1,
  LayerImplementation.exec' u o1 s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
  refines_related ATC_Refinement RS s1 s2 ->
  oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore
              data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD
           Definitions.TDCoreRefinement) T u s1 p1
        (fun
           s : HorizontalComposition.state'
                 AuthenticationOperation
                 TransactionCacheOperation =>
         (fst s, ([], snd (snd s)))) 
        o1 oa1 ->
  oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore
              data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD
           Definitions.TDCoreRefinement) T u s2 p2
        (fun
           s : HorizontalComposition.state'
                 AuthenticationOperation
                 TransactionCacheOperation =>
         (fst s, ([], snd (snd s)))) 
        (o1++o2) oa2 ->
  ~LayerImplementation.exec' u (o1 ++ o2) s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Crashed s2')) ->

  (forall u o1 o2 oa1 oa2 s1 s2 s1' s2' r2,
  LayerImplementation.exec' u o1 s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
  refines_related ATC_Refinement RS s1 s2 ->
  oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore
              data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD
           Definitions.TDCoreRefinement) T u s1 p1
        (fun
           s : HorizontalComposition.state'
                 AuthenticationOperation
                 TransactionCacheOperation =>
         (fst s, ([], snd (snd s)))) 
        (o1++o2) oa1 ->
  oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore
              data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD
           Definitions.TDCoreRefinement) T u s2 p2
        (fun
           s : HorizontalComposition.state'
                 AuthenticationOperation
                 TransactionCacheOperation =>
         (fst s, ([], snd (snd s)))) 
        o1 oa2 ->
  ~LayerImplementation.exec' u (o1 ++ o2) s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Crashed s1')) ->
  
  (forall u o oa1 oa2 s1 s2 s1' s2',
  LayerImplementation.exec' u o s1 (ATC_Refinement.(Simulation.Definitions.compile) (Bind p1 p3)) (Crashed s1') ->
  LayerImplementation.exec' u o s2 (ATC_Refinement.(Simulation.Definitions.compile) (Bind p2 p4)) (Crashed s2') ->
  refines_related ATC_Refinement RS s1 s2 ->
  oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore
              data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD
           Definitions.TDCoreRefinement) _ u s1 (Bind p1 p3)
        (fun
           s : HorizontalComposition.state'
                 AuthenticationOperation
                 TransactionCacheOperation =>
         (fst s, ([], snd (snd s)))) 
        o oa1 ->
  oracle_refines
        (HorizontalComposition AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore
              data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD
           Definitions.TDCoreRefinement) _ u s2 (Bind p2 p4)
        (fun
           s : HorizontalComposition.state'
                 AuthenticationOperation
                 TransactionCacheOperation =>
         (fst s, ([], snd (snd s)))) 
        o oa2 ->
  refines_related_reboot _ _ _ _ ATC_Refinement RSR (ATC_reboot_f s1') (ATC_reboot_f s2')) ->

  oracle_refines_same_from_related ATC_Refinement u (Bind p1 p3) (Bind p2 p4) rec (ATC_reboot_list n) RS.
  Proof.
      unfold oracle_refines_same_from_related,
      ATC_reboot_list; 
      simpl; intros; destruct n; simpl in *; intuition.
  
      {
        destruct l_o_imp; simpl in *; try tauto;
      cleanup; simpl in *; try congruence; try lia;
      try solve [cleanup; tauto].
      {  
        repeat split_ors; cleanup;
        try solve [cleanup; tauto].
        repeat match goal with
        | [H: exec ATCLang _ _ _ (Bind _ _) _ |- _] =>
        invert_exec'' H
        end.
        repeat match goal with
        | [H: forall _, _ |- _] =>
        specialize (H ATC_reboot_f)
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
        

        specialize (H 0 [x3] [x12] [x5]).
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
        | [H: exec ATCLang _ _ _ (Bind _ _) _ |- _] =>
        invert_exec'' H
        end.
        repeat match goal with
        | [H: forall _, _ |- _] =>
        specialize (H ATC_reboot_f)
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
        
        
        specialize (H 0 [x3] [x12] [x5]).
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
        | [H: exec ATCLang _ _ _ (Bind _ _) _ |- _] =>
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
        specialize (H (S n) [x1] [x10] [x3]).
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
        cleanup.
        match goal with
        | [A: LayerImplementation.exec' _ _ ?s1_imp _ (Finished _ _),
          A0: LayerImplementation.exec' _ _ ?s2_imp _ (Finished _ _),
          A1: refines_related _ _ ?s1_imp ?s2_imp,
          A2: oracle_refines _ _ _ _ _ _ _ ?s1_imp _ _ _ _, 
          A3: oracle_refines _ _ _ _ _ _ _ ?s2_imp _ _ _ _ |- _] =>
          specialize H0 with (1:=A)(2:= A0)(3:= A1)(4:=A2)(5:=A3); subst; cleanup
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
        specialize (H (S n) (o::l_o_imp) (o1::l) (o0::l)).
        simpl in *.
        specialize H with (1 := H8).
        simpl in *.
        assert ((o1::l) = (o0::l)). {
          eapply H.
          intuition; right; do 2 eexists; 
          intuition eauto.

          intuition; right; do 2 eexists; 
          intuition eauto.
        }
        cleanup; eauto.

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




  Lemma ATC_ORS_recover:
      forall n u R,
      oracle_refines_same_from_related_reboot _ _ _ _ ATC_Refinement u
      (Simulation.Definitions.compile FD.refinement (| Recover |))
      (Simulation.Definitions.compile FD.refinement (| Recover |))
      (Simulation.Definitions.compile FD.refinement (| Recover |))
      (ATC_reboot_list n) R. (* (AD_related_states_reboot u' ex). *)
      Proof.
        Transparent File.recover.
        unfold oracle_refines_same_from_related_reboot, 
        ATC_reboot_list; induction n; simpl in *.
        { (* Finished *)
          intros.
          unfold File.recover in *; simpl in *.
          destruct l_o_imp; simpl in *; intuition.
          cleanup; try tauto.
          repeat split_ors; cleanup;
          simpl in *; try lia.
          specialize (H7 ATC_reboot_f).
          specialize (H4 ATC_reboot_f).
          cleanup.
          specialize (H7 tt).
          specialize (H10 tt).
          repeat invert_exec; simpl in *; cleanup.
          (*
          inversion H0; inversion H4; subst; clear H0 H4.
          inversion H9; inversion H1; subst; clear H9 H1.
          *) 
          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto.
          unfold Transaction.recover in *.
          repeat invert_exec; simpl in *; cleanup; eauto.
          split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto.

          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto.
          unfold Transaction.recover in *.
          repeat invert_exec; simpl in *; cleanup; eauto.
          split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto.
        }
        {(*Crashed*)
          intros.
          unfold File.recover in *; simpl in *.
          destruct l_o_imp; simpl in *; intuition.
          cleanup; try tauto.
          repeat split_ors; cleanup;
          simpl in *; try lia.
          {
            specialize (H7 ATC_reboot_f).
            specialize (H4 ATC_reboot_f).
            cleanup.
            specialize (H7 tt).
            specialize (H10 tt).
            repeat invert_exec; simpl in *; cleanup.
            (*
            inversion H0; inversion H4; subst; clear H0 H4.
            inversion H9; inversion H1; subst; clear H9 H1.
            *)
            repeat split_ors; cleanup;
            repeat invert_exec; simpl in *; cleanup; eauto.
            unfold Transaction.recover in *.
            repeat invert_exec; simpl in *; cleanup; eauto.
            split_ors; cleanup;
            repeat invert_exec; simpl in *; cleanup; eauto.

            repeat split_ors; cleanup;
            repeat invert_exec; simpl in *; cleanup; eauto.
            unfold Transaction.recover in *.
            repeat invert_exec; simpl in *; cleanup; eauto.
            split_ors; cleanup;
            repeat invert_exec; simpl in *; cleanup; eauto.
          }
          {
            cleanup.
            repeat invert_exec; simpl in *; cleanup.
            specialize (H8 tt).
            specialize (H13 tt).
            repeat split_ors; cleanup;
            repeat invert_exec; simpl in *; cleanup; eauto.
            {
              eapply IHn in H5.
              3: apply H10.
              2:{
                unfold refines_related_reboot, AD_related_states_reboot, refines_related_reboot in *;
                cleanup.
                do 2 eexists; split; eauto.
                2: split; eauto.
                {
                  simpl in *; unfold HC_refines_reboot in *;
                  simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines,
                  Transaction.transaction_rep in *; simpl in *; cleanup; eauto.
                }
                {
                  simpl in *; unfold HC_refines_reboot in *;
                  simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines,
                  Transaction.transaction_rep in *; simpl in *; cleanup; eauto.
                }
              }
              subst; eauto.
            }
            {
              unfold Transaction.recover in *;
              repeat invert_exec; simpl in *; cleanup.
            }
            {
              unfold Transaction.recover in *;
              repeat invert_exec; simpl in *; cleanup.
            }
            {
              unfold Transaction.recover in *;
              repeat invert_exec; simpl in *; cleanup.
            }
            {
              unfold Transaction.recover in *;
              repeat invert_exec; simpl in *; cleanup.
              repeat split_ors; cleanup;
              repeat invert_exec; simpl in *; cleanup; eauto.
            }
            {
              unfold Transaction.recover in *;
              repeat invert_exec; simpl in *; cleanup.
              
              repeat split_ors; cleanup;
              repeat invert_exec; simpl in *; cleanup; eauto.
              eapply IHn in H5.
              3: apply H10.
              2:{
                unfold refines_related_reboot, AD_related_states_reboot, refines_related_reboot in *;
                cleanup.
                do 2 eexists; split; eauto.
                2: split; eauto.
                {
                  simpl in *; unfold HC_refines_reboot in *;
                  simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines,
                  Transaction.transaction_rep in *; simpl in *; cleanup; eauto.
                }
                {
                  simpl in *; unfold HC_refines_reboot in *;
                  simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines,
                  Transaction.transaction_rep in *; simpl in *; cleanup; eauto.
                }
              }
              subst; eauto.
            }
            {
              unfold Transaction.recover in *;
              repeat invert_exec; simpl in *; cleanup.
            }
            {
              unfold Transaction.recover in *;
              repeat invert_exec; simpl in *; cleanup.
              repeat split_ors; cleanup;
              repeat invert_exec; simpl in *; cleanup; eauto.
              eapply IHn in H5.
              3: apply H10.
              2:{
                unfold refines_related_reboot, AD_related_states_reboot, refines_related_reboot in *;
                cleanup.
                do 2 eexists; split; eauto.
                2: split; eauto.
                {
                  simpl in *; unfold HC_refines_reboot in *;
                  simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines,
                  Transaction.transaction_rep in *; simpl in *; cleanup; eauto.
                }
                {
                  simpl in *; unfold HC_refines_reboot in *;
                  simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines,
                  Transaction.transaction_rep in *; simpl in *; cleanup; eauto.
                }
              }
              subst; eauto.
            }
          }
        }
      Qed.



      Lemma oracle_refines_independent_from_reboot_function:
      forall u (T : Type) (p : prog AD T)
    (s
    s' : LayerImplementation.state'
    (HorizontalComposition AuthenticationOperation
    TransactionCacheOperation)) (r : T)
    (o : oracle'
    (HorizontalComposition AuthenticationOperation
    TransactionCacheOperation))
    (o_abs : list
    (Layer.token'
      (HorizontalComposition AuthenticationOperation
         (TransactionalDiskLayer.TDCore data_length))))
    (grs : state ATCLang -> state ATCLang),
    LayerImplementation.exec' u o s (Simulation.Definitions.compile ATC_Refinement p)
    (Finished s' r) ->
    oracle_refines
    (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
    (HorizontalComposition AuthenticationOperation
    (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
    ATC_CoreRefinement T u s p grs o o_abs ->
    forall grs' : state ATCLang -> state ATCLang,
    oracle_refines
    (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
    (HorizontalComposition AuthenticationOperation
    (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
    ATC_CoreRefinement T u s p grs' o o_abs.
    Proof.
      induction p; simpl; eauto.
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
    Qed.
    
    (*
    Lemma HC_oracle_refines_lift2:
    forall T (p: TD.(prog) T) o u s x,
    oracle_refines
    (HorizontalComposition AuthenticationOperation
    TransactionCacheOperation)
    (HorizontalComposition AuthenticationOperation
    (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
    (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
    T u s
    (lift_L2 AuthenticationOperation p)
    (fun
    s : HorizontalComposition.state' AuthenticationOperation
          TransactionCacheOperation => (fst s, ([], snd (snd s))))
    o x ->
    
      ((RefinementLift.compile
    (HorizontalComposition AuthenticationOperation
        TransactionCacheOperation)
    (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
    (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement) T
    (lift_L2 AuthenticationOperation p)) = 
    (lift_L2 AuthenticationOperation 
    (RefinementLift.compile TransactionCacheOperation
    (TransactionalDiskLayer.TDCore data_length) Definitions.imp TD
    Definitions.TDCoreRefinement T p))) ->
    
      oracle_refines _ _ Definitions.imp TD Definitions.TDCoreRefinement
      T u (snd s) p (fun s => ([], snd s)) (HC_transform_oracle _ o) x.
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
    
          Lemma TD_oracle_refines_operation_eq:
          forall (u0 : user) (T : Type) (o1 : operation Definitions.abs_op T)
          (T' : Type) (o2 : operation Definitions.abs_op T')
          (x16 : list (Layer.token' TransactionCacheOperation))
          (x17 : TransactionalDiskLayer.token')
          (x18 : oracle' TransactionCacheOperation)
          (x19 : state Definitions.imp -> state Definitions.imp)
          (x20 : list (Layer.token' TransactionCacheOperation))
          (x21 : oracle' TransactionCacheOperation)
          (x22 : state Definitions.imp -> state Definitions.imp)
          (x23 : TransactionalDiskLayer.token') (s0 s3 : state Definitions.imp)
          (s1' s2' : LayerImplementation.state' TransactionCacheOperation) 
          (r1 : T) (r2 : T'),
        TransactionToTransactionalDisk.Definitions.token_refines T u0 s0 o1 x22 x21
          x17 ->
        TransactionToTransactionalDisk.Definitions.token_refines T' u0 s3 o2 x19 x18
          x23 ->
        exec Definitions.imp u0 x21 s0
          (TransactionToTransactionalDisk.Definitions.compile T o1) 
          (Finished s1' r1) ->
        exec Definitions.imp u0 x18 s3
          (TransactionToTransactionalDisk.Definitions.compile T' o2)
          (Finished s2' r2) ->
        TD_have_same_structure o1 o2 ->
        x18 ++ x16 = x21 ++ x20 -> x18 = x21 /\ x17 = x23.
        Proof.
          intros;
          destruct o1, o2; simpl in *; cleanup; try tauto.
          {
            repeat split_ors; cleanup; repeat unify_execs_prefix; cleanup.
            eapply Transaction.read_finished_oracle_eq in H1; eauto.
            exfalso; eapply Transaction.read_finished_not_crashed; eauto.
            symmetry in H4; exfalso; eapply Transaction.read_finished_not_crashed; eauto.
            exfalso; eapply Transaction.read_finished_not_crashed; eauto.
          }
          {
            repeat (split_ors; cleanup; repeat unify_execs;
            repeat unify_execs_prefix; cleanup);
            try solve [eapply Transaction.write_finished_oracle_eq in H1; eauto; cleanup; eauto].
            {
              unfold Transaction.write in *; cleanup; try lia.
              invert_exec; try lia.
              invert_exec'' H; try lia.
              repeat (invert_exec; try lia);
              simpl in *; cleanup;
              repeat cleanup_pairs; simpl in *; try lia. 
              exfalso; eapply PeanoNat.Nat.lt_nge.
              2: apply l2.
              eauto.
              invert_exec'' H; try lia.
              invert_exec'' H12; try lia.
              invert_exec'' H11; try lia.
              exfalso; apply n; eauto.
            }
            {
              unfold Transaction.write in *; cleanup; try lia.
              invert_exec; try lia.
              repeat (invert_exec; try lia);
              simpl in *; cleanup;
              repeat cleanup_pairs; simpl in *; try lia. 
            }
            {
              unfold Transaction.write in *; cleanup; try lia.
              invert_exec; try lia.
              invert_exec'' H; try lia.
              invert_exec'' H12; try lia.
              invert_exec'' H11; try lia.
              exfalso; eapply PeanoNat.Nat.lt_nge.
              2: apply l1.
              eauto.
              invert_exec'' H; try lia.
              invert_exec'' H12; try lia.
              invert_exec'' H11; try lia.
              invert_exec'' H0; try lia.
              repeat (invert_exec; try lia).
              simpl in *; cleanup.
              exfalso; apply n0; eauto.
            }
            {
              unfold Transaction.write in *; cleanup; try lia.
              invert_exec; try lia.
              repeat (invert_exec; try lia);
              simpl in *; cleanup;
              repeat cleanup_pairs; simpl in *; try lia. 
            }
          }
          {
            repeat (split_ors; cleanup; repeat unify_execs;
            repeat unify_execs_prefix; cleanup);
            try solve [eapply Transaction.commit_finished_oracle_eq in H1; eauto; cleanup; eauto].
          }
          {
            repeat (split_ors; cleanup; repeat unify_execs;
            repeat unify_execs_prefix; cleanup);
            try solve [eapply Transaction.abort_finished_oracle_eq in H1; eauto; cleanup; eauto].
          }
          {
            repeat (split_ors; cleanup; repeat unify_execs;
            repeat unify_execs_prefix; cleanup);
            try solve [eapply Transaction.recover_finished_oracle_eq in H1; eauto; cleanup; eauto].
          }
          {
            repeat (split_ors; cleanup; repeat unify_execs;
            repeat unify_execs_prefix; cleanup);
            try solve [eapply Transaction.init_finished_oracle_eq in H1; eauto; cleanup; eauto].
          }
          Unshelve.
          all: eauto.
        Qed.
      
    
        Lemma TD_oracle_refines_operation_eq_crashed:
          forall (u0 : user) (T : Type) (o1 : operation Definitions.abs_op T)
          (T' : Type) (o2 : operation Definitions.abs_op T')
          (x16 : list (Layer.token' TransactionCacheOperation))
          (x17 : TransactionalDiskLayer.token')
          (x18 : oracle' TransactionCacheOperation)
          (x19 : state Definitions.imp -> state Definitions.imp)
          (x20 : list (Layer.token' TransactionCacheOperation))
          (x21 : oracle' TransactionCacheOperation)
          (x22 : state Definitions.imp -> state Definitions.imp)
          (x23 : TransactionalDiskLayer.token') (s0 s3 : state Definitions.imp)
          (s1' s2' : LayerImplementation.state' TransactionCacheOperation),
        TransactionToTransactionalDisk.Definitions.token_refines T u0 s0 o1 x22 x21
          x17 ->
        TransactionToTransactionalDisk.Definitions.token_refines T' u0 s3 o2 x19 x18
          x23 ->
        exec Definitions.imp u0 x21 s0
          (TransactionToTransactionalDisk.Definitions.compile T o1) 
          (Crashed s1') ->
        exec Definitions.imp u0 x18 s3
          (TransactionToTransactionalDisk.Definitions.compile T' o2)
          (Crashed s2') ->
        TD_have_same_structure o1 o2 ->
        x18 ++ x16 = x21 ++ x20 -> x17 = x23.
        Proof.
          intros;
          destruct o1, o2; simpl in *; cleanup; try tauto.
          {
            repeat split_ors; cleanup; repeat unify_execs_prefix; cleanup; eauto.
            exfalso; eapply Transaction.read_finished_not_crashed; eauto.
            exfalso; eapply Transaction.read_finished_not_crashed; eauto.
          }
          {
            repeat (split_ors; cleanup; repeat unify_execs;
            repeat unify_execs_prefix; cleanup);
            try solve [eapply Transaction.write_finished_oracle_eq in H1; eauto; cleanup; eauto].
            eauto.
          }
          {
            split_ors; cleanup; repeat unify_execs;
            repeat unify_execs_prefix; cleanup.
            split_ors; cleanup; repeat unify_execs;
            repeat unify_execs_prefix; cleanup; eauto;
            destruct H; cleanup; repeat unify_execs;
            repeat unify_execs_prefix; cleanup; eauto;
            destruct H0; cleanup; repeat unify_execs;
            repeat unify_execs_prefix; cleanup; eauto.

            unfold Transaction.commit in *.
            repeat (repeat invert_exec; repeat split_ors;
            cleanup; simpl in *; try lia; try congruence).

            all: try solve [repeat rewrite app_length in *;
            match goal with
            | [H: length ?x + _ = _ |- _] =>
               destruct x
            end; simpl in *; try lia; cleanup; try congruence;
            match goal with
            | [H: S (length ?x + _) = _ |- _] =>
               destruct x
            end; simpl in *; try lia; cleanup; try congruence].

            all: try solve [setoid_rewrite cons_app in H1 at 2; eapply app_inj_tail in H1; cleanup; congruence].
            all: try solve [setoid_rewrite cons_app in H at 2; eapply app_inj_tail in H; cleanup; congruence].

            unfold Transaction.commit in *.
            repeat (repeat invert_exec; repeat split_ors;
            cleanup; simpl in *; try lia; try congruence).

            all: try solve [repeat rewrite app_length in *;
            match goal with
            | [H: length ?x + _ = _ |- _] =>
               destruct x
            end; simpl in *; try lia; cleanup; try congruence;
            match goal with
            | [H: S (length ?x + _) = _ |- _] =>
               destruct x
            end; simpl in *; try lia; cleanup; try congruence].

            all: try solve [setoid_rewrite cons_app in H1 at 2; eapply app_inj_tail in H1; cleanup; congruence].
            all: try solve [setoid_rewrite cons_app in H at 2; eapply app_inj_tail in H; cleanup; congruence].

          }
          {
            repeat (split_ors; cleanup; repeat unify_execs;
            repeat unify_execs_prefix; cleanup; eauto).          
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
    
      Lemma ATC_oracle_refines_impl_eq:
      forall u T p1 T' p2 s1 s2 s1' s2' s1a s2a r1 r2 o1 o2 o3 o4 oa1 oa2, (* oa3 oa4, *)
      oracle_refines
       (HorizontalComposition AuthenticationOperation
          TransactionCacheOperation)
       (HorizontalComposition AuthenticationOperation
          (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
       (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
       T u s1 p1 ATC_reboot_f o1 oa1 ->
      oracle_refines
       (HorizontalComposition AuthenticationOperation
          TransactionCacheOperation)
       (HorizontalComposition AuthenticationOperation
          (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
       (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
       T' u s2 p2 ATC_reboot_f o2 oa2 ->
    
      @HC_refines _ _ _ _ _ AD Definitions.TDCoreRefinement s1 s1a ->
      @HC_refines _ _ _ _ _ AD Definitions.TDCoreRefinement s2 s2a ->
    
       exec ATCLang u o1 s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
       exec ATCLang u o2 s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
      have_same_structure p1 p2 u s1a s2a ->
    
       (forall u T o1 T' o2 x x0 x1 x2 x3 x4 x5 x6 s1 s2 s1' s2' r1 r2,
      TransactionToTransactionalDisk.Definitions.token_refines T u 
       s1 o1 x5 x4 x0 ->
      TransactionToTransactionalDisk.Definitions.token_refines T' u 
       s2 o2 x2 x1 x6 ->
       exec Definitions.imp u x4 s1
       (TransactionToTransactionalDisk.Definitions.compile T o1)
       (Finished s1' r1) ->
       exec Definitions.imp u x1 s2
       (TransactionToTransactionalDisk.Definitions.compile T' o2)
       (Finished s2' r2) ->
       TD_have_same_structure o1 o2 ->
       x1 ++ x = x4 ++ x3 ->
       x1 = x4 /\ x0 = x6) ->
    
      o1 ++ o3 = o2 ++ o4 ->
      True ->
      o1 = o2 /\ oa1 = oa2.
      Proof.
        induction p1; destruct p2; simpl; intros; try tauto; 
        cleanup; try tauto.
        {
          unfold HC_token_refines in *; cleanup;
          simpl in *; cleanup; eauto.
        }
        {
          unfold HC_token_refines in *; cleanup;
          simpl in *; cleanup; eauto.
          specialize (H10 tt).
          specialize (H12 tt).
          eapply HC_map_ext_eq_prefix in H7; cleanup.
          eapply lift2_invert_exec in H3; cleanup.
          eapply lift2_invert_exec in H4; cleanup.
          eapply HC_map_ext_eq in H4; cleanup.
          eapply HC_map_ext_eq in H0; cleanup.
            assert (x6 = x5 /\ x3 = x1). {
            eapply H6; eauto.
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
    
          eapply exec_finished_deterministic_prefix in H19; eauto; cleanup.
          eapply exec_finished_deterministic_prefix in H14; eauto; cleanup.
          repeat unify_execs; cleanup.
          repeat rewrite <- app_assoc in *.
          eapply_fresh IHp1 in H16; eauto; subst; cleanup.
    
    
          eapply ATC_exec_lift_finished in H4; eauto;
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
          try solve [apply not_init_read].
          eapply ATC_exec_lift_finished in H5; eauto;
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
          try solve [apply not_init_read].
          simpl in *; cleanup.
    
          eapply H in H17; eauto.
          cleanup; eauto.
        }
    Unshelve.
    all: eauto.
      Qed.
    
    
        Lemma ATC_oracle_refines_prefix_finished:
        forall u T (p1 : AD.(prog) T) T' (p2 : AD.(prog) T') o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 s1a s2a oa1 oa2,
        oracle_refines
        (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement) 
        _ u s1 p1 ATC_reboot_f o1 oa1 ->
    
        oracle_refines
        (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement) 
        _ u s2 p2 ATC_reboot_f o2 oa2 ->
    
       exec ATCLang u o1 s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
       exec ATCLang u o2 s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
     
        @HC_refines _ _ _ _ _ AD Definitions.TDCoreRefinement s1 s1a ->
        @HC_refines _ _ _ _ _ AD Definitions.TDCoreRefinement s2 s2a ->
    
        (forall (u0 : user) (T : Type) (o1 : operation Definitions.abs_op T)
        (T' : Type) (o2 : operation Definitions.abs_op T')
        (x16 : list (Layer.token' TransactionCacheOperation))
        (x17 : TransactionalDiskLayer.token')
        (x18 : oracle' TransactionCacheOperation)
        (x19 : state Definitions.imp -> state Definitions.imp)
        (x20 : list (Layer.token' TransactionCacheOperation))
        (x21 : oracle' TransactionCacheOperation)
        (x22 : state Definitions.imp -> state Definitions.imp)
        (x23 : TransactionalDiskLayer.token') (s0 s3 : state Definitions.imp)
        (s1' s2' : LayerImplementation.state' TransactionCacheOperation) 
        (r1 : T) (r2 : T'),
      TransactionToTransactionalDisk.Definitions.token_refines T u0 s0 o1 x22 x21
        x17 ->
      TransactionToTransactionalDisk.Definitions.token_refines T' u0 s3 o2 x19 x18
        x23 ->
      exec Definitions.imp u0 x21 s0
        (TransactionToTransactionalDisk.Definitions.compile T o1) 
        (Finished s1' r1) ->
      exec Definitions.imp u0 x18 s3
        (TransactionToTransactionalDisk.Definitions.compile T' o2)
        (Finished s2' r2) ->
      TD_have_same_structure o1 o2 ->
      x18 ++ x16 = x21 ++ x20 -> x18 = x21 /\ x17 = x23) ->
        have_same_structure p1 p2 u s1a s2a ->
        not_init p1 ->
        not_init p2 ->
        o1 ++ o3 = o2 ++ o4 ->
        oa1 = oa2.
        Proof.
          induction p1; simpl; intros. 
          {
            repeat (simpl in *; cleanup; try tauto; eauto).
            specialize (H12 tt).
            specialize (H14 tt).
            eapply lift2_invert_exec in H1; cleanup.
            eapply lift2_invert_exec in H2; cleanup.
            eapply HC_map_ext_eq in H2.
            eapply HC_map_ext_eq in H.
            eapply HC_map_ext_eq_prefix in H9; cleanup.
            assert (x1 = x3). {
              eapply H5; eauto.
            }
            subst; eauto.
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
            repeat rewrite <- app_assoc in *; eauto.
    
            exfalso; eapply finished_not_crashed_oracle_prefix; 
            [eauto | | eauto];
            rewrite <- app_assoc; eauto.
    
            exfalso; eapply finished_not_crashed_oracle_prefix; 
            [eauto | | eauto];
            rewrite <- app_assoc; eauto.
    
            exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto;
            rewrite <- app_assoc; eauto.
    
            eapply exec_finished_deterministic_prefix in H17; eauto; cleanup.
            eapply exec_finished_deterministic_prefix in H22; eauto; cleanup.
            repeat unify_execs; cleanup.
            repeat rewrite <- app_assoc in *.
            
              assert (x16 = x9). {
                eapply IHp1.
                8: eauto.
                all: eauto.
              }
              subst.
              
              eapply_fresh exec_compiled_preserves_refinement_finished in H2; eauto; 
              cleanup; simpl in *.
              eapply_fresh exec_compiled_preserves_refinement_finished in H3; eauto; 
              cleanup; simpl in *.
              eapply_fresh ATC_exec_lift_finished in H2; eauto;
              try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
              try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
              eapply_fresh ATC_exec_lift_finished in H3; eauto;
              try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
              try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
              simpl in *; cleanup.
    
              assert (x14 = x7). {
                eapply ATC_oracle_refines_impl_eq.
                7: eauto.
                all: eauto.
              }
              subst; cleanup.
              
              assert (x17 = x10). {
                eapply H.
                8: eauto.
                all: eauto.
              }
              subst; eauto.
            }
            Unshelve.
            all: eauto.
        Qed.

        Lemma ATC_oracle_refines_prefix_one_crashed:
        forall u T (p1 : AD.(prog) T) T' (p2 : AD.(prog) T') o1 o2 o3 o4 s1 s2 s1' s2' r1 s1a s2a oa1 oa2,
        oracle_refines
        (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement) 
        _ u s1 p1 ATC_reboot_f o1 oa1 ->
    
        oracle_refines
        (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
        (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement) 
        _ u s2 p2 ATC_reboot_f o2 oa2 ->
    
       exec ATCLang u o1 s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
       exec ATCLang u o2 s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Crashed s2') ->
     
        @HC_refines _ _ _ _ _ AD Definitions.TDCoreRefinement s1 s1a ->
        @HC_refines _ _ _ _ _ AD Definitions.TDCoreRefinement s2 s2a ->
    
        have_same_structure p1 p2 u s1a s2a ->
        not_init p1 ->
        not_init p2 ->
        o1 ++ o3 = o2 ++ o4 ->
        False.
        Proof.
          induction p1; simpl; intros. 
          {
            repeat (simpl in *; cleanup; try tauto; eauto).
            repeat invert_exec.
            eapply lift2_invert_exec in H1; cleanup.
            eapply lift2_invert_exec_crashed in H2; cleanup.
            eapply HC_map_ext_eq in H.
            eapply HC_map_ext_eq in H2.
            subst.
            eapply HC_map_ext_eq_prefix in H8; cleanup.
            destruct o0, o6; cleanup; try tauto.
    
            eapply Transaction.read_finished_not_crashed; eauto.
            eapply Transaction.write_finished_not_crashed; eauto.
            eapply Transaction.commit_finished_not_crashed; eauto.
            eapply Transaction.abort_finished_not_crashed; eauto.
            eapply Transaction.recover_finished_not_crashed; eauto.
            eapply Transaction.init_finished_not_crashed; eauto.
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
    
              eapply_fresh ATC_oracle_refines_impl_eq in H19. 
              7: eauto.
              all: eauto.
              2: apply TD_oracle_refines_operation_eq.
              cleanup.
              
              eapply_fresh exec_compiled_preserves_refinement_finished in H2; eauto; 
              cleanup; simpl in *.
              eapply_fresh exec_compiled_preserves_refinement_finished in H14; eauto; 
              cleanup; simpl in *.
              eapply_fresh ATC_exec_lift_finished in H2; eauto;
              try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
              try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
              eapply_fresh ATC_exec_lift_finished in H14; eauto;
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


        Lemma ATC_ORS_equiv_impl:
        forall u T (p1 p2: AD.(prog) T) rec l_grs (EQ1 EQ2: state AD -> state AD -> Prop),
        oracle_refines_same_from_related ATC_Refinement u
        p1 p2 rec l_grs EQ2 ->
        (forall s1 s2, EQ1 s1 s2 -> EQ2 s1 s2) ->
        oracle_refines_same_from_related ATC_Refinement u
        p1 p2 rec l_grs EQ1.
        Proof.
          unfold oracle_refines_same_from_related; intros.
          eapply H; eauto.
          unfold refines_related in *; cleanup; eauto.
          do 2 eexists; intuition eauto.
        Qed.
        


        Lemma ATC_oracle_refines_impl_eq_crashed:
        forall u T p1 T' p2 s1 s2 s1' s2' s1a s2a o1 o2 o3 o4 oa1 oa2, (* oa3 oa4, *)
        oracle_refines _ _ ATCLang AD ATC_CoreRefinement
          T u s1 p1 ATC_reboot_f o1 oa1 ->
        oracle_refines _ _ ATCLang AD ATC_CoreRefinement
          T' u s2 p2 ATC_reboot_f o2 oa2 ->
        
        @HC_refines _ _ _ _ _ AD TransactionToTransactionalDisk.Definitions.TDCoreRefinement s1 s1a ->
        @HC_refines _ _ _ _ _ AD TransactionToTransactionalDisk.Definitions.TDCoreRefinement s2 s2a ->
        
          exec ATCLang u o1 s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Crashed s1') ->
          exec ATCLang u o2 s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Crashed s2') ->
          have_same_structure p1 p2 u s1a s2a ->
        
          (forall (u0 : user) (T : Type) (o1 : operation Definitions.abs_op T)
          (T' : Type) (o2 : operation Definitions.abs_op T')
          (x16 : list (Layer.token' TransactionCacheOperation))
          (x17 : TransactionalDiskLayer.token')
          (x18 : oracle' TransactionCacheOperation)
          (x19 : state Definitions.imp -> state Definitions.imp)
          (x20 : list (Layer.token' TransactionCacheOperation))
          (x21 : oracle' TransactionCacheOperation)
          (x22 : state Definitions.imp -> state Definitions.imp)
          (x23 : TransactionalDiskLayer.token') (s0 s3 : state Definitions.imp)
          (s1' s2' : LayerImplementation.state' TransactionCacheOperation) 
          (r1 : T) (r2 : T'),
        TransactionToTransactionalDisk.Definitions.token_refines T u0 s0 o1 x22 x21
          x17 ->
        TransactionToTransactionalDisk.Definitions.token_refines T' u0 s3 o2 x19 x18
          x23 ->
        exec Definitions.imp u0 x21 s0
          (TransactionToTransactionalDisk.Definitions.compile T o1) 
          (Finished s1' r1) ->
        exec Definitions.imp u0 x18 s3
          (TransactionToTransactionalDisk.Definitions.compile T' o2)
          (Finished s2' r2) ->
        TD_have_same_structure o1 o2 ->
        x18 ++ x16 = x21 ++ x20 -> x18 = x21 /\ x17 = x23) ->
        
        (forall (u0 : user) (T : Type) (o1 : operation Definitions.abs_op T)
        (T' : Type) (o2 : operation Definitions.abs_op T')
        (x16 : list (Layer.token' TransactionCacheOperation))
        (x17 : TransactionalDiskLayer.token')
        (x18 : oracle' TransactionCacheOperation)
        (x19 : state Definitions.imp -> state Definitions.imp)
        (x20 : list (Layer.token' TransactionCacheOperation))
        (x21 : oracle' TransactionCacheOperation)
        (x22 : state Definitions.imp -> state Definitions.imp)
        (x23 : TransactionalDiskLayer.token') (s0 s3 : state Definitions.imp)
        (s1' s2' : LayerImplementation.state' TransactionCacheOperation),
      TransactionToTransactionalDisk.Definitions.token_refines T u0 s0 o1 x22 x21
        x17 ->
      TransactionToTransactionalDisk.Definitions.token_refines T' u0 s3 o2 x19 x18
        x23 ->
      exec Definitions.imp u0 x21 s0
        (TransactionToTransactionalDisk.Definitions.compile T o1) 
        (Crashed s1') ->
      exec Definitions.imp u0 x18 s3
        (TransactionToTransactionalDisk.Definitions.compile T' o2)
        (Crashed s2') ->
      TD_have_same_structure o1 o2 ->
      x18 ++ x16 = x21 ++ x20 ->  x17 = x23) ->
        
        o1 ++ o3 = o2 ++ o4 ->
        not_init p1 /\ not_init p2 ->
        oa1 = oa2.
        Proof.
          induction p1; destruct p2; simpl; intros; try tauto; 
          cleanup_no_match; try tauto.
          {
            clear H9 H10.
            cleanup; try tauto;
            unfold HC_token_refines in *; cleanup;
            simpl in *; cleanup; eauto.
        
            specialize (H10 tt).
            specialize (H12 tt).
            eapply_fresh HC_map_ext_eq_prefix in H8; eauto; cleanup_no_match.
            eapply lift2_invert_exec_crashed in H3; cleanup.
            eapply lift2_invert_exec_crashed in H4; cleanup.
            eapply_fresh HC_map_ext_eq in H4; eauto; subst.
            eapply_fresh HC_map_ext_eq in H0; eauto; subst.
        
            assert (x3 = x1). {
              eapply H7; eauto.
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
            eapply IHp1; eauto.
        
        
            exfalso; eapply finished_not_crashed_oracle_prefix in H17.
            eapply H17; eauto.
            rewrite <- app_assoc; eauto.
        
            exfalso; eapply finished_not_crashed_oracle_prefix in H14.
            eapply H14; eauto.
            rewrite <- app_assoc; eauto.
        
        
            exfalso; eapply finished_not_crashed_oracle_prefix in H21.
            eapply H21; eauto.
            rewrite <- app_assoc; eauto.
        
            exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto.
            rewrite <- app_assoc; eauto.
        
            rewrite <- app_assoc in *.
            eapply exec_finished_deterministic_prefix in H19; eauto; cleanup.
            exfalso; eapply ATC_oracle_refines_prefix_one_crashed.
            4: eauto.
            6: eauto.
            8: eauto.
            all: eauto.
        
            exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto.
            rewrite <- app_assoc; eauto.
        
            exfalso; eapply finished_not_crashed_oracle_prefix in H5; eauto.
            rewrite <- app_assoc; eauto.
        
            exfalso; eapply finished_not_crashed_oracle_prefix in H1; eauto.
            rewrite <- app_assoc; eauto.
        
            rewrite <- app_assoc in *.
            eapply exec_finished_deterministic_prefix in H18; eauto; cleanup.
            exfalso; eapply ATC_oracle_refines_prefix_one_crashed.
            4: apply H4.
            3: apply H6.
            5: eapply have_same_structure_sym; eauto.
            all: eauto.
        
        
            exfalso; eapply finished_not_crashed_oracle_prefix in H4; eauto;
            rewrite <- app_assoc; eauto.
        
            exfalso; eapply finished_not_crashed_oracle_prefix in H1; eauto;
            rewrite <- app_assoc; eauto.
        
            exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto;
            rewrite <- app_assoc; eauto.
        
            eapply exec_finished_deterministic_prefix in H20; eauto; cleanup.
            eapply exec_finished_deterministic_prefix in H25; eauto; cleanup.
            repeat unify_execs; cleanup.
            repeat rewrite <- app_assoc in *.
            eapply_fresh ATC_oracle_refines_impl_eq in H6.
            7: eauto.
            all: eauto.
            cleanup.
        
            eapply ATC_exec_lift_finished in H6; eauto;
            try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
            try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
            try solve [apply not_init_read].
            eapply ATC_exec_lift_finished in H17; eauto;
            try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
            try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
            try solve [apply not_init_read].
            simpl in *; cleanup.
        
            eapply H in H14.
            6: eauto.
            2: eauto.
            2: eauto.
            all: eauto.
            cleanup; eauto.
          }
        Unshelve.
        all: eauto.
        Qed.
        
        
        
  Lemma ATC_ORS_transfer:
        forall n T (p1 p2: AD.(prog) T)  u u' ex,
        
        not_init p1 ->
        not_init p2 ->
        
        (forall s1 s2, 
        AD_related_states u' ex s1 s2 ->
        have_same_structure p1 p2 u s1 s2) ->
        
        oracle_refines_same_from_related ATC_Refinement u
        p1 p2 File.recover (ATC_reboot_list n) 
        (AD_related_states u' ex).
        Proof.
          unfold ATC_reboot_list; induction n; intros.
          {
            unfold oracle_refines_same_from_related; intros.
            simpl in *.
            destruct l_o_imp; simpl in *; try tauto.
            cleanup; try tauto.
            simpl in *; repeat split_ors; cleanup; try tauto.
            unfold refines_related at 1 in H2; cleanup; eauto.
            simpl in *. 
            eapply ATC_oracle_refines_impl_eq in H10.
            5: apply H5.
            all: eauto.
            3: apply TD_oracle_refines_operation_eq.
            cleanup; eauto.
            all: shelve.
          }
          {
            unfold oracle_refines_same_from_related; intros.
            simpl in *.
            destruct l_o_imp; simpl in *; try tauto.
            cleanup; try tauto.
            unfold refines_related at 1 in H2; cleanup; eauto.
            simpl in *; repeat split_ors; cleanup; try tauto.
            {
              simpl in *. 
              eapply ATC_oracle_refines_impl_eq in H12.
              5: apply H5.
              all: eauto.
              3: apply TD_oracle_refines_operation_eq.
              cleanup; eauto.
              all: shelve.
            }
            {
              simpl in *.
              exfalso; eapply ATC_oracle_refines_prefix_one_crashed.
              3: eauto.
              3: eauto.
              all: eauto.
              all: shelve.
            }
            {
              simpl in *.
              exfalso; eapply ATC_oracle_refines_prefix_one_crashed.
              3: eauto.
              3: eauto.
              all: eauto.
              all: shelve.
            }
            {
              simpl in *. 
              eapply_fresh ATC_oracle_refines_impl_eq_crashed in H11.
              5: apply H5.
              all: eauto.
              3: apply TD_oracle_refines_operation_eq.
              3: apply TD_oracle_refines_operation_eq_crashed.
              cleanup; eauto.
              eapply ATC_ORS_recover in H10.
              apply H10 in H12; 
              subst; eauto.
              all: shelve.
            }
          }
          Unshelve.
          all: eauto.
          all: try split.
          all: try solve [eapply not_init_compile; eauto].
          all: try solve [ apply H1 in H8; eauto; apply have_same_structure_sym; eauto].
          exact (fun _ _ => True).
          {
            unfold refines_related_reboot in *; cleanup; simpl in *.
            eapply ATC_exec_lift_crashed in H6; eauto;
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
          eapply ATC_exec_lift_crashed in H7; eauto;
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
          cleanup.
        
        
          unfold HC_refines_reboot; simpl;
          unfold HC_refines_reboot; simpl.
          eexists (_, (_, _)), (_, (_, _)).
          simpl; intuition eauto.
          }
          Unshelve.
          all: exact Empty.
        Qed.
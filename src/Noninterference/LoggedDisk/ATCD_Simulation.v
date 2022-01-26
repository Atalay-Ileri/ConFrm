Require Import Lia Framework FSParameters FileDiskLayer FileDiskNoninterference. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import ATC_Simulation Not_Init ATCDLayer. (** TransferProofs. *)
Require Import LoggedDiskRefinement LogCache.RepImplications.
Require Import Coq.Program.Equality.
Require Import Eqdep FunctionalExtensionality.

Set Nested Proofs Allowed.

Fixpoint not_init {T} (p: ATCLang.(prog) T) :=
  match p with
  | Op _ o =>
    match o with
    | P1 _ => True
    | P2 o =>
    match o with
    | P1 _ => True
    | P2 o =>
      (forall l, ~eq_dep Type (operation (LoggedDiskOperation
      log_length
      data_length)) _ o 
      unit (LoggedDiskLayer.Init l))
    end
    end
  | Ret _ => True
  | Bind p1 p2 =>
  not_init p1 /\ forall t, not_init (p2 t)
  end.

Lemma not_init_compile:
forall T (p: AD.(prog) T),
ATC_Simulation.not_init p ->
not_init (Simulation.Definitions.compile ATC_Refinement p).
Proof.
  induction p; simpl; intros; cleanup; simpl; eauto.
  destruct o0; cleanup; simpl; eauto.
  {
    unfold Transaction.read;
    destruct (Compare_dec.lt_dec a FSParameters.data_length); simpl; intuition eauto.
    destruct (Transaction.get_first t a); simpl; intuition eauto.
    inversion H0.
  }
  {
    unfold Transaction.write; simpl;
    destruct (Compare_dec.lt_dec a FSParameters.data_length); simpl; intuition eauto.
    destruct_fresh (Compare_dec.le_dec
    (length (addr_list_to_blocks (map fst t ++ [a])) +
      length (map snd t ++ [v])) FSParameters.log_length); 
      setoid_rewrite D; simpl; intuition eauto.
  }
  all: intuition eauto; inversion H0.
Qed.  

Lemma HC_exec_same_finished:
  forall u T (p: ATCLang.(prog) T) 
  o o0 s_imp s_abs x x0 t,
  not_init p ->
  Language.exec' u o s_imp
 (ATCD_Refinement.(Simulation.Definitions.compile) p)
 (Finished x x0) ->

 oracle_refines _ _ _ _ ATCD_CoreRefinement T u s_imp
 p (fun s  =>
(fst s,
([],
(empty_mem,
(fst (snd (snd (snd s))),
select_total_mem t
 (snd (snd (snd (snd s))))))))) o o0 ->

 ATCD_Refinement.(Simulation.Definitions.refines) s_imp s_abs ->

  (forall u s_imp s_abs T o x x0 x2 x3 x4,
  exec (CachedDiskLang) u x3 s_imp
 (compile T o) (Finished x x0) ->
 token_refines T u s_imp o x4 x3 x2 ->
 refines s_imp s_abs ->
 (forall l, ~eq_dep Type (operation (LoggedDiskOperation
      log_length
      data_length)) _ o 
      unit (LoggedDiskLayer.Init l)) ->
exists s_abs',
LoggedDiskLayer.exec' log_length
data_length
 u x2
  s_abs o (Finished s_abs' x0) /\
refines x s_abs') ->
 exists s_abs' : Recovery_Result,
  recovery_exec ATCLang u [o0] s_abs
    (ATC_reboot_list 0) p
    (ATC_Refinement.(Simulation.Definitions.compile) File.recover) s_abs' /\
    ATCD_Refinement.(Simulation.Definitions.refines) x
    (extract_state_r s_abs') /\
  Some x0 = extract_ret_r s_abs'.
Proof.
  induction p; simpl; intros.
  {
    cleanup; simpl in *.
    {
      invert_exec'' H0.
      invert_exec.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold ATC_reboot_list; simpl.
      eexists (RFinished _ _); split.
      repeat econstructor; eauto.
      simpl; intuition eauto.
    }
    {
      invert_exec'' H0; repeat invert_exec; cleanup;
      simpl in *; cleanup;
      specialize (H4 tt);
      unfold HC_refines in *; simpl in *; cleanup;
      unfold HC_refines in *; simpl in *; cleanup;
      unfold ATC_reboot_list; simpl;
      eexists (RFinished _ _); split.
      repeat econstructor; eauto.
      simpl; intuition eauto.

      repeat econstructor; eauto.
      simpl; intuition eauto.

      repeat econstructor; eauto.
      simpl; intuition eauto.
    }
    {
      eapply lift2_invert_exec in H0; cleanup.
      apply HC_map_ext_eq in H0; subst.
      specialize (e1 tt).
      eapply lift2_invert_exec in H4; cleanup.
      apply HC_map_ext_eq in H0; subst.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold ATC_reboot_list; simpl.
      eapply_fresh H3 in H6; eauto; cleanup.
      eexists (RFinished _ _); split.
      repeat econstructor; eauto.
      simpl; intuition eauto.
      eapply H8; eauto.
      econstructor.
    }
  }
  {
    cleanup; simpl in *.
    split_ors; cleanup; repeat unify_execs; cleanup.
    invert_exec'' H0.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold ATC_reboot_list; simpl.
    eexists (RFinished _ _); split.
    repeat econstructor; eauto.
    simpl; intuition eauto.
  }
  {
    cleanup; simpl in *.
    invert_exec'' H1.
    split_ors; cleanup; simpl in *;
    repeat unify_execs; cleanup.
    {
      exfalso; eapply finished_not_crashed_oracle_prefix in H12.
      apply H12; eauto.
      setoid_rewrite app_nil_r at 2; eauto.
    }
    {
      eapply exec_finished_deterministic_prefix in H6; eauto; cleanup.
      repeat unify_execs; cleanup.

      edestruct IHp; eauto.
      cleanup; invert_exec; simpl in *; cleanup.
      edestruct H; eauto.
      cleanup; invert_exec; simpl in *; cleanup.
      eexists (RFinished _ _); split; eauto.
      repeat econstructor; eauto.
      simpl; eauto.
    }
  }
Qed.

Lemma log_rep_synced:
forall txns s_imp,
Log.log_rep txns s_imp ->
(forall a : nat, a >= data_start -> snd (snd s_imp a) = []) ->
forall (a : addr) (vs : value * list value),
snd s_imp a = vs -> snd vs = [].
Proof.
intros; cleanup.
destruct (Compare_dec.lt_dec a data_start); eauto.
{
  unfold Log.log_rep, Log.log_rep_general,
  Log.log_rep_explicit,
  Log.log_data_blocks_rep,
  Log.log_header_block_rep in *; intros; cleanup.

  destruct a.
  rewrite hdr_block_num_eq in *; eauto.
  eapply H7.
  replace (S a) with (log_start + (S a - log_start)).
  rewrite H2.
  apply in_seln.
  pose proof data_start_where_log_ends.
  rewrite H3. 
  rewrite log_start_eq in *.
  rewrite H in *.
  lia.

  pose proof data_start_where_log_ends.
  rewrite log_start_eq in *.
  rewrite H in *.
  lia.
  rewrite log_start_eq in *; lia.
}
{
  eapply H0; lia.
}
Qed.

Lemma refines_to_refines_reboot_same:
forall s_imp s_abs,
refines s_imp s_abs ->
refines_reboot s_imp s_abs.
Proof.
  intros;
unfold refines, refines_reboot,
LogCache.cached_log_reboot_rep,
LogCache.cached_log_rep in *;
cleanup; eauto.
split.
eexists; intuition eauto.
eapply RepImplications.log_rep_to_reboot_rep_same; eauto.
eapply log_rep_synced; eauto.
Qed.


Lemma refines_to_refines_reboot:
forall s_imp s_abs t,
refines s_imp s_abs ->
refines_reboot
  (empty_mem,
  (fst (snd s_imp),
  select_total_mem t (snd (snd  s_imp)))) 
  s_abs.
Proof.
  intros;
unfold refines, refines_reboot in *;
cleanup; simpl; eauto.
split.
eapply cached_log_rep_to_reboot_rep; eauto.
eapply select_total_mem_synced with (A:= addr); eauto.
Qed.

Lemma refines_reboot_to_refines_reboot:
forall s_imp s_abs a,
refines_reboot s_imp s_abs ->
refines_reboot (empty_mem,
(fst (snd s_imp),
select_total_mem a
  (snd (snd s_imp))))
s_abs.
Proof.
  intros;
unfold refines_reboot in *;
simpl in *; cleanup.
intuition eauto.
apply cached_log_reboot_rep_to_reboot_rep; eauto.
eapply select_total_mem_synced with (A:= addr); eauto.
Qed.

Lemma HC_exec_same_crashed:
  forall u T (p: ATCLang.(prog) T) 
  o o0 s_imp s_abs x t,
  not_init p ->
  Language.exec' u o s_imp
 (ATCD_Refinement.(Simulation.Definitions.compile) p)
 (Crashed x) ->

 oracle_refines _ _ _ _ ATCD_CoreRefinement T u s_imp
 p (fun s =>
(fst s,
([],
(empty_mem,
(fst (snd (snd (snd s))),
select_total_mem t
 (snd (snd (snd (snd s))))))))) o o0 ->

 ATCD_Refinement.(Simulation.Definitions.refines) s_imp s_abs -> 

  (forall u s_imp s_abs T o x x2 x3,
  exec (CachedDiskLang) u x3 s_imp
  (compile T o) (Crashed x) ->
    token_refines T u s_imp o (fun x => (empty_mem, (fst (snd x), select_total_mem t (snd (snd x))))) x3 x2 ->
    refines s_imp s_abs ->
    (forall l, ~eq_dep Type (operation (LoggedDiskOperation
      log_length
      data_length)) _ o 
      unit (LoggedDiskLayer.Init l)) ->
    exists s_abs',
    LoggedDiskLayer.exec' log_length
data_length u x2
      s_abs o (Crashed s_abs') /\
    refines_reboot (empty_mem, (fst (snd x), select_total_mem t (snd (snd x)))) s_abs') ->

    (forall u s_imp s_abs T o x x0 x2 x3 x4,
    exec (CachedDiskLang)  u x3 s_imp
   (compile T o) (Finished x x0) ->
   token_refines T u s_imp o x4 x3 x2 ->
   refines s_imp s_abs ->
   (forall l, ~eq_dep Type (operation (LoggedDiskOperation
      log_length
      data_length)) _ o 
      unit (LoggedDiskLayer.Init l)) ->
        exists s_abs',
        LoggedDiskLayer.exec' log_length
        data_length u x2
    s_abs o (Finished s_abs' x0) /\
  refines x s_abs') ->

 exists s_abs',
 Language.exec' u o0 s_abs p (Crashed s_abs') /\
  refines_reboot 
  (empty_mem, (fst (snd (snd (snd x))), select_total_mem t (snd (snd (snd (snd x)))))) (snd (snd s_abs')).
Proof.
  induction p; simpl; intros.
  {
    cleanup; simpl in *.
    {
      invert_exec'' H0.
      invert_exec.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      eexists; split.
      repeat econstructor; eauto.
      simpl; intuition eauto.
      apply refines_to_refines_reboot; eauto.
    }
    {
      invert_exec'' H0; repeat invert_exec; cleanup;
      simpl in *; cleanup;
      specialize (H5 tt);
      unfold HC_refines in *; simpl in *; cleanup;
      unfold HC_refines in *; simpl in *; cleanup;
      unfold ATC_reboot_list; simpl;
      eexists; split.
      repeat econstructor; eauto.
      simpl; intuition eauto.
      eapply refines_to_refines_reboot; eauto.
    }
    {
      eapply lift2_invert_exec_crashed in H0; cleanup.
      eapply lift2_invert_exec_crashed in H5; cleanup.
      specialize (e1 tt).
      unfold HC_refines in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      repeat apply HC_map_ext_eq in H0; cleanup.
      unfold ATC_reboot_list; simpl.
      eapply H3 in H7; eauto; cleanup.
      eexists; split.
      repeat econstructor; eauto.
      simpl; intuition eauto.
      apply H10; econstructor.
    }
  }
  {
    cleanup; simpl in *.
    split_ors; cleanup; repeat unify_execs; cleanup.
    invert_exec'' H0.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold ATC_reboot_list; simpl.
    eexists; split.
    repeat econstructor; eauto.
    eapply refines_to_refines_reboot; eauto.
  }
  {
    cleanup; simpl in *.
    invert_exec'' H1.
    split_ors; cleanup; simpl in *;
    repeat unify_execs; cleanup.
    {
      exfalso; eapply finished_not_crashed_oracle_prefix in H13; eauto.
      setoid_rewrite app_nil_r at 2; eauto.
    }
    {
      eapply exec_finished_deterministic_prefix in H7; eauto; cleanup.
      repeat unify_execs; cleanup.

      edestruct HC_exec_same_finished; eauto.
      cleanup; invert_exec; simpl in *; cleanup.
      edestruct H; eauto.
      cleanup; simpl in *; cleanup.
      eexists; split; eauto.
      repeat econstructor; eauto.
    }
    {
      split_ors; cleanup; simpl in *;
      repeat unify_execs; cleanup.
      {
        eapply_fresh exec_deterministic_wrt_oracle_prefix in H12; eauto; cleanup.
        edestruct IHp.
        3: eauto.
        eauto.
        eauto.
        all: eauto.
        cleanup.
        eexists; split; eauto.
        solve [econstructor; eauto].
      }
      {
        exfalso; eapply finished_not_crashed_oracle_prefix in H7; eauto.
        setoid_rewrite app_nil_r at 2; eauto.
      }
    }
  }
  Unshelve.
  eauto.
Qed.

Opaque LogCache.recover.
Theorem ATCD_recover_simulation:
forall u l_selector,
SimulationForProgramGeneral _ _ _ _ ATCD_Refinement 
u _
  (ATC_Refinement.(Simulation.Definitions.compile) File.recover) 
  (ATC_Refinement.(Simulation.Definitions.compile) File.recover)
  (ATCD_reboot_list l_selector)
  (ATC_reboot_list (length l_selector))
  (fun s1 s2 => refines_reboot (snd (snd s1)) (snd (snd s2)))
  ATCD_Refinement.(Simulation.Definitions.refines).
  Proof.
      unfold File.recover, 
      SimulationForProgram,
      SimulationForProgramGeneral,
      ATCD_reboot_list. 
      induction l_selector; simpl in *; intros.
      {
          repeat invert_exec.
          simpl in *; cleanup; try tauto.
          destruct l; simpl in *; try lia.
          split_ors; cleanup; repeat unify_execs; cleanup.
          specialize (H2 (fun s => s)); cleanup.
          invert_exec'' H8; repeat invert_exec.
          invert_exec'' H9; repeat invert_exec.

          simpl in *; cleanup.
          split_ors; cleanup.
          inversion H4; subst.
          invert_exec'' H; repeat invert_exec.
          invert_exec'' H2; repeat invert_exec.
          simpl in *; cleanup.
          rewrite <- H4 in H1.
          inversion H1; cleanup.

          invert_exec'' H; repeat invert_exec.
          simpl in *; cleanup.
          rewrite <- H in H5.
          simpl in *; cleanup.
          unify_execs; cleanup.
          specialize (H9 tt).
          specialize (H13 tt).
          eapply lift2_invert_exec in H12; cleanup.
          eapply lift2_invert_exec in H4; cleanup.
          simpl in *; cleanup.
          repeat apply HC_map_ext_eq in H1; eauto; cleanup.
          specialize (o []).
          split_ors; cleanup; try unify_execs; cleanup.
          simpl in *.
          eexists (RFinished _ _); intuition eauto.
          econstructor.
          rewrite cons_app; repeat econstructor; eauto.
          unfold HC_refines; simpl.
          unfold HC_refines; simpl.
          unfold refines, refines_reboot in *;
          cleanup; eauto.
          intuition eauto.
          repeat cleanup_pairs; eauto.
          destruct s6, s; eauto.
      }
      {
        repeat invert_exec.
          simpl in *; cleanup; try tauto.
          split_ors; cleanup; repeat unify_execs; cleanup.
          invert_exec'' H11; repeat invert_exec.
          {
            invert_exec'' H9; repeat invert_exec.
            unfold HC_refines in *; simpl in *;
            split_ors; cleanup; try unify_execs; cleanup.
            specialize (H6 tt).
            simpl in *; cleanup; try congruence.
            simpl in *; cleanup.
            exfalso; eapply exec_empty_oracle; eauto.
            
            specialize (H10 tt).
            specialize (H15 tt).
            invert_exec'' H4; repeat invert_exec.
            simpl in *; cleanup.

          simpl in *; cleanup.
          unify_execs; cleanup.
          eapply lift2_invert_exec_crashed in H14; cleanup.
          eapply lift2_invert_exec_crashed in H4; cleanup.
          simpl in *.
          repeat eapply HC_map_ext_eq in H1; eauto; cleanup.
          specialize (H8 []).
          split_ors; cleanup; try unify_execs; cleanup.
          simpl in *.
          rewrite <- H5 in *; clear H5.
          unfold TCD_reboot_list  in *; simpl in *.
          unfold refines_reboot in *; simpl in *; cleanup.
          edestruct IHl_selector; eauto.
            simpl; intuition eauto. 
            instantiate (1:= (fst s_abs, ([], snd (snd s_abs)))).
            apply H7 in H0; repeat split_ors; cleanup.
            eapply cached_log_reboot_rep_to_reboot_rep; eauto.
            eapply cached_log_crash_rep_during_recovery_to_reboot_rep; eauto.
            eapply cached_log_crash_rep_after_commit_to_reboot_rep; eauto.
            eapply select_total_mem_synced with (A:= addr); eauto.

            eexists (Recovered _).
            simpl; intuition eauto.
            econstructor.
            rewrite cons_app; repeat econstructor.
            simpl; repeat econstructor; eauto.
          }
          {
            invert_exec'' H8; repeat invert_exec.
              unfold HC_refines in *; simpl in *;
              split_ors; cleanup; try unify_execs; cleanup.
            
              specialize (H6 tt).
              invert_exec'' H1; repeat invert_exec; cleanup.
              simpl in *; cleanup.
              edestruct IHl_selector; simpl; eauto.
              simpl; intuition eauto.
              instantiate (1:= (fst s_abs, ([], snd (snd s_abs)))).
              eapply refines_reboot_to_refines_reboot; eauto.
              eexists (Recovered _).
              simpl; intuition eauto.
              econstructor.
              repeat econstructor.
              simpl; repeat econstructor; eauto.

              invert_exec'' H4; repeat invert_exec; simpl in *; cleanup.
              rewrite <- H2 in H1; simpl in *; cleanup.
          }
      }
      Unshelve.
  all: exact ATCDLang.
  Qed.

  Theorem HC_recovery_exec_same:
      forall u T (p: ATCLang.(prog) T) l_selector 
      l_o_imp l_o_abs s_imp s_abs s_imp',
    not_init p ->
      recovery_exec ATCDLang u l_o_imp s_imp (ATCD_reboot_list l_selector)
      (Simulation.Definitions.compile ATCD_Refinement p)
      (Simulation.Definitions.compile ATCD_Refinement 
      (Simulation.Definitions.compile ATC_Refinement File.recover)) s_imp' ->

      recovery_oracles_refine_to ATCD_Refinement u
      s_imp p (Simulation.Definitions.compile ATC_Refinement File.recover) 
      (ATCD_reboot_list l_selector) l_o_imp l_o_abs ->

      Simulation.Definitions.refines
       ATCD_Refinement s_imp
       s_abs ->

       (forall u s_imp s_abs T o x x0 x2 x3 x4,
       exec (CachedDiskLang)  u x3 s_imp
      (compile T o) (Finished x x0) ->
      token_refines T u s_imp o x4 x3 x2 ->
      refines s_imp s_abs ->
      (forall l, ~eq_dep Type (operation (LoggedDiskOperation
         log_length
         data_length)) _ o 
         unit (LoggedDiskLayer.Init l)) ->
           exists s_abs',
           LoggedDiskLayer.exec' log_length
           data_length u x2
       s_abs o (Finished s_abs' x0) /\
     refines x s_abs') ->

       (forall u s_imp s_abs T o x x2 x3 t,
  exec (CachedDiskLang) u x3 s_imp
  (compile T o) (Crashed x) ->
    token_refines T u s_imp o (fun x => (empty_mem, (fst (snd x), select_total_mem t (snd (snd x))))) x3 x2 ->
    refines s_imp s_abs ->
    (forall l, ~eq_dep Type (operation (LoggedDiskOperation
      log_length
      data_length)) _ o 
      unit (LoggedDiskLayer.Init l)) ->
    exists s_abs',
    LoggedDiskLayer.exec' log_length
data_length u x2
      s_abs o (Crashed s_abs') /\
    refines_reboot (empty_mem, (fst (snd x), select_total_mem t (snd (snd x)))) s_abs') ->

      exists s_abs' : Recovery_Result,
      recovery_exec ATCLang u l_o_abs s_abs
      (ATC_reboot_list (length l_selector)) p (Simulation.Definitions.compile ATC_Refinement File.recover) s_abs' /\
      Simulation.Definitions.refines ATCD_Refinement (extract_state_r s_imp')
    (extract_state_r s_abs') /\ extract_ret_r s_imp' = extract_ret_r s_abs'.
    Proof.
      intros; destruct l_selector.
      {
        invert_exec.
        simpl in *; cleanup; try tauto.
        destruct l; simpl in *; try lia.
        split_ors; cleanup; repeat unify_execs; cleanup.
        eapply HC_exec_same_finished; eauto.
      }
      {
        unfold ATCD_reboot_list in *; invert_exec.
        simpl in *; cleanup; try tauto.
        split_ors; cleanup; repeat unify_execs; cleanup.
        simpl in *.
        edestruct HC_exec_same_crashed; eauto; cleanup.

        edestruct ATCD_recover_simulation.
        eauto.
        instantiate (1:= (fst x0, ([], snd (snd x0)))).
        simpl; eauto. 
        eauto.
        cleanup.
        eexists (Recovered _); split.
        unfold ATC_reboot_list, 
        Refinement.transaction_cache_reboot_list in *; simpl in *; 
        econstructor; eauto.
           unfold HC_refines in *; simpl in *; cleanup.
        simpl; split; eauto.
        }
      Unshelve.
      exact (fun _ => 0).
Qed.


Lemma operation_simulation_finished:
forall (u : user) (s_imp : Language.state' CachedDiskOperation)
(s_abs : state Definitions.abs) (T : Type)
(o : operation Definitions.abs_core T)
(x : Language.state' CachedDiskOperation) (x0 : T)
(x2 : LoggedDiskLayer.token') (x3 : oracle' CachedDiskOperation)
(x4 : Language.state' CachedDiskOperation -> state CachedDiskLang),
exec CachedDiskLang u x3 s_imp (compile T o) (Finished x x0) ->
token_refines T u s_imp o x4 x3 x2 ->
refines s_imp s_abs ->
(forall l : list (addr * value),
~
eq_dep Type (operation (LoggedDiskOperation log_length data_length)) T
 o unit (Init l)) ->
exists s_abs' : LoggedDiskLayer.state',
LoggedDiskLayer.exec' log_length data_length u x2 s_abs o
  (Finished s_abs' x0) /\ refines x s_abs'.
    Proof. (*
      intros; destruct o.
      {
        edestruct Simulations.read_simulation with (l_selector:= nil: list (@total_mem addr addr_dec nat)); eauto.
        2: {
          instantiate (1:= RFinished _ _).
          eapply ExecFinished; eauto.
          simpl in *; eauto.
         }
         instantiate (1:= [ _ ]). 
         simpl; eauto.
         split; eauto.
         left; do 2 eexists; intuition eauto.
         cleanup; simpl in *.
         repeat invert_exec; simpl in *; cleanup.
        invert_exec'' H12.
         eexists; split; eauto.
      }
      {
        edestruct Simulations.write_simulation with (l_selector:= nil: list (@total_mem addr addr_dec nat)); eauto.
        2: {
          instantiate (1:= RFinished _ _).
          eapply ExecFinished; eauto.
          simpl in *; eauto.
         }
         instantiate (1:= [ _ ]). 
            simpl in *; eauto.
         split; eauto.
         left; do 2 eexists; intuition eauto.
         cleanup.
         eexists; intuition eauto.
         apply H0 in H3.
         repeat split_ors; cleanup; try unify_execs; cleanup.
         unfold logged_disk_reboot_list  in *; simpl in *.
         cleanup; simpl in *.
         repeat invert_exec; simpl in *; cleanup.
        (* invert_exec'' H12. *)
         intros; left; 
         eexists; intuition eauto.
         repeat split_ors; cleanup; try unify_execs; cleanup.
         cleanup; simpl in *.
         repeat invert_exec; simpl in *; cleanup.
        invert_exec'' H12.
         eexists; split; eauto.
      }
      {
        edestruct Simulations.recovery_simulation with (l_selector:= nil: list (@total_mem addr addr_dec nat)); eauto.
        3: {
          instantiate (1:= RFinished _ _).
          eapply ExecFinished; eauto.
         }
          instantiate (1:= [ _ ]). 
            simpl; eauto.
         split; eauto.
         left; do 2 eexists; intuition eauto.
         apply refines_to_refines_reboot_same; eauto.
         cleanup; simpl in *.
         repeat invert_exec; simpl in *; cleanup.
        invert_exec'' H12.
         eexists; split; eauto.
      }
      {
        exfalso.
        eapply H2.
        eauto.
      }
    Qed. 
*)
    Admitted.

Lemma operation_simulation_crashed:
forall u s_imp s_abs T o x x2 x3 t,
exec (CachedDiskLang) u x3 s_imp
(compile T o) (Crashed x) ->
  token_refines T u s_imp o (fun x => (empty_mem, (fst (snd x), select_total_mem t (snd (snd x))))) x3 x2 ->
  refines s_imp s_abs ->
  (forall l, ~eq_dep Type (operation (LoggedDiskOperation
    log_length
    data_length)) _ o 
    unit (LoggedDiskLayer.Init l)) ->
  exists s_abs',
  LoggedDiskLayer.exec' log_length
data_length u x2
    s_abs o (Crashed s_abs') /\
  refines_reboot (empty_mem, (fst (snd x), select_total_mem t (snd (snd x)))) s_abs'.
    Proof. (*
      intros; destruct o; simpl in *.
      {
        intuition cleanup;
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.

        eexists; intuition eauto.
        repeat econstructor.
        unfold refines, refines_reboot in *; cleanup; 
        eapply H4 in H1.
        split.
        eapply cached_log_rep_to_reboot_rep; eauto.
        unfold LogCache.cached_log_rep in *; cleanup. 
        simpl; eapply select_total_mem_synced.
      }
      {
        intuition cleanup.
        apply H0 in H1.
        repeat split_ors; cleanup;
        repeat split_ors; cleanup; try unify_execs; cleanup.
        {
          eexists; split; [repeat econstructor |]; eauto.
          unfold refines, refines_reboot in *; cleanup.
          split; try solve [simpl; eapply select_total_mem_synced]. 
          repeat split_ors.
            eapply cached_log_rep_to_reboot_rep; eauto.
            eapply cached_log_crash_rep_during_apply_to_reboot_rep; eauto.
            eapply cached_log_crash_rep_after_apply_to_reboot_rep; eauto.
        }
        {
          unfold refines, refines_reboot in *; cleanup.
          eexists; split; [repeat econstructor |]; eauto.
          split; try solve [simpl; eapply select_total_mem_synced]. 
          eapply cached_log_crash_rep_after_commit_to_reboot_rep; eauto.
        }

        {
          unfold refines, refines_reboot in *; cleanup.
          split_ors; cleanup.
          eexists; split; [repeat econstructor |]; eauto.
          split; try solve [simpl; eapply select_total_mem_synced].
          eauto.

          eexists; split; [repeat econstructor |]; eauto.
          split; try solve [simpl; eapply select_total_mem_synced]; eauto.
        }
      }
      {
        intuition cleanup;
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.
        eexists; intuition eauto.
        repeat econstructor.
        unfold refines, refines_reboot in *; cleanup.
        eapply cached_log_rep_to_reboot_rep_same in H1; eauto.
        eapply H4 in H1.
        split.
        repeat split_ors.
        eapply cached_log_reboot_rep_to_reboot_rep; eauto.
        eapply cached_log_crash_rep_during_recovery_to_reboot_rep; eauto.
        eapply cached_log_crash_rep_after_commit_to_reboot_rep; eauto.
        simpl; eapply select_total_mem_synced.
      }
      { exfalso; eapply H2; eauto. }
    Unshelve.
    all: eauto.
  Qed.
*) Admitted.

Theorem ATCD_simulation:
forall u l_selector T (p: ATCLang.(prog) T),
not_init p ->
SimulationForProgram ATCD_Refinement u
  p (ATC_Refinement.(Simulation.Definitions.compile) File.recover)
  (ATCD_reboot_list l_selector)
  (ATC_reboot_list (length l_selector)).
  Proof.
    unfold SimulationForProgram,
    SimulationForProgramGeneral; 
    intros.
    eapply HC_recovery_exec_same; eauto.
    eapply operation_simulation_finished.
    eapply operation_simulation_crashed.
  Qed.

  Lemma LD_token_refines_finished:
  forall u T o s orc s' r ,
  exec Definitions.impl u orc s (compile T o) (Finished s' r) ->
  exists t, 
  forall (s0: AuthenticationLayer.state')
  (s1: state' (addr * value)) 
  (grs: HorizontalComposition.state' AuthenticationOperation TCDCore ->
  HorizontalComposition.state' AuthenticationOperation TCDCore),
  token_refines T u s o 
  (fun s2: HorizontalComposition.state' (CacheOperation addr_dec value)
  CryptoDiskOperation => snd (snd (grs (s0, (s1, s2))))) orc t.
  Proof. (*
    intros; destruct o; simpl in *;
    eexists; left; do 2 eexists; intuition eauto.
    eapply LogCache.read_finished in H; eauto; cleanup; eauto.
    eapply LogCache.write_finished in H; eauto; cleanup; eauto.
    split_ors; cleanup; eauto.
    destruct r; eauto.
    eapply LogCache.recover_finished in H; eauto; cleanup; eauto.
    destruct r; eauto.
    eapply LogCache.init_finished in H; eauto; cleanup; eauto.
    repeat rewrite map_length; eauto.
    eapply LogCache.init_finished in H; eauto; cleanup; eauto.
  Qed.
*) Admitted.

Lemma cached_log_rep_eq:
forall s m1 m2,
LogCache.cached_log_rep m1 s ->
LogCache.cached_log_rep m2 s ->
m1 = m2.
Proof.
  unfold LogCache.cached_log_rep; intros; cleanup.
  eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H0.
  repeat rewrite total_mem_map_shift_comm.
  repeat rewrite total_mem_map_fst_list_upd_batch_set.
  setoid_rewrite H0; eauto.
  all: eapply LogCache.log_rep_forall2_txns_length_match; eauto.
Qed.

  Lemma LD_token_refines_crashed:
  forall u T o s orc s' selector,
  exec Definitions.impl u orc s (compile T o) (Crashed s') ->
  ( forall l : list (addr * value),
  ~ eq_dep Type logged_disk_prog T o unit (Init l)) ->
  (exists merged_disk, LogCache.cached_log_rep merged_disk s) ->
  non_colliding_selector selector (snd s') ->
  forall (s0: AuthenticationLayer.state')
  (s1: state' (addr * value)) 
  (grs: HorizontalComposition.state' AuthenticationOperation TCDCore ->
  HorizontalComposition.state' AuthenticationOperation TCDCore),
  exists t, token_refines T u s o 
  (fun s0 => (empty_mem, (fst (snd s0), 
select_total_mem selector (snd (snd s0))))) orc t.
  Proof. (*
    intros; destruct o; simpl in *.
    {
      eapply_fresh LogCache.read_crashed in H; eauto; cleanup; eauto.
      eexists; right; eexists; intuition eauto.
    }
    { 
      cleanup;
      eapply_fresh LogCache.write_crashed in H; eauto; cleanup; eauto.
      repeat split_ors; cleanup.
      {
        eexists; intros; right; intuition eauto.
        eexists; left; intuition eauto.
        eapply cached_log_rep_eq in H1; eauto; cleanup; eauto.
      }
      repeat split_ors; cleanup.
      {
        eapply_fresh cached_log_crash_rep_during_commit_to_reboot_rep in H2; eauto.
        split_ors; cleanup.
        eexists; intros; right; intuition eauto.
        eexists; right; right; intuition eauto.
        eapply cached_log_rep_eq in H1; eauto; cleanup; eauto.
        eapply cached_log_rep_eq in H1; eauto; cleanup; eauto.

        eexists; intros; right; intuition eauto.
        eexists; right; right; intuition eauto.
        eapply cached_log_rep_eq in H1; eauto; cleanup; eauto.
        eapply cached_log_rep_eq in H1; eauto; cleanup; eauto.
        right; intuition eauto.
        erewrite addr_list_to_blocks_length_eq; eauto.
        rewrite map_length; eauto.
      }
      {
        eexists; intros; right; intuition eauto.
        eexists; right; left; intuition eauto.
        eapply cached_log_rep_eq in H1; eauto; cleanup; eauto.
        erewrite addr_list_to_blocks_length_eq; eauto.
        rewrite map_length; eauto.
      }
      {
        eexists; intros; right; intuition eauto.
        eexists; left; intuition eauto.
        eapply cached_log_rep_eq in H1; eauto; cleanup; eauto.
      }
      {
        eexists; intros; right; intuition eauto.
        eexists; left; intuition eauto.
        eapply cached_log_rep_eq in H1; eauto; cleanup; eauto.
      }
    }
    {
      cleanup.
      eexists; right; eexists; eauto.
      repeat (split; eauto).
      intros; 
      eapply_fresh LogCache.recover_crashed in H; eauto; cleanup; eauto.
    }
    intuition eauto.
Qed.
*) Admitted.

Lemma ATCD_oracle_refines_finished:
forall T (p: ATCLang.(prog) T) u (o : oracle' ATCDCore)
s s' r,
(exists s1,
@HC_refines _ _ _ _ ATCDLang 
ATCLang TCD_CoreRefinement s s1) ->
exec ATCDLang u o s
(ATCD_Refinement.(Simulation.Definitions.compile) p) (Finished s' r) ->

exists oa,
forall grs,
oracle_refines ATCDCore ATCCore
ATCDLang ATCLang ATCD_CoreRefinement
T u s p grs o oa.
Proof.
induction p; simpl in *; intros.
{
destruct o.
{
  cleanup; invert_exec'' H0;
  repeat invert_exec.
  
  do 2 eexists; intuition eauto.
  simpl.
  eexists; intuition eauto.
  
  do 2 eexists; intuition eauto.
  simpl.
  eexists; intuition eauto.
}
{
  destruct o.
  {
    cleanup; invert_exec'' H0;
    repeat invert_exec.
    
    eexists; intuition eauto.
    simpl.
    eexists; intuition eauto.
    do 2 eexists; intuition eauto.
    
    eexists; intuition eauto.
    simpl.
    eexists; intuition eauto.
    do 2 eexists; intuition eauto.

    eexists; intuition eauto.
    simpl.
    eexists; intuition eauto.
    do 2 eexists; intuition eauto.
    eexists; intuition eauto.
    eexists; intuition eauto.
    simpl.
    do 2 eexists; intuition eauto.
    simpl; eauto.
  }
  {
    eapply lift2_invert_exec in H0; cleanup.
    eapply lift2_invert_exec in H2; cleanup.
    edestruct LD_token_refines_finished; eauto.
    eexists; intuition eauto.
    eexists; intuition eauto.
    simpl.
  do 2 eexists; intuition eauto.
  do 2 eexists; intuition eauto.
  }
}
}
{
eexists; right; eauto.
}
{
cleanup.
repeat invert_exec.
edestruct IHp; eauto.
eapply_fresh exec_compiled_preserves_refinement_finished in H1; eauto.
simpl in *; cleanup.
edestruct H; eauto.
eexists.
right.
do 7 eexists; intuition eauto.
}
Qed.

Lemma ATCD_oracle_refines_crashed:
forall T (p: ATCLang.(prog) T) u (o : oracle' ATCDCore) selector
s s',
(exists s1,
@HC_refines _ _ _ _ ATCDLang 
ATCLang TCD_CoreRefinement s s1) ->
exec ATCDLang u o s
(ATCD_Refinement.(Simulation.Definitions.compile) p) (Crashed s') ->

not_init p ->
non_colliding_selector selector (snd (snd (snd s'))) ->
exists oa,
oracle_refines ATCDCore ATCCore
ATCDLang ATCLang ATCD_CoreRefinement
T u s p (fun s0 => (fst s0, ([], (empty_mem, (fst (snd (snd (snd s0))), 
select_total_mem selector (snd (snd (snd (snd s0)))))))))  o oa.

Proof.
induction p; simpl in *; intros.
{
  destruct o.
  {
    cleanup; invert_exec'' H0;
    repeat invert_exec.
    
    do 2 eexists; intuition eauto.
    simpl.
    eexists; intuition eauto.
  }
  {
  destruct o.
  {
    cleanup; invert_exec'' H0;
    repeat invert_exec.
    
    eexists; intuition eauto.
    simpl.
    eexists; intuition eauto.
    do 2 eexists; intuition eauto.
    simpl; eauto.
  }
  {
    eapply lift2_invert_exec_crashed in H0; cleanup.
    eapply lift2_invert_exec_crashed in H4; cleanup.
    unfold HC_refines in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      unfold refines in *; simpl in *; cleanup.
    edestruct LD_token_refines_crashed; eauto.
    exact tt.
    exact [].
  do 2 eexists; intuition eauto.
  do 2 eexists; intuition eauto.
  do 2 eexists; intuition eauto.
  }
}
}
{
  eexists; left; eauto.
}
{
  cleanup.
  repeat invert_exec.
  split_ors; cleanup.
  {
    edestruct IHp; eauto.
  }
  {
    eapply_fresh ATCD_oracle_refines_finished in H5; eauto; cleanup.
    eapply_fresh exec_compiled_preserves_refinement_finished in H5; eauto.
    simpl in *; cleanup.
    edestruct H; eauto.
    eexists.
    right.
    do 7 eexists; intuition eauto.
  }
}
Qed.

Lemma ATCD_exec_lift_finished:
  forall T (p: ATCLang.(prog) T) u o_imp o_abs s_imp s_abs s_imp' r grs,
  exec ATCDLang u o_imp s_imp
  (ATCD_Refinement.(Simulation.Definitions.compile) p) (Finished s_imp' r) ->
  ATCD_Refinement.(Simulation.Definitions.refines) s_imp s_abs ->
  oracle_refines ATCDCore ATCCore
  ATCDLang ATCLang ATCD_CoreRefinement T u s_imp p grs o_imp o_abs ->
  
  not_init p ->

  exists s_abs', 
  exec ATCLang u o_abs s_abs p (Finished s_abs' r) /\
  ATCD_Refinement.(Simulation.Definitions.refines) s_imp' s_abs'.
  Proof.
    induction p; simpl; intros; eauto.
    {
      cleanup.
      destruct o0; simpl in *; repeat invert_exec;
      cleanup.
      {
      destruct s_abs.
      eexists; intuition eauto.
      repeat econstructor; eauto.
      }
      {
      destruct s_abs.
      eexists; intuition eauto.
      repeat econstructor; eauto.
      }
      {
        simpl in *; cleanup.
        specialize (H4 tt); 
        simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        destruct o1; simpl in *; repeat invert_exec;
        cleanup; simpl in *; cleanup.
        {
          destruct s_abs.
          eexists; split.
          repeat econstructor; eauto.
          repeat cleanup_pairs; eauto.
        }
        {
          destruct s_abs.
          eexists; split.
          repeat econstructor; eauto.
          repeat cleanup_pairs; eauto.
        }
        {
          destruct s_abs.
          eexists; split.
          repeat econstructor; eauto.
          repeat cleanup_pairs; eauto.
        }
      }
      {
        simpl in *; cleanup.
        specialize (H4 tt); cleanup.
        eapply lift2_invert_exec in H; cleanup.
        apply HC_map_ext_eq in H; subst.
        eapply lift2_invert_exec in H3; cleanup.
        apply HC_map_ext_eq in H; subst.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        edestruct operation_simulation_finished; eauto; cleanup.

        eexists; split.
        repeat econstructor.
        intuition eauto.
        simpl; intuition eauto.
      }
    }
    {
      split_ors; cleanup; unify_execs; cleanup.
      repeat invert_exec.
      eexists. 
      split.
      repeat econstructor.
      intuition eauto.
    }
    {
      invert_exec;
      split_ors; cleanup; try unify_execs; cleanup.
      exfalso; eapply finished_not_crashed_oracle_prefix.
      eauto.
      2: eauto.
      rewrite <- app_assoc; eauto.
      eapply exec_finished_deterministic_prefix in H0; eauto; cleanup.
      eapply exec_deterministic_wrt_oracle in H5; eauto; cleanup.
      simpl in *.
      edestruct IHp; eauto; cleanup.
      edestruct H; eauto; cleanup.
      eexists; split; eauto.
      econstructor; eauto.
    }
    Unshelve.
    econstructor.
    eauto.
  Qed.



Lemma ATCD_exec_lift_crashed:
  forall T (p: ATCLang.(prog) T) u o_imp o_abs s_imp s_abs s_imp' selector,
  exec ATCDLang u o_imp s_imp
  (ATCD_Refinement.(Simulation.Definitions.compile) p) (Crashed s_imp') ->
  ATCD_Refinement.(Simulation.Definitions.refines) s_imp s_abs ->
  oracle_refines ATCDCore ATCCore
  ATCDLang ATCLang ATCD_CoreRefinement T u s_imp p (ATCD_reboot_f selector) o_imp o_abs ->

  not_init p ->
  exists s_abs', 
  exec ATCLang u o_abs s_abs p (Crashed s_abs') /\
  ATCD_refines_reboot selector s_imp' s_abs'.
  Proof.
    unfold ATCD_refines_reboot; induction p; simpl; intros; eauto.
    {
      cleanup_no_match.
      destruct o; simpl in *; repeat invert_exec;
      cleanup.
      {
      unfold HC_refines in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      destruct s_abs.
      eexists; intuition eauto.
      repeat econstructor; eauto.
      simpl; apply refines_to_refines_reboot; eauto.
      }
      {
        apply HC_map_ext_eq in H3; subst.
        specialize (H4 tt).
        unfold HC_refines in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        destruct o0; simpl in *; repeat invert_exec;
        cleanup.
        eexists; split;[
        repeat econstructor; eauto
        |intuition eauto;
        simpl; intuition eauto;
        repeat cleanup_pairs;
      simpl; apply refines_to_refines_reboot; eauto].

        eexists; split;[
        repeat econstructor; eauto
        |intuition eauto;
        simpl; intuition eauto;
        repeat cleanup_pairs;
        
      simpl; apply refines_to_refines_reboot; eauto].

        eexists; split;[
        repeat econstructor; eauto
        |intuition eauto;
        simpl; intuition eauto;
        repeat cleanup_pairs;
        
      simpl; apply refines_to_refines_reboot; eauto].
      }
      {
        apply HC_map_ext_eq in H3; subst.
        specialize (H4 tt).
        simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        eapply lift2_invert_exec_crashed in H6; cleanup.
        apply HC_map_ext_eq in H4; subst.
        edestruct operation_simulation_crashed; eauto.
        eapply H3; eauto.
        constructor.

        cleanup; simpl in *.
        eexists; split.
        repeat econstructor; eauto.
        simpl; intuition eauto.
      }
    }
    {
      split_ors; cleanup; unify_execs; cleanup.
      repeat invert_exec.
      eexists. 
      split.
      repeat econstructor.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      intuition eauto.
      simpl; apply refines_to_refines_reboot; eauto.
    }
    {
      invert_exec;
      repeat split_ors; cleanup; try unify_execs; cleanup.
      edestruct IHp; eauto; cleanup.
      eexists; split.
      econstructor; eauto.
      simpl in *; eauto.

      exfalso; eapply finished_not_crashed_oracle_prefix.
        eauto.
        2: eauto.
        rewrite <- app_assoc; eauto.

          eapply finished_not_crashed_oracle_prefix in H6.
        exfalso; apply H6; eauto.
        rewrite <- app_assoc; eauto.

        eapply exec_finished_deterministic_prefix in H10; eauto; cleanup.
        eapply exec_deterministic_wrt_oracle in H11; eauto; cleanup.
        eapply ATCD_exec_lift_finished in H6; eauto; cleanup.
        edestruct H; eauto; cleanup.
        eexists; split.
        econstructor; eauto.
        simpl in *; eauto.
    }
    Unshelve.
    all: eauto.
  Qed.

Lemma ATCD_exec_lift_finished_recovery:
forall u o_imp o_abs s_imp s_abs s_imp' r grs,
exec ATCDLang u o_imp s_imp
(ATCD_Refinement.(Simulation.Definitions.compile) 
(ATC_Refinement.(Simulation.Definitions.compile) (File.recover))) (Finished s_imp' r) ->
refines_reboot (snd (snd s_imp)) (snd (snd s_abs)) ->
fst s_imp  = fst s_abs ->
fst (snd s_imp)  = fst (snd s_abs) ->

oracle_refines ATCDCore ATCCore
ATCDLang ATCLang ATCD_CoreRefinement 
_ u s_imp (ATC_Refinement.(Simulation.Definitions.compile) (File.recover)) grs o_imp o_abs ->

exists s_abs', 
exec ATCLang u o_abs s_abs (ATC_Refinement.(Simulation.Definitions.compile) (File.recover)) (Finished s_abs' r) /\
ATCD_Refinement.(Simulation.Definitions.refines) s_imp' s_abs'.
Proof.
  simpl; intros; eauto.
  cleanup; simpl in *.
  simpl in *.
  repeat invert_exec; cleanup.
  split_ors; cleanup; repeat invert_exec; cleanup.
  rewrite <- H3 in H8. simpl in H8.
  inversion H8; cleanup.
  specialize (H13 tt).
  specialize (H16 tt).
  simpl in *; cleanup.
  simpl in *; cleanup.
  repeat eapply HC_map_ext_eq in H10; cleanup.
  specialize (H11 []).
  split_ors; cleanup; repeat unify_execs; cleanup.
  unfold refines_reboot in *; cleanup.
  destruct s_abs.
  eexists; split.
  rewrite cons_app;
  repeat econstructor; eauto.
  simpl in *.
  unfold HC_refines; simpl; intuition eauto.
  unfold HC_refines; simpl; intuition eauto.
  unfold refines; simpl; intuition eauto.
Qed.

Lemma ATCD_exec_lift_crashed_recovery:
forall u o_imp o_abs s_imp s_abs s_imp' selector,
exec ATCDLang u o_imp s_imp
(ATCD_Refinement.(Simulation.Definitions.compile) 
(ATC_Refinement.(Simulation.Definitions.compile) (File.recover))) (Crashed s_imp') ->
refines_reboot (snd (snd s_imp)) (snd (snd s_abs)) ->
fst s_imp  = fst s_abs ->
fst (snd s_imp)  = fst (snd s_abs) ->

oracle_refines ATCDCore ATCCore
ATCDLang ATCLang ATCD_CoreRefinement 
_ u s_imp (ATC_Refinement.(Simulation.Definitions.compile) (File.recover)) (ATCD_reboot_f selector) o_imp o_abs ->

exists s_abs', 
exec ATCLang u o_abs s_abs (ATC_Refinement.(Simulation.Definitions.compile) (File.recover)) (Crashed s_abs') /\
ATCD_refines_reboot selector s_imp' s_abs'.
Proof.
  unfold ATCD_refines_reboot; simpl; intros; eauto.
  cleanup; simpl in *.
  simpl in *.
  repeat invert_exec; cleanup.
  repeat split_ors; cleanup; repeat invert_exec; cleanup.
  {
    specialize (H7 tt).
  simpl in *; cleanup.
  simpl in *; cleanup.
  destruct s_abs.
  eexists; split.
  repeat econstructor; eauto.
  simpl in *; intuition eauto.
  eapply refines_reboot_to_refines_reboot; eauto.
  } 
  {
    simpl in *; cleanup.
    rewrite <- H in H6; clear H; simpl; cleanup.
  }
  {
    specialize (H11 tt).
    specialize (H14 tt).
  simpl in *; cleanup.
  simpl in *; cleanup; congruence.
  }
  {
    specialize (H11 tt).
    specialize (H14 tt).
  simpl in *; cleanup.
  simpl in *; cleanup.
  repeat eapply HC_map_ext_eq in H10; cleanup.
  specialize (H11 []).
  split_ors; cleanup; repeat unify_execs; cleanup.
    destruct s_abs.
    eexists; split.
    rewrite cons_app;
    repeat econstructor; eauto.
    simpl; intuition eauto.
    unfold refines_reboot in *; cleanup.
    simpl in *; split.
    eapply H4 in H0; repeat split_ors.
    eapply cached_log_reboot_rep_to_reboot_rep; eauto.
    eapply cached_log_crash_rep_during_recovery_to_reboot_rep; eauto.
    eapply cached_log_crash_rep_after_commit_to_reboot_rep; eauto.
    eapply select_total_mem_synced; eauto.
  }
Qed.

Lemma ATCD_simulation_crash:
forall u grs T (p: ATCLang.(prog) T) o s s',
(exists s1, Simulation.Definitions.refines ATCD_Refinement s s1) ->
exec ATCDLang u o s
  (Simulation.Definitions.compile ATCD_Refinement p) (Crashed s') ->
not_init p ->
non_colliding_selector grs (snd (snd (snd s'))) ->
exists s1', ATCD_refines_reboot grs s' s1'.
Proof.
  intros; cleanup.
  eapply_fresh ATCD_oracle_refines_crashed in H0; eauto.
  cleanup.
  eapply ATCD_exec_lift_crashed in H0; eauto.
  cleanup; simpl in *; eauto.
  simpl in *; eauto.
Qed.
Require Import Framework FSParameters TotalMem.
Require Import TransactionCacheLayer TransactionalDiskLayer Transaction.
Close Scope predicate_scope.
Import ListNotations.

Local Definition imp_op := TransactionCacheOperation.
Local Definition abs_op := (TransactionalDiskOperation data_length).
Local Definition imp := TransactionCacheLang.
Local Definition abs := (TransactionalDiskLang data_length).

Definition compile  T (p2: abs_op.(operation) T) : prog imp T.
  destruct p2.
  exact start.
  exact (read a).
  exact (write a v).
  exact commit.
  exact abort.
  exact recover.
Defined.

Definition token_refines_to  T u (d1: state imp) (p: Core.operation abs_op T) (get_reboot_state: imp.(state) -> imp.(state)) o1 o2 : Prop :=
     match p with
     | Start =>
       (exists d1' r,
          exec imp u o1 d1 start (Finished d1' r) /\
          o2 = Cont /\
          d1' = ([], snd d1)) \/
       
       (exists d1',
          exec imp u o1 d1 start (Crashed d1') /\
          o2 = CrashBefore /\
          d1' = d1)
         
     | Read a =>
       (exists d1' r,
          exec imp u o1 d1 (read a) (Finished d1' r) /\
          o2 = Cont /\
          d1' = d1) \/
       
       (exists d1',
          exec imp u o1 d1 (read a) (Crashed d1') /\
          o2 = CrashBefore /\
          d1' = d1)
         
     | Write a v =>
       (exists d1' r,
          exec imp u o1 d1 (write a v) (Finished d1' r) /\          
          ((o2 = Cont /\
            a < data_length /\
            d1' = ((a, v)::fst d1, snd d1)) \/

           (o2 = Cont /\
            a >= data_length /\
            d1' = d1) \/

           (o2 = TxnFull /\
            a < data_length /\
            length (fst d1) >= log_length /\
            d1' = d1)
          )
       ) \/
       
       (exists d1',
          exec imp u o1 d1 (write a v) (Crashed d1') /\
          o2 = CrashBefore /\
          d1' = d1)

     | Commit =>
       (exists d1' r,
          exec imp u o1 d1 commit (Finished d1' r) /\
          o2 = Cont /\
          d1' = ([], upd_batch (snd d1) (map fst (fst d1)) (map snd (fst d1)))) \/
       
       (exists d1',
          exec imp u o1 d1 commit (Crashed d1') /\
          ((o2 = CrashBefore /\
            d1' = d1) \/
           (o2 = CrashAfter /\
            d1' = ([], upd_batch (snd d1) (map fst (fst d1)) (map snd (fst d1))))))

     | Abort =>
       (exists d1' r,
          exec imp u o1 d1 abort (Finished d1' r) /\
          o2 = Cont /\
          d1' = ([], snd d1)) \/
       
       (exists d1',
          exec imp u o1 d1 abort (Crashed d1') /\
          o2 = CrashBefore /\
          d1' = d1)

      | Recover =>
       (exists d1' r,
          exec imp u o1 d1 recover (Finished d1' r) /\
          o2 = Cont /\
          d1' = d1) \/
       
       (exists d1',
          exec imp u o1 d1 recover (Crashed d1') /\
          o2 = CrashBefore /\
          d1' = d1)
     end.

   Definition refines_to (d1: state imp) (d2: state abs) :=     
     transaction_rep d1 d2.

   Lemma exec_compiled_preserves_refinement_finished_core:
    forall T (p2: abs_op.(Core.operation) T) o1 s1 s1' r u,
        (exists s2, refines_to s1 s2) ->
        imp.(exec) u o1 s1 (compile T p2) (Finished s1' r)->
        (exists s2', refines_to s1' s2').
  Proof. Admitted. (*
    intros; destruct p2; simpl in *; cleanup.
    {
      eapply read_finished in H0; eauto; cleanup; eauto.
    }
    {
      unfold refines_to in *; cleanup.
      eapply write_finished in H0; eauto.
      split_ors; cleanup; eauto.
    }
    {
      unfold refines_to, cached_log_rep in *; cleanup.
      eapply recover_finished in H0; eauto.
      unfold cached_log_reboot_rep;
      eexists; intuition eauto.      
      eapply log_rep_to_reboot_rep_same; eauto.
    }
  Qed.
   *)

   
  Definition TransactionalDiskCoreRefinement := Build_CoreRefinement compile refines_to token_refines_to exec_compiled_preserves_refinement_finished_core.
  Definition TransactionalDiskRefinement := LiftRefinement abs TransactionalDiskCoreRefinement.
  
  Notation "| p |" := (Op abs_op p)(at level 60).
  Notation "x <-| p1 ; p2" := (Bind (Op abs_op p1) (fun x => p2))(right associativity, at level 60).

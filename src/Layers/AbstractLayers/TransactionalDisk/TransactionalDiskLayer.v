Require Import Lia Framework TotalMem.
Import ListNotations.

Set Implicit Arguments.

Section TransactionalDisk.
  
  Variable disk_size: nat.

  Inductive token' :=
  | CrashBefore : token'
  | CrashAfter : token'
  | Cont : token'
  | TxnFull : token'.

  Definition state' := (txn_state * ((@total_mem addr addr_dec value) * (@total_mem addr addr_dec value)))%type.
  
  Inductive transactional_disk_prog : Type -> Type :=
  (* | Start : transactional_disk_prog unit *)
  | Read : addr -> transactional_disk_prog value
  | Write : addr -> value -> transactional_disk_prog (option unit)
  | Commit : transactional_disk_prog unit
  | Abort : transactional_disk_prog unit
  | Recover : transactional_disk_prog unit
  | Init : list (addr * value) -> transactional_disk_prog unit.

  Inductive exec' :
    forall T, user -> token' ->  state' -> transactional_disk_prog T -> @Result state' T -> Prop :=              
  | ExecReadInbound : 
      forall s a u,
        let st := fst s in
        let c := fst (snd s) in
        let d := snd (snd s) in
        a < disk_size ->
        exec' u Cont s (Read a) (Finished s (c a))

  | ExecReadOutbound : 
      forall s a u,
        a >= disk_size ->
        exec' u Cont s (Read a) (Finished s value0)
             
  | ExecWriteInbound :
      forall s a v u ,
        let st := fst s in
        let c := fst (snd s) in
        let d := snd (snd s) in
        a < disk_size ->
        exec' u Cont s (Write a v) (Finished (NotEmpty, ((upd c a v), d)) (Some tt))

  | ExecWriteInboundFull :
      forall s a v u,
        a < disk_size ->
        exec' u TxnFull s (Write a v) (Finished s None)
              
  | ExecWriteOutbound :
      forall s a v u,
        a >= disk_size ->
        exec' u Cont s (Write a v) (Finished s None)

  | ExecCommit : 
      forall s u,
        exec' u Cont s Commit (Finished (Empty, (fst (snd s), fst (snd s))) tt)

  | ExecAbort : 
      forall s u,
        exec' u Cont s Abort (Finished (Empty, (snd (snd s), snd (snd s))) tt)

  | ExecRecover : 
      forall s u,
        exec' u Cont s Recover (Finished (Empty, (snd (snd s), snd (snd s))) tt)

  | ExecInit : 
      forall s u l_av,
        let l_a := map fst l_av in
        let l_v := map snd l_av in
        exec' u Cont s (Init l_av) (Finished (Empty, (upd_batch (snd (snd s)) l_a l_v, upd_batch (snd (snd s)) l_a l_v)) tt)

  | ExecCrashBefore :
      forall d T (p: transactional_disk_prog T) u,
        exec' u CrashBefore d p (Crashed d)

  | ExecCommitCrashAfter :
      forall s u,
        let c := fst (snd s) in
        exec' u CrashAfter s Commit (Crashed (Empty, (c, c))).

  Hint Constructors exec' : core.

  Theorem exec_deterministic_wrt_token' :
    forall u o s T (p: transactional_disk_prog T) ret1 ret2,
      exec' u o s p ret1 ->
      exec' u o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto;
    repeat split_ors; cleanup; eauto; try lia; try congruence.
  Qed.
  
  Definition TDCore :=
    Build_Core
      transactional_disk_prog
      exec'
      exec_deterministic_wrt_token'.

  Definition TDLang := Build_Language TDCore.

End TransactionalDisk.

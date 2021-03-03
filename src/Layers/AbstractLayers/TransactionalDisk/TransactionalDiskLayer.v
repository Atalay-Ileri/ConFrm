Require Import Lia Framework TotalMem.
Import ListNotations.

Set Implicit Arguments.

Section TransactionalDisk.
  
  Variable disk_size: nat.

  Inductive token' :=
  | CrashBefore : token'
  | CrashAfter : token'
  | CrashDuringCommit : token'
  | Cont : token'
  | TxnFull : token'.

  Definition state' := ((@total_mem addr addr_dec value) * (@total_mem addr addr_dec value))%type.
  
  Inductive transactional_disk_prog : Type -> Type :=
  (* | Start : transactional_disk_prog unit *)
  | Read : addr -> transactional_disk_prog value
  | Write : addr -> value -> transactional_disk_prog unit
  | Commit : transactional_disk_prog unit
  | Abort : transactional_disk_prog unit
  | Recover : transactional_disk_prog unit
  | Init : list (addr * value) -> transactional_disk_prog unit.

  Inductive exec' :
    forall T, user -> token' ->  state' -> transactional_disk_prog T -> @Result state' T -> Prop :=
  (* | ExecStart : 
      forall s u,
        let c := fst s in
        let d := snd s in
        exec' u Cont s Start (Finished (empty_mem, d) tt) *)
              
  | ExecReadInbound : 
      forall s a u,
        let c := fst s in
        let d := snd s in
        a < disk_size ->
        exec' u Cont s (Read a) (Finished s (c a))

  | ExecReadOutbound : 
      forall s a u,
        a >= disk_size ->
        exec' u Cont s (Read a) (Finished s value0)
             
  | ExecWriteInbound :
      forall s a v u,
        let c := fst s in
        let d := snd s in
        a < disk_size ->
        exec' u Cont s (Write a v) (Finished ((upd c a v), d) tt)

  | ExecWriteInboundFull :
      forall s a v u,
        let c := fst s in
        let d := snd s in
        a < disk_size ->
        exec' u TxnFull s (Write a v) (Finished s tt)
              
  | ExecWriteOutbound :
      forall s a v u,
        a >= disk_size ->
        exec' u Cont s (Write a v) (Finished s tt)

  | ExecCommit : 
      forall s u,
        exec' u Cont s Commit (Finished (fst s, fst s) tt)

  | ExecAbort : 
      forall s u,
        exec' u Cont s Abort (Finished (snd s, snd s) tt)

  | ExecRecover : 
      forall s u,
        exec' u Cont s Recover (Finished (snd s, snd s) tt)

  | ExecInit : 
      forall s u l_av,
        let l_a := map fst l_av in
        let l_v := map snd l_av in
        exec' u Cont s (Init l_av) (Finished (upd_batch (snd s) l_a l_v, upd_batch (snd s) l_a l_v) tt)

  | ExecCrashBefore :
      forall d T (p: transactional_disk_prog T) u,
        exec' u CrashBefore d p (Crashed d)

  | ExecCommitCrashAfter :
      forall s u,
        let c := fst s in
        exec' u CrashAfter s Commit (Crashed (c, c)).

  (* 
     | ExecCrashDuringCommit :
      forall s c d u,
        (exists v, exec' u Cont s Commit (Finished (c, d) v)) ->
        exec' u CrashDuringCommit s Commit (Crashed (fst s, d)). *)

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
    repeat split_ors; cleanup; eauto; lia.
  Qed.
  
  Definition TransactionalDiskOperation :=
    Build_Core
      transactional_disk_prog
      exec'
      exec_deterministic_wrt_token'.

  Definition TransactionalDiskLang := Build_Language TransactionalDiskOperation.

End TransactionalDisk.

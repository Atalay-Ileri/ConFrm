Require Import Lia Framework.
Import ListNotations.
Import Mem.

Set Implicit Arguments.

Section FileDisk.

  Variable disk_size : nat.
  Notation "'Inum'" := addr.

  Inductive token' :=
  | CrashBefore : token'
  | CrashAfter : token'
  | CrashAfterCreate : Inum -> token'
  | NewInum : Inum -> token'
  | InodesFull : token'
  | TxnFull: token'
  | Cont : token'.

  Definition state' := (disk File)%type.
  
  Inductive file_disk_prog : Type -> Type :=
  | Read : Inum -> addr -> file_disk_prog (option value)
  | Write : Inum -> addr -> value -> file_disk_prog (option unit)
  | Extend : Inum -> value -> file_disk_prog (option unit)
  | ChangeOwner : Inum -> user -> file_disk_prog (option unit)
  | Create : user -> file_disk_prog (option addr)
  | Delete : Inum -> file_disk_prog (option unit)
  | Recover : file_disk_prog unit
  | Init : file_disk_prog unit.
  
  Inductive exec' :
    forall T, user -> token' ->  state' -> file_disk_prog T -> @Result state' T -> Prop :=
  | ExecReadSuccess : 
      forall d inum off file v u,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        nth_error file.(blocks) off = Some v ->
        exec' u Cont d (Read inum off) (Finished d (Some v))
              
  | ExecReadFail : 
      forall d u inum off file,
        (inum >= disk_size \/
         d inum = None \/
         (d inum = Some file /\
         (file.(owner) <> u \/ nth_error file.(blocks) off = None))) ->
        exec' u Cont d (Read inum off) (Finished d None)
              
  | ExecWriteSuccess :
      forall d u inum file off v,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        off < length (file.(blocks)) ->
        let new_file := Build_File file.(owner) (updn file.(blocks) off v) in
        exec' u Cont d (Write inum off v) (Finished (upd d inum new_file) (Some tt))

  (** Check log fitting condition **)
  | ExecWriteFail :
      forall d u inum file off v,
        (inum >= disk_size \/
         d inum = None \/
         d inum = Some file /\
         (file.(owner) <> u \/ off >= length (file.(blocks)))) ->
        exec' u Cont d (Write inum off v) (Finished d None)

  | ExecWriteFailTxnFull :
      forall d u inum file off v,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        off < length (file.(blocks)) ->
        exec' u TxnFull d (Write inum off v) (Finished d None)

  | ExecExtendSuccess :
      forall d u inum file v,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        let new_file := Build_File file.(owner) (file.(blocks) ++ [v]) in
        exec' u Cont d (Extend inum v) (Finished (upd d inum new_file) (Some tt))

  | ExecExtendFail :
      forall d u inum file v,
        (inum >= disk_size \/
         d inum = None \/
         (d inum = Some file /\ file.(owner) <> u)) ->
        exec' u Cont d (Extend inum v) (Finished d None)

  | ExecExtendFailTxnFull :
      forall d u inum file v,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        exec' u TxnFull d (Extend inum v) (Finished d None)

  | ExecChangeOwnerSuccess :
      forall d u inum file o,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        let new_file := Build_File o file.(blocks) in
        exec' u Cont d (ChangeOwner inum o) (Finished (upd d inum new_file) (Some tt))

  | ExecChangeOwnerFail :
      forall d u inum file o,
        (inum >= disk_size \/
         d inum = None \/
         (d inum = Some file /\ file.(owner) <> u)) ->
        exec' u Cont d (ChangeOwner inum o) (Finished d None)

  | ExecChangeOwnerFailTxnFull :
      forall d u inum file o,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        exec' u TxnFull d (ChangeOwner inum o) (Finished d None)

  | ExecCreateSuccess :
      forall d u inum owner,
        inum < disk_size ->
        d inum = None ->
        let new_file := Build_File owner [] in
        exec' u (NewInum inum) d (Create owner) (Finished (upd d inum new_file) (Some inum))

  | ExecCreateFail :
      forall d u owner,
        (forall inum, inum < disk_size -> d inum <> None) ->
        exec' u InodesFull d (Create owner) (Finished d None)

  | ExecCreateFailTxnFull :
      forall d u owner,
        exec' u TxnFull d (Create owner) (Finished d None)
              
  | ExecDeleteSuccess :
      forall d u inum file,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        exec' u Cont d (Delete inum) (Finished (Mem.delete d inum) (Some tt))

  | ExecDeleteFail :
      forall d u file inum,
        (inum >= disk_size \/
         d inum = None \/
         (d inum = Some file /\ file.(owner) <> u)) ->
        exec' u Cont d (Delete inum) (Finished d None)
              
  | ExecDeleteFailTxnFull :
      forall d u inum file,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        exec' u TxnFull d (Delete inum) (Finished d None)

  | ExecRecover : 
      forall d u,
        exec' u Cont d Recover (Finished d tt)
  
  | ExecInit : 
        forall d u,
          exec' u Cont d Init (Finished empty_mem tt)

  | ExecCrashBefore :
      forall u d T (p: file_disk_prog T),
        exec' u CrashBefore d p (Crashed d)

  | ExecChangeOwnerCrashAfter :
      forall d u inum file o,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        let new_file := Build_File o file.(blocks) in
        exec' u CrashAfter d (ChangeOwner inum o) (Crashed (upd d inum new_file))

  | ExecWriteCrashAfter :
      forall d u inum file off v,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        off < length (file.(blocks)) ->
        let new_file := Build_File file.(owner) (updn file.(blocks) off v) in
        exec' u CrashAfter d (Write inum off v) (Crashed (upd d inum new_file))

  | ExecExtendCrashAfter :
      forall d u inum file v,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        let new_file := Build_File file.(owner) (file.(blocks) ++ [v]) in
        exec' u CrashAfter d (Extend inum v) (Crashed (upd d inum new_file))

  | ExecDeleteCrashAfter :
      forall d u inum file,
        inum < disk_size ->
        d inum = Some file ->
        file.(owner) = u ->
        exec' u CrashAfter d (Delete inum) (Crashed (Mem.delete d inum))

  | ExecCreateCrashAfter :
      forall d u inum owner,
        inum < disk_size ->
        d inum = None ->
        let new_file := Build_File owner [] in
        exec' u (CrashAfterCreate inum) d (Create owner) (Crashed (upd d inum new_file)).

  Hint Constructors exec' : core.


  Theorem exec_deterministic_wrt_token' :
    forall u o s T (p: file_disk_prog T) ret1 ret2,
      exec' u o s p ret1 ->
      exec' u o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ _ |- _] =>
        inversion H; clear H; try split_ors; cleanup
      end;
    try solve [ repeat (cleanup; intuition eauto; try congruence; try lia) ].
  Qed.
  
  Definition FDOperation :=
    Build_Core
      file_disk_prog
      exec'
      exec_deterministic_wrt_token'.

  Definition FDLang := Build_Layer FDOperation.

End FileDisk.

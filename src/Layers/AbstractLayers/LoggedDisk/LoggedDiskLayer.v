Require Import Framework TotalMem.
Import ListNotations.

Set Implicit Arguments.

Section LoggedDisk.
Variable disk_size: addr.

  Inductive token' :=
  | CrashBefore : token'
  | CrashAfter : token'
  | Cont : token'.

  Definition state' := @total_mem addr addr_dec value.
  
  Inductive logged_disk_prog : Type -> Type :=
  | Read : addr -> logged_disk_prog value
  | Write : list addr -> list value -> logged_disk_prog unit
  | Recover : logged_disk_prog unit.
   
  Inductive exec' :
    forall T, token' ->  state' -> logged_disk_prog T -> @Result state' T -> Prop :=
  | ExecReadSuccess : 
      forall d a,
        a  < disk_size ->
        exec' Cont d (Read a) (Finished d (d a))

  | ExecReadFail : 
      forall d a,
        a  >= disk_size ->
        exec' Cont d (Read a) (Finished d value0)
             
  | ExecWriteSuccess :
      forall d la lv,
        NoDup la ->
        length la = length lv ->
        Forall (fun a => a < disk_size) la ->
        exec' Cont d (Write la lv) (Finished (upd_batch d la lv) tt)

  | ExecWriteFail :
      forall d la lv,
        ~NoDup la \/ length la <> length lv \/
        ~Forall (fun a => a < disk_size) la ->
        exec' Cont d (Write la lv) (Finished d tt)

  | ExecRecover : 
      forall d,
        exec' Cont d Recover (Finished d tt)

  | ExecCrashBefore :
      forall d T (p: logged_disk_prog T),
        exec' CrashBefore d p (Crashed d)

  | ExecCrashWriteAfter :
      forall d la lv,
        NoDup la ->
        length la = length lv ->
        Forall (fun a => a < disk_size) la ->
        exec' CrashAfter d (Write la lv) (Crashed (upd_batch d la lv)).

  Hint Constructors exec' : core.

  Theorem exec_deterministic_wrt_token' :
    forall o s T (p: logged_disk_prog T) ret1 ret2,
      exec' o s p ret1 ->
      exec' o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto;
    try split_ors; intuition;
    cleanup; exfalso; eauto.
  Qed.
  
  Definition LoggedDiskOperation :=
    Build_Core
      logged_disk_prog
      exec'
      exec_deterministic_wrt_token'.

  Definition LoggedDiskLang := Build_Language LoggedDiskOperation.
End LoggedDisk.

Notation "| p |" := (Op LoggedDiskOperation p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op LoggedDiskOperation p1) (fun x => p2))(right associativity, at level 60). 
Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).

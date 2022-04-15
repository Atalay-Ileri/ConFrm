Require Import Framework TotalMem.
Import ListNotations.

Set Implicit Arguments.

Section LoggedDisk.
  Variable log_size: nat.
  Variable disk_size: nat.

  Inductive token' :=
  | CrashBefore : token'
  | CrashAfter : token'
  | Cont : token'.

  Definition state' := @total_mem addr addr_dec value.
  
  Inductive logged_disk_prog : Type -> Type :=
  | Read : addr -> logged_disk_prog value
  | Write : list addr -> list value -> logged_disk_prog unit
  | Recover : logged_disk_prog unit
  | Init : list (addr * value) -> logged_disk_prog unit.
   
  Inductive exec' :
    forall T, user -> token' ->  state' -> logged_disk_prog T -> @Result state' T -> Prop :=
  | ExecReadSuccess : 
      forall d a u,
        a < disk_size ->
        exec' u Cont d (Read a) (Finished d (d a))

  | ExecReadFail : 
      forall d a u,
        a  >= disk_size ->
        exec' u Cont d (Read a) (Finished d value0)
             
  | ExecWriteSuccess :
      forall d la lv u,
        NoDup la ->
        length la = length lv ->
        Forall (fun a => a < disk_size) la ->
        length (addr_list_to_blocks la) + length lv <= log_size ->
        exec' u Cont d (Write la lv) (Finished (upd_batch d la lv) tt)

  | ExecWriteFail :
      forall d la lv u,
        ~NoDup la \/ length la <> length lv \/
        ~Forall (fun a => a < disk_size) la \/
        length (addr_list_to_blocks la) + length lv > log_size ->
        exec' u Cont d (Write la lv) (Finished d tt)

  | ExecRecover : 
      forall d u,
        exec' u Cont d Recover (Finished d tt)

  | ExecInit : 
      forall d u l_av,
        let l_a := map fst l_av in
        let l_v := map snd l_av in
        exec' u Cont d (Init l_av) (Finished (upd_batch d l_a l_v) tt)

  | ExecCrashBefore :
      forall d T (p: logged_disk_prog T) u,
        exec' u CrashBefore d p (Crashed d)

  | ExecCrashWriteAfter :
      forall d la lv u,
        NoDup la ->
        length la = length lv ->
        Forall (fun a => a < disk_size) la ->
        length (addr_list_to_blocks la) + length lv <= log_size ->
        exec' u CrashAfter d (Write la lv) (Crashed (upd_batch d la lv)).

  Hint Constructors exec' : core.

  Theorem exec_deterministic_wrt_token' :
    forall u o s T (p: logged_disk_prog T) ret1 ret2,
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
    try split_ors; intuition;
    cleanup; exfalso; eauto.
  Qed.
  
  Definition LoggedDiskOperation :=
    Build_Core
      logged_disk_prog
      exec'
      exec_deterministic_wrt_token'.

  Definition LoggedDiskLang := Build_Layer LoggedDiskOperation.
End LoggedDisk.


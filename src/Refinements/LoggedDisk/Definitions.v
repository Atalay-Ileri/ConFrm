Require Import Framework CachedDiskLayer LoggedDiskLayer LogCache.Definitions.
Close Scope pred_scope.
Import ListNotations.

Fixpoint compile {T} (p2: LoggedDiskHL.Lang.prog T) : CachedDiskHL.Lang.prog T.
  destruct p2; simpl in *.
  {
    destruct p.
    exact (read a).
    exact (write l l0).
  }
  {
    exact (CachedDiskHL.Lang.Ret t).
  }
  {
    exact (CachedDiskHL.Lang.Bind (compile T p2) (fun x => compile T' (p x))).
  }
Defined.


Fixpoint oracle_refines_to T (d1: State cached_disk_lts) (p: Prog logged_disk_lts T)  (o1: Oracle cached_disk_lts) (o2: Oracle logged_disk_lts) : Prop :=
  CachedDiskHL.Lang.oracle_ok (compile p) o1 d1 /\
    match p with
    | @Bind T1 T2 p1 p2 =>
      exists o1' o1'',
      o1 = o1'++o1'' /\
     ((exists d1', CachedDiskHL.Lang.exec o1 d1 (compile p1) (Crashed d1') /\
         oracle_refines_to T1 d1 p1 o1 o2) \/
      (exists d1' r ret,
         CachedDiskHL.Lang.exec o1' d1 (compile p1) (Finished d1' r) /\
         CachedDiskHL.Lang.exec o1'' d1' (compile (p2 r)) ret /\
         exists o2' o2'',
         oracle_refines_to T1 d1 p1 o1' o2' /\
         oracle_refines_to T2 d1' (p2 r) o1'' o2'' /\
         o2 = o2' ++ o2''))
    |Op op =>
     match op with
     | Read a =>
       (exists d1',
          CachedDiskHL.Lang.exec o1 d1 (read a) (Crashed d1') /\
          o2 = [OpOracle [CrashBefore] ]) \/
       (exists d1' r,
          CachedDiskHL.Lang.exec o1 d1 (read a) (Finished d1' r) /\
          o2 = [Cont])
         
     | Write la lv =>
       (exists d1',
          CachedDiskHL.Lang.exec o1 d1 (write la lv) (Crashed d1') /\
          ((d1' = d1 /\ o2 = [ OpOracle [CrashBefore] ]) \/
           (d1' <> d1 /\ o2 = [ OpOracle [CrashAfter] ]))) \/
       (exists d1' r,
          CachedDiskHL.Lang.exec o1 d1 (write la lv) (Finished d1' r) /\          
          o2 = [Cont])
     end

    | Ret v =>
      (exists d1',
         CachedDiskHL.Lang.exec o1 d1 (CachedDiskHL.Lang.Ret v) (Crashed d1') /\
         o2 = [Crash]) \/
      (exists d1' r,
         CachedDiskHL.Lang.exec o1 d1 (CachedDiskHL.Lang.Ret v) (Finished d1' r) /\
         o2 = [Cont])
    end
.
(*
    | Read _ =>
      if (in_dec Layer1.token_dec Layer1.Crash o1) then
        o2 = [Crash1]
      else
        o2 = [Cont]
    | Ret _ =>
      if (in_dec Layer1.token_dec Layer1.Crash o1) then
        o2 = [Crash1]
      else
        o2 = [Cont]
    | Write a _ =>
      if (in_dec Layer1.token_dec Layer1.Crash o1) then
         forall d1',
          Layer1.exec o1 d1 (compile p) (Crashed d1') ->
          let sv := d1 a in
          let sv' := d1' a in
          match sv, sv' with
          | Some v, Some v' =>
            (v = v' ->
             o2 = [Crash1]) /\
            (v <> v' ->
             o2 = [Crash2])
          | _, _ => False
          end
      else
        o2 = [Cont]
    end.
*)
  Definition refines_to (d1: State cached_disk_lts) (d2: State logged_disk_lts) :=
    exists F, cached_log_rep F d2 d1.

  Definition compilation_of T (p1: Prog cached_disk_lts T) (p2: Prog logged_disk_lts T) :=
    p1 = @compile T p2.

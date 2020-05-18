Require Import Framework CachedDiskLayer LoggedDiskLayer LogCache.Definitions.
Close Scope pred_scope.
Import ListNotations.

Notation "'low'" := CachedDiskLang.
Notation "'high'" := LoggedDiskLang.

Fixpoint compile {T} (p2: prog high T) : prog low T.
  destruct p2; simpl in *.
  {
    destruct p.
    exact (read a).
    exact (write l l0).
  }
  {
    exact (Ret t).
  }
  {
    exact (Bind (compile T p2) (fun x => compile T' (p x))).
  }
Defined.

Fixpoint oracle_refines_to T (d1: state low) (p: prog high T) o1 o2 : Prop :=
    match p with
    | @Bind _ T1 T2 p1 p2 =>
      exists o1' o1'' o2' o2'',
      o1 = o1'++o1'' /\
      o2 = o2' ++ o2'' /\
     ((exists d1', exec low o1' d1 (compile p1) (Crashed d1') /\
         oracle_refines_to T1 d1 p1 o1' o2') \/
      (exists d1' r ret,
         exec low o1' d1 (compile p1) (Finished d1' r) /\
         exec low o1'' d1' (compile (p2 r)) ret /\
         oracle_refines_to T1 d1 p1 o1' o2' /\
         oracle_refines_to T2 d1' (p2 r) o1'' o2''
         ))
    |Op _ op =>
     match op with
     | Read a =>
       (exists d1',
          exec low o1 d1 (read a) (Crashed d1') /\
          o2 = [OpOracle LoggedDiskOperation [CrashBefore] ]) \/
       (exists d1' r,
          exec low o1 d1 (read a) (Finished d1' r) /\
          o2 = [OpOracle LoggedDiskOperation [LoggedDisk.Definitions.Cont] ])
         
     | Write la lv =>
       (exists d1',
          exec low o1 d1 (write la lv) (Crashed d1') /\
          ((d1' = d1 /\
           o2 = [ OpOracle LoggedDiskOperation [CrashBefore] ]) \/
           (d1' <> d1 /\
            o2 = [ OpOracle LoggedDiskOperation [CrashAfter] ]))) \/
       (exists d1' r,
          exec low o1 d1 (write la lv) (Finished d1' r) /\          
          o2 = [OpOracle LoggedDiskOperation [LoggedDisk.Definitions.Cont] ] /\
       (forall s ,(exists F, cached_log_rep F s d1) -> (exists F, cached_log_rep F (write_all s la lv) d1')))
     end

    | Ret v =>
      (exists d1',
         exec low o1 d1 (Ret v) (Crashed d1') /\
         o2 = [Language.Crash _]) \/
      (exists d1' r,
         exec low o1 d1 (Ret v) (Finished d1' r) /\
         o2 = [Language.Cont _])
    end
.

  Definition refines_to (d1: state low) (d2: state high) :=
    exists F, cached_log_rep F d2 d1.

  Definition compilation_of T (p1: prog low T) (p2: prog high T) :=
    p1 = @compile T p2.

  Definition LoggedDiskRefinement := Build_Refinement compilation_of refines_to oracle_refines_to.

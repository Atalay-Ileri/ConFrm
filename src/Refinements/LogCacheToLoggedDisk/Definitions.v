Require Import Framework CachedDiskLayer LoggedDiskLayer LogCache.
Close Scope pred_scope.
Import ListNotations.

Local Definition low_op := CachedDiskOperation.
Local Definition high_op := LoggedDiskOperation.
Local Definition low := CachedDiskLang.
Local Definition high := LoggedDiskLang.

Definition compile_op T (p2: Operation.prog high_op T) : prog low T.
 destruct p2.
 exact (read a).
 exact (write l l0).
Defined.

Definition oracle_refines_to_op T (d1: state low) (p: Operation.prog high_op T) o1 o2 : Prop :=
   match p with
     | Read a =>
       (exists d1',
          exec low o1 d1 (read a) (Crashed d1') /\
          o2 = [CrashBefore]) \/
       (exists d1' r,
          exec low o1 d1 (read a) (Finished d1' r) /\
          o2 = [Cont])
         
     | Write la lv =>
       (exists d1',
          exec low o1 d1 (write la lv) (Crashed d1') /\
          ((d1' = d1 /\
           o2 = [CrashBefore]) \/
           (d1' <> d1 /\
            o2 = [CrashAfter]))) \/
       (exists d1' r,
          exec low o1 d1 (write la lv) (Finished d1' r) /\          
          o2 = [Cont] /\
       (forall s ,(exists F, cached_log_rep F s d1) -> (exists F, cached_log_rep F (write_all s la lv) d1')))
   end.

  Definition refines_to (d1: state low) (d2: state high) :=
    exists F, cached_log_rep F d2 d1.

  Definition LoggedDiskOperationRefinement := Build_OperationRefinement compile_op refines_to oracle_refines_to_op.
  Definition LoggedDiskRefinement := LiftRefinement LoggedDiskLang LoggedDiskOperationRefinement.

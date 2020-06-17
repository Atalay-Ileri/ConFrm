Require Import Framework CachedDiskLayer LoggedDiskLayer Log LogCache.
Close Scope pred_scope.
Import ListNotations.

Local Definition low_op := CachedDiskOperation.
Local Definition high_op := LoggedDiskOperation.
Local Definition low := CachedDiskLang.
Local Definition high := LoggedDiskLang.

Definition compile T (p2: Operation.prog high_op T) : prog low T.
 destruct p2.
 exact (read a).
 exact (write l l0).
Defined.

Definition oracle_refines_to T (d1: state low) (p: Operation.prog high_op T) o1 o2 : Prop :=
   match p with
   | Read a =>
     (exists d1' r,
        exec low o1 d1 (read a) (Finished d1' r) /\
        o2 = [Cont] /\
        d1' = d1) \/
     (exists d1',
        exec low o1 d1 (read a) (Crashed d1') /\
        o2 = [CrashBefore] /\
        d1 = d1')
         
   | Write la lv =>
     (exists d1' r,
          exec low o1 d1 (write la lv) (Finished d1' r) /\          
          o2 = [Cont] /\
          (forall s,
             (exists F log_state, cached_log_rep F s d1 log_state) ->
             (exists F log_state, cached_log_rep F (write_all s la lv) d1' log_state))
       ) \/
     (exists d1',
        (exec low o1 d1 (write la lv) (Crashed d1') /\
         o2 = [CrashBefore] /\
         d1' = d1) \/
        (exec low o1 d1 (write la lv) (Crashed d1') /\
         o2 = [CrashAfter] /\
         d1' <> d1)
     )  
   end.

  Definition refines_to (d1: state low) (d2: state high) :=
    exists F d2' log_state,
      cached_log_rep F d2' d1 log_state /\
      d2 = mem_map fst d2'.

  Definition LoggedDiskOperationRefinement := Build_OperationRefinement compile refines_to oracle_refines_to.
  Definition LoggedDiskRefinement := LiftRefinement LoggedDiskLang LoggedDiskOperationRefinement.

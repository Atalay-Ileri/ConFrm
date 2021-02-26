Require Import Framework FSParameters.
Require Import AuthenticatedDiskLayer FileDiskLayer File.
Close Scope predicate_scope.
Import ListNotations.

Local Definition low_op := (AuthenticatedDiskOperation).
Local Definition high_op := (FileDiskOperation inode_count).
Local Definition low := (AuthenticatedDiskLang).
Local Definition high := (FileDiskLang inode_count).


Fixpoint compile T (p2: Core.operation high_op T) : prog low T.
  destruct p2.
  exact (read a a0).
  exact (write a a0 v).
  exact (extend a v).
  exact (change_owner a u).
  exact (create u).
  exact (delete a).
  exact recover.
Defined.

Definition token_refines_to T u (d1: state low) (p: Core.operation high_op T) (get_reboot_state: state low -> state low) o1 o2 : Prop :=
    match p with
    | Read inum a =>
      forall fd,
      files_rep fd d1 ->
      (
        (exists d' r,
           exec low u o1 d1 (read inum a) (Finished d' r) /\
           o2 = Cont /\
           files_rep fd d') \/
        
        (exists d',
           exec low u o1 d1 (read inum a) (Crashed d') /\
           o2 = CrashBefore /\
           files_crash_rep fd d')
      )
        
    | Write inum off v =>
      forall fd,
        files_rep fd d1 ->
      (
        (exists d' r file,
           (
             exec low u o1 d1 (write inum off v) (Finished d' r) /\
             o2 = Cont /\
             inum < inode_count /\
             fd inum = Some file /\
             file.(owner) = u /\
             let new_file := update_file file off v in
             files_rep (Mem.upd fd inum new_file) d'
           ) \/
           (
             exec low u o1 d1 (write inum off v) (Finished d' r) /\
             o2 = Cont /\
             (inum >= inode_count \/
               fd inum = None \/
               (fd inum = Some file /\ file.(owner) <> u)) /\
             files_rep fd d'
           ) 
        ) \/
        
        (exists d',
           (
             exec low u o1 d1 (write inum off v) (Crashed d') /\
             o2 = CrashBefore /\
             files_crash_rep fd d'
           ) \/
           (exists file,
              exec low u o1 d1 (write inum off v) (Crashed d') /\
              o2 = CrashAfter /\ 
              inum < inode_count /\
              fd inum = Some file /\
              file.(owner) = u /\
              off < length file.(blocks) /\
              let new_file := update_file file off v in
              files_crash_rep (Mem.upd fd inum new_file) d'     
           )
        )
      )

     | Extend inum v =>
       forall fd,
      files_rep fd d1 ->
      (
       (exists d' r file,
          (
            exec low u o1 d1 (extend inum v) (Finished d' r) /\
            o2 = Cont /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            let new_file := extend_file file v in
            files_rep (Mem.upd fd inum new_file) d'
          ) \/
          (
            exec low u o1 d1 (extend inum v) (Finished d' r) /\
            o2 = Cont /\
            (inum >= inode_count \/
             fd inum = None \/
             (fd inum = Some file /\ file.(owner) <> u)) /\
            files_rep fd d'
          ) \/
          (
            exec low u o1 d1 (extend inum v) (Finished d' r) /\
            o2 = DiskFull /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            files_rep fd d'
          )
       ) \/
  
       (exists d',
          (
            exec low u o1 d1 (extend inum v) (Crashed d') /\
            o2 = CrashBefore /\
            files_crash_rep fd d'
          ) \/
          (exists file,
            exec low u o1 d1 (extend inum v) (Crashed d') /\
            o2 = CrashAfter /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            let new_file := extend_file file v in
            files_crash_rep (Mem.upd fd inum new_file) d'
          )
       )
      )
         
     | ChangeOwner inum own =>
       forall fd,
      files_rep fd d1 ->
      (
       (exists d' r file,
          (
            exec low u o1 d1 (change_owner inum own) (Finished d' r) /\
            o2 = Cont /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            let new_file := change_file_owner file own in
            files_rep (Mem.upd fd inum new_file) d'
          ) \/
          (
            exec low u o1 d1 (change_owner inum own) (Finished d' r) /\
            o2 = Cont /\
            (
              inum >= inode_count \/
              fd inum = None \/
              (fd inum = Some file /\ file.(owner) <> u)
            ) /\
            files_rep fd d'
          )
       ) \/
       (exists d',
          (
            exec low u o1 d1 (change_owner inum own) (Crashed d') /\
            o2 = CrashBefore /\
            files_crash_rep fd d'
          ) \/
          (exists file,
            exec low u o1 d1 (change_owner inum own) (Crashed d') /\
            o2 = CrashAfter /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            let new_file := change_file_owner file own in
            files_crash_rep (Mem.upd fd inum new_file) d'
          )
       )
      )
     | Create own =>
       forall fd,
      files_rep fd d1 ->
      (
       (exists d',
          (exists inum,
            exec low u o1 d1 (create own) (Finished d' (Some inum)) /\
            o2 = NewInum inum /\
            inum < inode_count /\
            fd inum = None /\
            let new_file := new_file own in
            files_rep (Mem.upd fd inum new_file) d'
          ) \/
          (
            exec low u o1 d1 (create own) (Finished d' None) /\
            o2 = InodesFull /\
            (forall inum, inum < inode_count -> fd inum <> None) /\
            files_rep fd d'
          )
       ) \/
       (exists d',
          (
            exec low u o1 d1 (create own) (Crashed d') /\
            o2 = CrashBefore /\
            files_crash_rep fd d'
          ) \/
          (exists inum,
            exec low u o1 d1 (create own) (Crashed d') /\
            o2 = CrashAfterCreate inum /\
            inum < inode_count /\
            fd inum = None /\
            let new_file := new_file own in
            files_crash_rep (Mem.upd fd inum new_file) d'
          )
       )
      )
     | Delete inum =>
       forall fd,
      files_rep fd d1 ->
      (
       (exists d' r file,
          (
            exec low u o1 d1 (delete inum) (Finished d' r) /\
            o2 = Cont /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            files_rep (Mem.delete fd inum) d'
          ) \/
          (
            exec low u o1 d1 (delete inum) (Finished d' r) /\
            o2 = Cont /\
            (
              inum >= inode_count \/
              fd inum = None \/
              (fd inum = Some file /\ file.(owner) <> u)
            ) /\
            files_rep fd d'
          )
       ) \/
       (exists d',
          (
            exec low u o1 d1 (delete inum) (Crashed d') /\
            o2 = CrashBefore /\
            files_crash_rep fd d'
          ) \/
          (exists file,
            exec low u o1 d1 (delete inum) (Crashed d') /\
            o2 = CrashAfter /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            files_crash_rep (Mem.delete fd inum) d'
          )
       )
      )
     | Recover =>
       forall fd,
         files_reboot_rep fd d1 ->
       (
         (exists d',
            exec low u o1 d1 recover (Finished d' tt) /\
            o2 = Cont /\
            files_rep fd d') \/
         
         (exists d',
            exec low u o1 d1 recover (Crashed d') /\
            o2 = CrashBefore /\
            files_crash_rep fd d')
       )
    end.

   Definition refines_to (d1: state low) (d2: state high) :=
     files_rep d2 d1.

   Definition refines_to_reboot (d1: state low) (d2: state high) :=
     files_reboot_rep d2 d1.

   Lemma exec_compiled_preserves_refinement_finished_core:
    forall T (p2: high_op.(Core.operation) T) o1 s1 s1' r u,
        (exists s2, refines_to s1 s2) ->
        low.(exec) u o1 s1 (compile T p2) (Finished s1' r)->
        (exists s2', refines_to s1' s2').
  Proof.
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
      unfold refines_to in *; cleanup.
      eapply extend_finished in H0; cleanup; eauto.
      split_ors; cleanup; eauto.
    }
    {
      unfold refines_to in *; cleanup.
      eapply change_owner_finished in H0; cleanup; eauto.
      split_ors; cleanup; eauto.
    }
    {
      unfold refines_to in *; cleanup.
      eapply create_finished in H0; cleanup; eauto.
      split_ors; cleanup; eauto.
    }
    {
      unfold refines_to in *; cleanup.
      eapply delete_finished in H0; cleanup; eauto.
      split_ors; cleanup; eauto.
    }
    {
      unfold refines_to in *; cleanup.
      eapply recover_finished in H0; eauto.
      unfold files_rep, files_reboot_rep, files_crash_rep in *;
      cleanup; eauto.
    }
  Qed.

  Definition FileDiskOperationRefinement := Build_CoreRefinement compile refines_to token_refines_to exec_compiled_preserves_refinement_finished_core.
  Definition FileDiskRefinement := LiftRefinement high FileDiskOperationRefinement.

  Notation "| p |" := (Op high_op p)(at level 60).

Require Import Framework FSParameters.
Require Import AuthenticatedDiskLayer FileDiskLayer.
Require Import File FileSpecs.
Import ListNotations.

Local Definition impl_core := (ADOperation).
Local Definition abs_core := (FDOperation inode_count).
Local Definition impl := (ADLang).
Local Definition abs := (FDLang inode_count).


Fixpoint compile T (p2: Core.operation abs_core T) : prog impl T.
  destruct p2.
  exact (read a a0).
  exact (write a a0 v).
  exact (extend a v).
  exact (change_owner a u).
  exact (create u).
  exact (delete a).
  exact recover.
Defined.

Definition token_refines T u (d1: state impl) (p: Core.operation abs_core T) (get_reboot_state: state impl -> state impl) o1 o2 : Prop :=
    match p with
    | Read inum a =>
      forall fd,
      files_rep fd d1 ->
      (
        (exists d' r,
           exec impl u o1 d1 (read inum a) (Finished d' r) /\
           o2 = Cont /\
           files_rep fd d') \/
        
        (exists d',
           exec impl u o1 d1 (read inum a) (Crashed d') /\
           o2 = CrashBefore /\
           files_crash_rep fd d')
      )
        
    | Write inum off v =>
      forall fd,
        files_rep fd d1 ->
      (
        (exists d' r file,
           (
             exec impl u o1 d1 (write inum off v) (Finished d' r) /\
             o2 = Cont /\
             r = Some tt /\
             inum < inode_count /\
             fd inum = Some file /\
             file.(owner) = u /\
             let new_file := update_file file off v in
             files_rep (Mem.upd fd inum new_file) d'
           ) \/
           (
             exec impl u o1 d1 (write inum off v) (Finished d' r) /\
             o2 = Cont /\
             r = None /\
             (inum >= inode_count \/
              fd inum = None \/
              (fd inum = Some file /\
               (file.(owner) <> u \/ off >= length file.(blocks)))) /\
             files_rep fd d'
           ) \/
             (
             exec impl u o1 d1 (write inum off v) (Finished d' r) /\
             o2 = TxnFull /\
             r = None /\
             inum < inode_count /\
             fd inum = Some file /\
             file.(owner) = u /\
             off < length file.(blocks) /\
             files_rep fd d'
           )
        ) \/
        
        (exists d',
           (
             exec impl u o1 d1 (write inum off v) (Crashed d') /\
             o2 = CrashBefore /\
             files_crash_rep fd d'
           ) \/
           (exists file,
              exec impl u o1 d1 (write inum off v) (Crashed d') /\
              o2 = CrashAfter /\ 
              inum < inode_count /\
              fd inum = Some file /\
              file.(owner) = u /\
              off < length file.(blocks) /\
              seln file.(blocks) off value0 <> v /\
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
            exec impl u o1 d1 (extend inum v) (Finished d' r) /\
            o2 = Cont /\
            r = Some tt /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            let new_file := extend_file file v in
            files_rep (Mem.upd fd inum new_file) d'
          ) \/
          (
            exec impl u o1 d1 (extend inum v) (Finished d' r) /\
            o2 = Cont /\
            r = None /\
            (inum >= inode_count \/
             fd inum = None \/
             (fd inum = Some file /\ file.(owner) <> u)) /\
            files_rep fd d'
          ) \/
          (
            exec impl u o1 d1 (extend inum v) (Finished d' r) /\
            o2 = TxnFull /\
            r = None /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            files_rep fd d'
          )
       ) \/
  
       (exists d',
          (
            exec impl u o1 d1 (extend inum v) (Crashed d') /\
            o2 = CrashBefore /\
            files_crash_rep fd d'
          ) \/
          (exists file,
            exec impl u o1 d1 (extend inum v) (Crashed d') /\
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
            exec impl u o1 d1 (change_owner inum own) (Finished d' r) /\
            r = Some tt /\
            o2 = Cont /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            let new_file := change_file_owner file own in
            files_rep (Mem.upd fd inum new_file) d'
          ) \/
          (
            exec impl u o1 d1 (change_owner inum own) (Finished d' r) /\
            r = None /\
            o2 = Cont /\
            (
              inum >= inode_count \/
              fd inum = None \/
              (fd inum = Some file /\ file.(owner) <> u)
            ) /\
            files_rep fd d'
          ) \/
          (
            exec impl u o1 d1 (change_owner inum own) (Finished d' r) /\
            r = None /\
            o2 = TxnFull /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            files_rep fd d'
          )
       ) \/
       (exists d',
          (
            exec impl u o1 d1 (change_owner inum own) (Crashed d') /\
            o2 = CrashBefore /\
            files_crash_rep fd d'
          ) \/
          (exists file,
            exec impl u o1 d1 (change_owner inum own) (Crashed d') /\
            o2 = CrashAfter /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            own <> u /\
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
            exec impl u o1 d1 (create own) (Finished d' (Some inum)) /\
            o2 = NewInum inum /\
            inum < inode_count /\
            fd inum = None /\
            (forall i, i < inum -> fd i <> None ) /\ 
            let new_file := new_file own in
            files_rep (Mem.upd fd inum new_file) d'
          ) \/
          (
            exec impl u o1 d1 (create own) (Finished d' None) /\
            o2 = InodesFull /\
            (forall inum, inum < inode_count -> fd inum <> None) /\
            files_rep fd d'
          ) \/
          (exists inum,
            exec impl u o1 d1 (create own) (Finished d' None) /\
            o2 = TxnFull /\
            inum < inode_count /\
            fd inum = None /\
            files_rep fd d'
          )
       ) \/
       (exists d',
          (
            exec impl u o1 d1 (create own) (Crashed d') /\
            o2 = CrashBefore /\
            files_crash_rep fd d'
          ) \/
          (exists inum,
            exec impl u o1 d1 (create own) (Crashed d') /\
            o2 = CrashAfterCreate inum /\
            inum < inode_count /\
            fd inum = None /\
            (forall i, i < inum -> fd i <> None ) /\ 
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
            exec impl u o1 d1 (delete inum) (Finished d' r) /\
            o2 = Cont /\
            r = Some tt /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            files_rep (Mem.delete fd inum) d'
          ) \/
          (
            exec impl u o1 d1 (delete inum) (Finished d' r) /\
            o2 = Cont /\
            r = None /\
            (
              inum >= inode_count \/
              fd inum = None \/
              (fd inum = Some file /\ file.(owner) <> u)
            ) /\
            files_rep fd d'
          ) \/
          (
            exec impl u o1 d1 (delete inum) (Finished d' r) /\
            o2 = TxnFull /\
            r = None /\
            inum < inode_count /\
            fd inum = Some file /\
            file.(owner) = u /\
            files_rep fd d'
          )
       ) \/
       (exists d',
          (
            exec impl u o1 d1 (delete inum) (Crashed d') /\
            o2 = CrashBefore /\
            files_crash_rep fd d'
          ) \/
          (exists file,
            exec impl u o1 d1 (delete inum) (Crashed d') /\
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
            exec impl u o1 d1 recover (Finished d' tt) /\
            o2 = Cont /\
            files_rep fd d') \/
         
         (exists d',
            exec impl u o1 d1 recover (Crashed d') /\
            o2 = CrashBefore /\
            files_crash_rep fd d')
       )
    end.

   Definition refines (d1: state impl) (d2: state abs) :=
     files_rep d2 d1.

   Definition refines_reboot (d1: state impl) (d2: state abs) :=
     files_reboot_rep d2 d1.

   Lemma exec_compiled_preserves_refinement_finished_core:
    forall T (p2: abs_core.(Core.operation) T) o1 s1 s1' r u,
        (exists s2, refines s1 s2) ->
        impl.(exec) u o1 s1 (compile T p2) (Finished s1' r)->
        (exists s2', refines s1' s2').
  Proof.
    intros; destruct p2; simpl in *; cleanup.
    {
      eapply read_finished in H0; eauto; cleanup; eauto.
    }
    {
      unfold refines in *; cleanup.
      eapply write_finished in H0; eauto.
      split_ors; cleanup; eauto.
    }
    {
      unfold refines in *; cleanup.
      eapply extend_finished in H0; cleanup; eauto.
      split_ors; cleanup; eauto.
    }
    {
      unfold refines in *; cleanup.
      eapply change_owner_finished in H0; cleanup; eauto.
      split_ors; cleanup; eauto.
    }
    {
      unfold refines in *; cleanup.
      eapply create_finished in H0; cleanup; eauto.
      split_ors; cleanup; eauto.
    }
    {
      unfold refines in *; cleanup.
      eapply delete_finished in H0; cleanup; eauto.
      split_ors; cleanup; eauto.
    }
    {
      unfold refines in *; cleanup.
      eapply recover_finished in H0; eauto.
      unfold files_rep, files_reboot_rep, files_crash_rep in *;
      cleanup; eauto.
    }
  Qed.

  Definition FDOperationRefinement := Build_CoreRefinement compile refines refines_reboot token_refines exec_compiled_preserves_refinement_finished_core.
  Definition FDRefinement := LiftRefinement abs FDOperationRefinement.

  Notation "| p |" := (Op abs_core p)(at level 60).

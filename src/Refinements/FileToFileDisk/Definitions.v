Require Import Framework FSParameters.
Require Import AuthenticatedDiskLayer FileDiskLayer File.
Close Scope predicate_scope.
Import ListNotations.

Local Definition low_op := (AuthenticatedDiskOperation).
Local Definition high_op := (FileDiskOperation inode_count).
Local Definition low := (AuthenticatedDiskLang).
Local Definition high := (FileDiskLang inode_count).

Fixpoint apply_list {A AEQ V} (m: @mem A AEQ V) l :=
  match l with
  | nil =>
    m
  | av :: l' =>
    apply_list (upd m (fst av) (snd av)) l'
  end.

Fixpoint compile T (p2: Operation.prog high_op T) : prog low T.
  destruct p2.
  exact (read a a0).
  exact (write a a0 v).
  exact (extend a v).
  exact (change_owner a u).
  exact (create u).
  exact (delete a).
Defined.

Definition oracle_refines_to T (d1: state low) (p: Operation.prog high_op T) o1 o2 : Prop :=
  let u := fst d1 in
  let dx := snd d1 in
  let d := mem_union (fst dx) (snd dx) in
  exists fm,
    files_rep fm d /\
    match p with
    | Read inum a =>
      (exists d1' r,
         exec low o1 d1 (read inum a) (Finished d1' r) /\
         o2 = [Cont] /\
         d1' = d1) \/
      
      (exists d1',
         exec low o1 d1 (read inum a) (Crashed d1') /\
         o2 = [CrashBefore] /\
         d1' = d1)
        
    | Write inum off v =>
      (exists d' r file,
         (
           exec low o1 d1 (write inum off v) (Finished (u, d') r) /\
           o2 =  [Cont] /\
           inum < inode_count /\
           fm inum = Some file /\
           file.(owner) = u /\
           off < length (file.(blocks)) /\
           let new_file := Build_File file.(owner)
                 (updN file.(blocks) off v) in
           files_rep (upd fm inum new_file) (mem_union (fst d') (snd d'))
         ) \/
         (
           exec low o1 d1 (write inum off v) (Finished (u, d') r) /\
           o2 =  [Cont] /\
           (
             inum >= disk_size \/
             fm inum = None \/
             (fm inum = Some file /\
              (file.(owner) <> u \/ off >= length (file.(blocks))))
           ) /\
           d' = dx
         )
      ) \/
       
      (exists d',
         (
           exec low o1 d1 (write inum off v) (Crashed (u, d')) /\
           o2 = [CrashBefore] /\
           d' = dx
         ) \/
         (exists file,
           exec low o1 d1 (write inum off v) (Crashed (u, d')) /\
           o2 = [CrashAfter] /\ 
           inum < inode_count /\
           fm inum = Some file /\
           file.(owner) = u /\
           off < length (file.(blocks)) /\
           let new_file := Build_File file.(owner)
               (updN file.(blocks) off v) in
           files_rep (upd fm inum new_file) (mem_union (fst d') (snd d'))     
         )
      )

     | Extend inum v =>
       (exists d' r file,
          (
            exec low o1 d1 (extend inum v) (Finished (u, d') r) /\
            o2 = [Cont] /\
            inum < disk_size /\
            fm inum = Some file /\
            file.(owner) = u /\
            let new_file := Build_File file.(owner) (file.(blocks) ++ [v]) in
            files_rep (upd fm inum new_file) (mem_union (fst d') (snd d'))
          ) \/
          (
            exec low o1 d1 (extend inum v) (Finished (u, d') r) /\
            o2 = [Cont] /\
            (inum >= disk_size \/
             fm inum = None \/
             (fm inum = Some file /\ file.(owner) <> u)) /\
            d' = dx
          ) \/
          (
            exec low o1 d1 (extend inum v) (Finished (u, d') r) /\
            o2 = [DiskFull] /\
            inum < disk_size /\
            fm inum = Some file /\
            file.(owner) = u /\
            (* condition on disk being full *)
            d' = dx
          )
       ) \/
  
       (exists d',
          (
            exec low o1 d1 (extend inum v) (Crashed (u, d')) /\
            o2 = [CrashBefore] /\
            d' = dx
          ) \/
          (exists file,
            exec low o1 d1 (extend inum v) (Crashed (u, d')) /\
            o2 = [CrashAfter] /\
            inum < disk_size /\
            fm inum = Some file /\
            file.(owner) = u /\
            let new_file := Build_File file.(owner) (file.(blocks) ++ [v]) in
            files_rep (upd fm inum new_file) (mem_union (fst d') (snd d'))
          )
       )
         
     | SetOwner inum own =>
       (exists d' r file,
          (
            exec low o1 d1 (change_owner inum own) (Finished (u, d') r) /\
            o2 = [Cont] /\
            inum < disk_size /\
            fm inum = Some file /\
            file.(owner) = u /\
            let new_file := Build_File own file.(blocks) in
            files_rep (upd fm inum new_file) (mem_union (fst d') (snd d'))
          ) \/
          (
            exec low o1 d1 (change_owner inum own) (Finished (u, d') r) /\
            o2 = [Cont] /\
            (
              inum >= disk_size \/
              fm inum = None \/
              (fm inum = Some file /\ file.(owner) <> u)
            ) /\
            d' = dx
          )
       ) \/
       (exists d',
          (
            exec low o1 d1 (change_owner inum own) (Crashed (u, d')) /\
            o2 = [CrashBefore] /\
            d' = dx
          ) \/
          (exists file,
            exec low o1 d1 (change_owner inum own) (Crashed (u, d')) /\
            o2 = [CrashAfter] /\
            inum < disk_size /\
            fm inum = Some file /\
            file.(owner) = u /\
            let new_file := Build_File own file.(blocks) in
            files_rep (upd fm inum new_file) (mem_union (fst d') (snd d'))
          )
       )
     | Create own =>
       (exists d',
          (exists inum,
            exec low o1 d1 (create own) (Finished (u, d') (Some inum)) /\
            o2 = [NewInum inum] /\
            inum < disk_size /\
            fm inum = None /\
            let new_file := Build_File own [] in
            files_rep (upd fm inum new_file) (mem_union (fst d') (snd d'))
          ) \/
          (
            exec low o1 d1 (create own) (Finished (u, d') None) /\
            o2 = [InodesFull] /\
            (forall inum, inum < disk_size -> fm inum <> None) /\
            d' = dx
          )
       ) \/
       (exists d',
          (
            exec low o1 d1 (create own) (Crashed (u, d')) /\
            o2 = [CrashBefore] /\
            d' = dx
          ) \/
          (exists inum,
            exec low o1 d1 (change_owner inum own) (Crashed (u, d')) /\
            o2 = [CrashAfterCreate inum] /\
            inum < disk_size /\
            fm inum = None /\
            let new_file := Build_File own [] in
            files_rep (upd fm inum new_file) (mem_union (fst d') (snd d'))
          )
       )
     | Delete inum =>
       (exists d' r file,
          (
            exec low o1 d1 (delete inum) (Finished (u, d') r) /\
            o2 = [Cont] /\
            inum < disk_size /\
            fm inum = Some file /\
            file.(owner) = u /\
            files_rep (Mem.delete fm inum) (mem_union (fst d') (snd d'))
          ) \/
          (
            exec low o1 d1 (delete inum) (Finished (u, d') r) /\
            o2 = [Cont] /\
            (
              inum >= disk_size \/
              fm inum = None \/
              (fm inum = Some file /\ file.(owner) <> u)
            ) /\
            d' = dx
          )
       ) \/
       (exists d',
          (
            exec low o1 d1 (delete inum) (Crashed (u, d')) /\
            o2 = [CrashBefore] /\
            d' = dx
          ) \/
          (exists file,
            exec low o1 d1 (delete inum) (Crashed (u, d')) /\
            o2 = [CrashAfter] /\
            inum < disk_size /\
            fm inum = Some file /\
            file.(owner) = u /\
            files_rep (Mem.delete fm inum) (mem_union (fst d') (snd d'))
          )
       )
     end.

   Definition refines_to (d1: state low) (d2: state high) :=
     fst d1 = fst d2 /\
     files_rep (snd d2) (mem_union (fst (snd d1)) (snd (snd d1))).

  Definition FileDiskOperationRefinement := Build_OperationRefinement compile refines_to oracle_refines_to.
  Definition FileDiskRefinement := LiftRefinement high FileDiskOperationRefinement.

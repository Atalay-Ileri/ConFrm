Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia SSECommon.
Require Import AuthenticationLayer TransactionalDiskLayer AuthenticatedDiskLayer.


Ltac unify_invariants :=
    match goal with
 |[H: files_inner_rep _ ?s,
 H0 : files_inner_rep _ ?s |- _] =>
 eapply FileInnerSpecs.files_inner_rep_eq in H; eauto; subst
 |[H: Inode.inode_rep _ ?s,
 H0 : Inode.inode_rep _ ?s |- _] =>
 eapply Inode.inode_rep_eq in H; eauto; subst
 |[H: DiskAllocator.block_allocator_rep _ ?s,
 H0 : DiskAllocator.block_allocator_rep _ ?s |- _] =>
 eapply DiskAllocator.block_allocator_rep_eq in H; eauto; subst 
 |[H: file_map_rep _ ?im ?s,
 H0 : file_map_rep _ ?im ?s |- _] =>
 eapply FileInnerSpecs.file_map_rep_eq in H; eauto; subst
end.

Lemma exec_Crash_finished_exfalso:
forall O (L: Language O) u T (p: L.(prog) T) s s' r,
~exec L u [Language.Crash O] s p (Finished s' r).
Proof.
    unfold not; induction p; simpl; intros;
    invert_exec.
    symmetry in H2; apply app_eq_unit in H2;
    intuition cleanup;
    exfalso; eapply exec_empty_oracle; eauto.
Qed.

Lemma exec_finished_no_crash_tokens:
forall u T (p: Definitions.impl.(prog) T) o s s' r,
exec Definitions.impl u o s p (Finished s' r) -> 
(forall (t: Definitions.impl.(token)), In t o -> 
t <> Language.Crash _ /\ 
t <> OpToken AuthenticatedDiskOperation (Token1 AuthenticationOperation _ Crash) /\
t <> OpToken AuthenticatedDiskOperation (Token2 _ (TransactionalDiskOperation FSParameters.data_length) CrashBefore) /\
t <> OpToken AuthenticatedDiskOperation (Token2 _ (TransactionalDiskOperation FSParameters.data_length) CrashAfter)).
Proof.
    induction p; simpl; intros;
    invert_exec.
    {
        destruct o; invert_exec;
        destruct o; invert_exec;
        (inversion H0; cleanup;
        [ repeat (split; try congruence)
        | inversion H]).
    }
    {
        inversion H0; cleanup;
        [ repeat (split; try congruence)
        | inversion H].
    }
    {
        eapply in_app_iff in H1; split_ors; eauto.
    }
Qed.   

Lemma exec_crashed_exists_crash_token:
forall u T (p: Definitions.impl.(prog) T) o s s',
exec Definitions.impl u o s p (Crashed s') -> 
(exists (t: Definitions.impl.(token)), 
In t o /\
( 
t = Language.Crash _ \/
t = OpToken AuthenticatedDiskOperation (Token1 AuthenticationOperation _ Crash) \/
t = OpToken AuthenticatedDiskOperation (Token2 _ (TransactionalDiskOperation FSParameters.data_length) CrashBefore) \/
t = OpToken AuthenticatedDiskOperation (Token2 _ (TransactionalDiskOperation FSParameters.data_length) CrashAfter))
).
Proof.
    induction p; simpl; intros;
    invert_exec.
    {
        destruct o; invert_exec;
        destruct o; invert_exec.
        all: eexists; split; [econstructor; eauto | eauto].
    }
    {
        eexists; split; [econstructor; eauto | eauto].
    }
    {
        split_ors; cleanup.
        edestruct IHp; eauto.
        cleanup.
        eexists; split.
        apply in_app_iff; eauto.
        eauto.

        edestruct H; eauto.
        cleanup.
        eexists; split.
        apply in_app_iff; eauto.
        eauto.
    }
Qed.   

Lemma exec_finished_not_crashed_AuthenticatedDisk:
forall u T (p1 p2: Definitions.impl.(prog) T) o s s' s1 s1' r,
exec Definitions.impl u o s p1 (Finished s' r) -> 
~exec Definitions.impl u o s1 p2 (Crashed s1').
Proof.
  unfold not; intros.
  eapply exec_crashed_exists_crash_token in H0; cleanup.
  eapply exec_finished_no_crash_tokens in H; eauto.
  cleanup; intuition; subst; congruence.
Qed.

Import FileDiskLayer.

Local Ltac solve_ret_iff_goal:=
try solve [try lia; try congruence];
try solve [
        pose proof DiskAllocatorParams.blocks_fit_in_disk;
        pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk;
        pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds;
        pose proof DiskAllocatorParams.num_of_blocks_in_bounds;
        unfold DiskAllocatorParams.bitmap_addr, DiskAllocatorParams.num_of_blocks,
        Inode.InodeAllocatorParams.bitmap_addr, Inode.InodeAllocatorParams.num_of_blocks in *;
       try lia];
     try solve [split; congruence];
     try solve [
         simpl in *;
        match goal with
        [H: _ :: _ = _ |- _] =>
        inversion H
        end];
     try solve [
        simpl in *;
        match goal with
        [H: _ ++ ?l = _ ++ ?l |- _] =>
        apply app_inv_tail in H; cleanup;
        apply map_ext_eq in H; 
        [| intros; cleanup; eauto;
        congruence]; subst
        end;
        match goal with
        | [H: forall _ _ _ _ _ _ _,
        _ ->
        _ ->
        _ = None <-> _ = None|- _] =>
        edestruct H; eauto
        end];
    try solve [
        simpl in *;
        match goal with
        [H: _ ++ ?l = ?l |- _] =>
        rewrite <- app_nil_l in H;
        apply app_inv_tail in H; cleanup;
        apply map_eq_nil in H; subst;
        exfalso; eapply exec_empty_oracle; eauto
        end 
    ];
    try solve [
        cleanup;
        match goal with
            [H: [] = map _ _ |- _] =>
        symmetry in H;
        apply map_eq_nil in H; subst
        end;
        exfalso; eapply exec_empty_oracle; eauto].


Ltac depth_first_solve := (invert_exec; solve_ret_iff_goal); try (only 1: depth_first_solve).


Lemma auth_then_exec_same_type_ret:
forall u o s1 s2 T (p1 p2: addr -> (TransactionalDiskLang FSParameters.data_length).(prog) (option T)) inum  sr1 sr2 r1 r2,
(forall o' s1' s2' sr1' sr2' ret1 ret2,
 exec (TransactionalDiskLang FSParameters.data_length) u o' s1' (p1 inum) (Finished sr1' ret1) ->
 exec (TransactionalDiskLang FSParameters.data_length) u o' s2' (p2 inum) (Finished sr2' ret2) ->
 ret1 = None <-> ret2 = None) ->
 exec Definitions.impl u o s1 (auth_then_exec inum p1) (Finished sr1 r1) ->
 exec Definitions.impl u o s2 (auth_then_exec inum p2) (Finished sr2 r2) ->
 r1 = None <-> r2 = None.
 Proof.
     Transparent Inode.get_owner Inode.get_inode.
     unfold auth_then_exec, Inode.get_owner, 
     Inode.get_inode, Inode.InodeAllocator.read.
     intros. 
     depth_first_solve.
 Qed. 
 Lemma write_inner_same_type_ret:
 forall (o' : oracle' (TransactionalDiskOperation FSParameters.data_length))
(s1' s2' sr1'
sr2' : Language.state'
     (TransactionalDiskOperation FSParameters.data_length))
(ret1 ret2 : option unit) off v v' inum u,
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s1' (write_inner off v inum) (Finished sr1' ret1) ->
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2' (write_inner off v' inum) (Finished sr2' ret2) ->
ret1 = None <-> ret2 = None.
Proof.  
Transparent Inode.get_block_number Inode.get_inode.
unfold write_inner, Inode.get_block_number, Inode.get_inode,
Inode.InodeAllocator.read, DiskAllocator.write.
intros.
depth_first_solve.
Qed.

Lemma change_owner_inner_same_type_ret:
forall (o' : oracle' (TransactionalDiskOperation FSParameters.data_length))
(s1' s2' sr1'
sr2' : Language.state'
    (TransactionalDiskOperation FSParameters.data_length))
(ret1 ret2 : option unit) own inum u,
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s1' (change_owner_inner own inum) (Finished sr1' ret1) ->
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2' (change_owner_inner own inum) (Finished sr2' ret2) ->
ret1 = None <-> ret2 = None.
Proof. 
Transparent Inode.change_owner Inode.get_block_number Inode.get_inode.
unfold change_owner_inner, Inode.change_owner, Inode.set_inode, Inode.get_inode,
Inode.InodeAllocator.read, Inode.InodeAllocator.write.
intros.
depth_first_solve.
Qed. 

Lemma delete_inner_same_type_ret:
forall (o' : oracle' (TransactionalDiskOperation FSParameters.data_length))
(s1' s2' sr1'
sr2' : Language.state'
    (TransactionalDiskOperation FSParameters.data_length))
(ret1 ret2 : option unit) inum u,
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s1' (delete_inner inum) (Finished sr1' ret1) ->
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2' (delete_inner inum) (Finished sr2' ret2) ->
ret1 = None <-> ret2 = None.
Proof. 
Transparent Inode.change_owner Inode.get_all_block_numbers Inode.get_inode
Inode.free.
unfold delete_inner, Inode.get_all_block_numbers, Inode.free, 
Inode.set_inode, Inode.get_inode, 
Inode.InodeAllocator.read, Inode.InodeAllocator.write, 
 Inode.InodeAllocator.free.
intros.
depth_first_solve.
all: cleanup;
repeat rewrite app_assoc in *;
repeat match goal with
|[H: _ ++ [_] = _ ++ [_] |- _] =>
apply app_inj_tail in H; cleanup
end; try congruence.
Qed. 

Lemma extend_inner_same_type_ret:
forall (o' : oracle' (TransactionalDiskOperation FSParameters.data_length))
(s1' s2' sr1'
sr2' : Language.state'
    (TransactionalDiskOperation FSParameters.data_length))
(ret1 ret2 : option unit) v v' inum u,
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s1' (extend_inner v inum) (Finished sr1' ret1) ->
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2' (extend_inner v' inum) (Finished sr2' ret2) ->
ret1 = None <-> ret2 = None.
Proof. 
Transparent Inode.extend Inode.get_inode.
unfold extend_inner, Inode.extend, 
DiskAllocator.alloc, 
Inode.set_inode, Inode.get_inode,
Inode.InodeAllocator.read, 
Inode.InodeAllocator.write.
intros.
depth_first_solve.
Qed. 

Lemma create_same_type_ret:
forall (o' : oracle AuthenticatedDiskLang)
(s1' s2' sr1'
sr2' : Language.state
    AuthenticatedDiskLang)
(ret1 ret2 : option nat) own u,
exec (AuthenticatedDiskLang) 
u o' s1' (create own) (Finished sr1' ret1) ->
exec (AuthenticatedDiskLang) 
u o' s2' (create own) (Finished sr2' ret2) ->
ret1 = None <-> ret2 = None.
Proof. 
Transparent Inode.alloc.
unfold create, Inode.alloc, 
Inode.InodeAllocator.alloc. 
intros.
depth_first_solve.
Qed. 

Set Nested Proofs Allowed.
Lemma upd_nop_rev:
forall (A V : Type) (AEQ : EqDec A) 
(m : A -> option V) (a : A) (v : V),
Mem.upd m a v = m ->
m a = Some v.
Proof.
    intros; rewrite <- H.
    apply Mem.upd_eq; eauto.
Qed.

Lemma seln_eq_updn_eq_rev:
forall (A : Type) (l : list A) (i : nat) (a def : A),
updn l i a = l -> 
i < length l ->
seln l i def = a.
Proof.
    induction l; simpl; intros.
    lia.
    destruct i; simpl in *.
    congruence.
    eapply IHl.
    congruence.
    lia.
Qed.

Ltac invert_exec_local :=
match goal with
| [H: exec (TransactionalDiskLang _) _ _ _ (Ret _) _ |- _] =>
    invert_exec'' H
| [H: exec (TransactionalDiskLang _) _ _ _ (Op _ _) _ |- _] =>
invert_exec'' H
| [H: Core.exec (TransactionalDiskOperation _) _ _ _ _ _ |- _] =>
invert_exec'' H
| [H: TransactionalDiskLayer.exec' _ _ _ _ _ _ |- _] =>
invert_exec'' H
| [H: AuthenticationLayer.exec' _ _ _ _ _ |- _] =>
invert_exec'' H
end.


Lemma files_inner_rep_extract_inode_rep:
forall fm s,
files_inner_rep fm s ->
exists inode_map, Inode.inode_rep inode_map s.
Proof.
    unfold files_inner_rep; intros; cleanup; eauto.
Qed.

Lemma files_inner_rep_extract_disk_allocator_rep:
forall fm s,
files_inner_rep fm s ->
exists blocks_map, DiskAllocator.block_allocator_rep blocks_map s.
Proof.
    unfold files_inner_rep; intros; cleanup; eauto.
Qed.


Ltac apply_specs :=
match goal with
| [H: exec (TransactionalDiskLang _) 
_ _ _ (Inode.get_owner _) (Crashed _) |- _] =>
    eapply Inode.get_owner_crashed in H; 
    [|repeat cleanup_pairs]; eauto
| [H: exec (TransactionalDiskLang _) 
_ _ _ (Inode.get_owner _) (Finished _ _) |- _] =>
    eapply Inode.get_owner_finished in H; 
    [|repeat cleanup_pairs]; eauto
| [H: exec (TransactionalDiskLang _) 
_ _ _ (Inode.get_block_number _ _) (Crashed _) |- _] =>
    eapply Inode.get_block_number_crashed in H; 
    [|repeat cleanup_pairs]; eauto
| [H: exec (TransactionalDiskLang _) 
_ _ _ (Inode.get_block_number _ _) (Finished _ _) |- _] =>
    eapply Inode.get_block_number_finished in H; 
    [|repeat cleanup_pairs]; eauto
| [H: exec (TransactionalDiskLang _) 
_ _ _ (Inode.get_all_block_numbers _) (Crashed _) |- _] =>
    eapply Inode.get_block_number_crashed in H; 
    [|repeat cleanup_pairs]; eauto
| [H: exec (TransactionalDiskLang _) 
_ _ _ (Inode.get_all_block_numbers _) (Finished _ _) |- _] =>
    eapply Inode.get_block_number_finished in H; 
    [|repeat cleanup_pairs]; eauto
| [H: exec (TransactionalDiskLang _) 
_ _ _ (DiskAllocator.write _ _) (Crashed _) |- _] =>
    eapply DiskAllocator.write_crashed in H; eauto
| [H: exec (TransactionalDiskLang _) 
_ _ _ (DiskAllocator.write _ _) (Finished _ _) |- _] =>
    eapply DiskAllocator.write_finished in H; 
    [|shelve]; eauto
| [H: exec (TransactionalDiskLang _) 
_ _ _ (Inode.extend _ _) (Crashed _) |- _] =>
    eapply Inode.extend_crashed in H; 
    [|shelve]; eauto
| [H: exec (TransactionalDiskLang _) 
_ _ _ (Inode.extend _ _) (Finished _ _) |- _] =>
    eapply Inode.extend_finished in H; 
    [|shelve| shelve |]; eauto
| [H: exec (TransactionalDiskLang _) 
_ _ _ (Inode.alloc _) (Crashed _) |- _] =>
    eapply Inode.alloc_crashed in H; 
    [|repeat cleanup_pairs]; eauto
| [H: exec (TransactionalDiskLang _) 
_ _ _ (Inode.alloc _) (Finished _ _) |- _] =>
    eapply Inode.alloc_finished in H; 
    [|repeat cleanup_pairs]; eauto
end.

Ltac split_crash :=
    match goal with
    | [H: exec _ _ _ _ _ _ \/ _ |- _] =>
    destruct H
    end.

Opaque Inode.get_owner Inode.get_block_number DiskAllocator.write.


 Lemma list_extend_ne:
 forall T (l : list T) t,
 l <> l ++[t].
 Proof.
    unfold not; induction l; simpl; intros; try congruence.
 Qed.

 Lemma all_block_numbers_in_bound:
    forall x x1 s2 x12 x14 inum ,
    Inode.inode_rep x1 s2 ->
    DiskAllocator.block_allocator_rep x12 s2 ->
    file_map_rep x x1 x12 ->
    x1 inum = Some x14 ->
    Forall (fun n : nat => n < DiskAllocatorParams.num_of_blocks)
  (Inode.block_numbers x14).
  Proof.
      intros.
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H2; eauto.
    cleanup.

    unfold file_map_rep in *; cleanup.
    eapply H4 in H2; eauto.
    unfold file_rep in *; cleanup.
    eapply Forall_forall; intros.
    eapply in_seln_exists in H7; cleanup.
    erewrite nth_seln_eq in H8.
    edestruct H6.
    erewrite nth_error_nth'; eauto.
    cleanup.
    unfold DiskAllocator.block_allocator_rep in H0; cleanup.
    destruct (Compare_dec.lt_dec x2 DiskAllocatorParams.num_of_blocks); eauto.
    erewrite e1  in H10; cleanup.
    rewrite H8; lia.
    Unshelve.
    eauto.
  Qed.

  Lemma write_inner_finished_oracle_eq:
  forall u u' ex fm1 fm2 o o' o1 o2 s1 s2 s1' s2' r1 r2 off v v' inum,
  exec (TransactionalDiskLang FSParameters.data_length) 
 u o s1 (write_inner off v inum)
 (Finished s1' r1) ->
 o ++ o1 = o' ++ o2 ->
 files_inner_rep fm1 (fst s1) ->
 files_inner_rep fm2 (fst s2) ->
 same_for_user_except u' ex fm1 fm2 ->
 exec (TransactionalDiskLang FSParameters.data_length) 
 u o' s2 (write_inner off v' inum)
 (Finished s2' r2) ->
 o = o' /\ (r1 = None <-> r2 = None).
 Proof.
  Transparent write_inner.
  unfold not, write_inner.
  intros.
  cleanup; repeat invert_exec;
  repeat (try split_ors; cleanup; repeat invert_exec;
  try solve [simpl in *; cleanup; split; eauto;
  intuition congruence]).

    {
        unfold files_inner_rep in *; cleanup.
        repeat rewrite <- app_assoc in H0; eauto;
     try eapply Inode.get_block_number_finished_oracle_eq in H; eauto; subst;
     cleanup; eauto.
     try eapply DiskAllocator.write_finished_oracle_eq in H6; eauto; subst;
     cleanup; eauto.
     split; eauto;
     intuition congruence.
     intros.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H11; 
     eauto; cleanup.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H12; 
     eauto; cleanup.
     unfold same_for_user_except in *; cleanup.
     eapply_fresh H16 in H13; eauto; cleanup.
     unfold file_map_rep in *; cleanup.
     eapply H19 in H11; eauto.
     eapply H20 in H12; eauto.
     unfold file_rep in *; cleanup; eauto.
    }
    {
        unfold files_inner_rep in *; cleanup.
        repeat rewrite <- app_assoc in H0; eauto;
     try eapply Inode.get_block_number_finished_oracle_eq in H; eauto; subst;
     cleanup; eauto.
     intuition congruence.
     intros.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H10; 
     eauto; cleanup.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H11; 
     eauto; cleanup.
     unfold same_for_user_except in *; cleanup.
     eapply_fresh H15 in H12; eauto; cleanup.
     unfold file_map_rep in *; cleanup.
     eapply H18 in H10; eauto.
     eapply H19 in H11; eauto.
     unfold file_rep in *; cleanup; eauto.
    }
    {
        unfold files_inner_rep in *; cleanup.
        repeat rewrite <- app_assoc in H0; eauto;
     try eapply Inode.get_block_number_finished_oracle_eq in H; eauto; subst;
     cleanup; eauto.
     intuition congruence.
     intros.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H10; 
     eauto; cleanup.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H11; 
     eauto; cleanup.
     unfold same_for_user_except in *; cleanup.
     eapply_fresh H15 in H12; eauto; cleanup.
     unfold file_map_rep in *; cleanup.
     eapply H18 in H10; eauto.
     eapply H19 in H11; eauto.
     unfold file_rep in *; cleanup; eauto.
    }
    {
        unfold files_inner_rep in *; cleanup.
        repeat rewrite <- app_assoc in H0; eauto;
     try eapply Inode.get_block_number_finished_oracle_eq in H; eauto; subst;
     cleanup; eauto.
     intuition congruence.
     intros.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H9; 
     eauto; cleanup.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H10; 
     eauto; cleanup.
     unfold same_for_user_except in *; cleanup.
     eapply_fresh H14 in H11; eauto; cleanup.
     unfold file_map_rep in *; cleanup.
     eapply H17 in H9; eauto.
     eapply H18 in H10; eauto.
     unfold file_rep in *; cleanup; eauto.
    }
  Opaque write_inner.
 Qed.



 Lemma extend_inner_finished_oracle_eq:
 forall u o o' o1 o2 s1 s2 s1' s2' r1 r2 v v' inum inum',
 exec (TransactionalDiskLang FSParameters.data_length) 
u o s1 (extend_inner v inum)
(Finished s1' r1) ->
o ++ o1 = o' ++ o2 ->
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2 (extend_inner v' inum')
(Finished s2' r2) ->
o = o' /\ (r1 = None <-> r2 = None).
Proof.
 Transparent extend_inner.
 unfold not, extend_inner.
 intros.
 cleanup; repeat invert_exec;
 repeat (try split_ors; cleanup; repeat invert_exec;
 try solve [simpl in *; cleanup; split; eauto;
 intuition congruence]);
 try solve [ 
    repeat rewrite <- app_assoc in H0; eauto;
    try eapply DiskAllocator.alloc_finished_oracle_eq in H; eauto; subst;
    cleanup; eauto;
    try eapply Inode.extend_finished_oracle_eq in H3; eauto; subst;
    cleanup; eauto;
    split; eauto;
    intuition congruence].
 Opaque extend_inner.
Qed.

Lemma change_owner_inner_finished_oracle_eq:
forall u o o' o1 o2 s1 s2 s1' s2' r1 r2 v v' inum inum',
exec (TransactionalDiskLang FSParameters.data_length) 
u o s1 (change_owner_inner v inum)
(Finished s1' r1) ->
o ++ o1 = o' ++ o2 ->
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2 (change_owner_inner v' inum')
(Finished s2' r2) ->
o = o' /\ (r1 = None <-> r2 = None).
Proof.
Transparent change_owner_inner.
unfold not, change_owner_inner.
intros.
eapply Inode.change_owner_finished_oracle_eq; eauto.
Opaque change_owner_inner.
Qed.


Lemma free_all_blocks_finished_oracle_eq:
forall blocks blocks' u o o' o1 o2 s1 s2 s1' s2' r1 r2,
exec (TransactionalDiskLang FSParameters.data_length) 
u o s1 (free_all_blocks blocks)
(Finished s1' r1) ->
o ++ o1 = o' ++ o2 ->
Forall (fun n => n < DiskAllocatorParams.num_of_blocks) blocks ->
Forall (fun n => n < DiskAllocatorParams.num_of_blocks) blocks' ->
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2 (free_all_blocks blocks')
(Finished s2' r2) ->
o = o' /\ (r1 = None <-> r2 = None).
Proof.
    induction blocks; simpl; intros; eauto.
    {
        invert_exec.
        destruct blocks'; 
        simpl in *;
        invert_exec; 
        cleanup.
        split; eauto;
        intuition congruence.
        unfold DiskAllocator.free in *.
        rewrite <- app_assoc in H0.
        cleanup; repeat invert_exec; cleanup;
        rewrite <- app_assoc in H0; simpl in *; cleanup.

        unfold DiskAllocator.free in *.
        rewrite <- app_assoc in H0.
        cleanup; repeat invert_exec; cleanup;
        try rewrite <- app_assoc in H0; simpl in *; cleanup.
        inversion H2; lia.
    }
    {
        repeat invert_exec;
        rewrite <- app_assoc in H0; simpl in *; cleanup.
        {
            destruct blocks'; 
            simpl in *;
            invert_exec; simpl in *;
            cleanup.
            
        unfold DiskAllocator.free in *;
        cleanup; repeat invert_exec; cleanup;
        rewrite <- app_assoc in H0; simpl in *; cleanup.

        rewrite <- app_assoc in H0; simpl in *; cleanup.
        eapply DiskAllocator.free_finished_oracle_eq in H; eauto;
        cleanup.
        eapply IHblocks in H5; eauto.
        cleanup; eauto. 
        inversion H1; inversion H2; eauto.
        inversion H1; inversion H2; eauto.

        rewrite <- app_assoc in H0; simpl in *; cleanup.
        eapply DiskAllocator.free_finished_oracle_eq in H; eauto;
        cleanup.
        intuition congruence.
        }
        {
            destruct blocks'; 
            simpl in *;
            invert_exec; simpl in *;
            cleanup.
            
            unfold DiskAllocator.free in *;
            cleanup; repeat invert_exec; simpl in *; cleanup.
            inversion H1; lia.
            rewrite <- app_assoc in H0; simpl in *; cleanup.
            eapply DiskAllocator.free_finished_oracle_eq in H; eauto;
            cleanup.
            intuition congruence.

            rewrite <- app_assoc in H0; simpl in *; cleanup.
            eapply DiskAllocator.free_finished_oracle_eq in H; eauto;
            cleanup.
            invert_exec; eauto.
        }
    }
Qed.

        
Lemma delete_inner_finished_oracle_eq:
forall u o o' o1 o2 s1 s2 s1' s2' r1 r2 inum inum',
exec (TransactionalDiskLang FSParameters.data_length) 
u o s1 (delete_inner inum)
(Finished s1' r1) ->
o ++ o1 = o' ++ o2 ->
exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2 (delete_inner inum')
(Finished s2' r2) ->
(exists fm, files_inner_rep fm (fst s1)) ->
(exists fm, files_inner_rep fm (fst s2)) ->
o = o' /\ (r1 = None <-> r2 = None).
Proof.
Transparent delete_inner.
unfold not, delete_inner.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec;
try solve [simpl in *; cleanup]);
try solve [ repeat rewrite <- app_assoc in H0; eauto;
eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto;
cleanup; intuition congruence].
{
    repeat rewrite <- app_assoc in H0; eauto;
    eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto;
    cleanup.

    eapply free_all_blocks_finished_oracle_eq in H6; eauto;
    cleanup.

    eapply Inode.free_finished_oracle_eq in H7; eauto;
    cleanup.
    split; intuition eauto.

    {

    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H1; eauto.
    cleanup; split_ors; cleanup.
    clear H13;
    eapply all_block_numbers_in_bound; eauto.
    }
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H; eauto.
    cleanup; split_ors; cleanup.

    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
}

{
    repeat rewrite <- app_assoc in H0; eauto;
    eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto;
    cleanup.

    eapply free_all_blocks_finished_oracle_eq in H6; eauto;
    cleanup.
    intuition congruence.
    {

    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H1; eauto.
    cleanup; split_ors; cleanup.
    clear H12;
    eapply all_block_numbers_in_bound; eauto.
    }
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H; eauto.
    cleanup; split_ors; cleanup.

    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
}
{
    repeat rewrite <- app_assoc in H0; eauto;
    eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto;
    cleanup.

    eapply free_all_blocks_finished_oracle_eq in H5; eauto;
    cleanup. 
    intuition congruence.
    {

    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H1; eauto.
    cleanup; split_ors; cleanup.
    clear H12;
    eapply all_block_numbers_in_bound; eauto.
    }
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H; eauto.
    cleanup; split_ors; cleanup.

    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
}

{
    repeat rewrite <- app_assoc in H0; eauto;
    eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto;
    cleanup.

    eapply free_all_blocks_finished_oracle_eq in H5; eauto;
    cleanup. 
    intuition congruence.
    {

    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H1; eauto.
    cleanup; split_ors; cleanup.
    clear H11;
    eapply all_block_numbers_in_bound; eauto.
    }
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H; eauto.
    cleanup; split_ors; cleanup.

    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
}
Unshelve.
all: eauto.
Opaque delete_inner.
Qed.


(* Finished, not crasherd lemmas*)
Lemma write_inner_finished_not_crashed:
forall u u' ex fm1 fm2 o o' o1 o2 s1 s2 s1' s2' r v v' inum off,
exec (TransactionalDiskLang FSParameters.data_length) 
u o s1 (write_inner off v inum)
(Finished s1' r) ->
o ++ o1 = o' ++ o2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
same_for_user_except u' ex fm1 fm2 ->
~exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2 (write_inner off v' inum)
(Crashed s2').
Proof.
    Transparent write_inner.
unfold not, write_inner.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec;
try solve [simpl in *; cleanup]);
try solve [ repeat rewrite <- app_assoc in H0; eauto;
eapply Inode.get_block_number_finished_not_crashed; eauto].

{
    unfold files_inner_rep in *; cleanup.
repeat rewrite <- app_assoc in H0; eauto;
eapply Inode.get_block_number_finished_oracle_eq in H; eauto; subst;
cleanup; eauto.
eapply DiskAllocator.write_finished_not_crashed; eauto;
intuition congruence.
intros.
eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H11; 
eauto; cleanup.
eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H12; 
eauto; cleanup.
unfold same_for_user_except in *; cleanup.
eapply_fresh H16 in H13; eauto; cleanup.
unfold file_map_rep in *; cleanup.
eapply H19 in H11; eauto.
eapply H20 in H12; eauto.
unfold file_rep in *; cleanup; eauto.
}
{
    unfold files_inner_rep in *; cleanup.
repeat rewrite <- app_assoc in H0; eauto;
eapply Inode.get_block_number_finished_oracle_eq in H; eauto; subst;
cleanup; eauto.
intuition congruence.
intros.
eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H10; 
eauto; cleanup.
eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H11; 
eauto; cleanup.
unfold same_for_user_except in *; cleanup.
eapply_fresh H15 in H12; eauto; cleanup.
unfold file_map_rep in *; cleanup.
eapply H18 in H10; eauto.
eapply H19 in H11; eauto.
unfold file_rep in *; cleanup; eauto.
}

{
    unfold files_inner_rep in *; cleanup.
repeat rewrite <- app_assoc in H0; eauto;
eapply Inode.get_block_number_finished_oracle_eq in H; eauto; subst;
cleanup; eauto.
intuition congruence.
intros.
eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H10; 
eauto; cleanup.
eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H11; 
eauto; cleanup.
unfold same_for_user_except in *; cleanup.
eapply_fresh H15 in H12; eauto; cleanup.
unfold file_map_rep in *; cleanup.
eapply H18 in H10; eauto.
eapply H19 in H11; eauto.
unfold file_rep in *; cleanup; eauto.
}

{
    unfold files_inner_rep in *; cleanup.
repeat rewrite <- app_assoc in H0; eauto;
eapply Inode.get_block_number_finished_oracle_eq in H; eauto; subst;
cleanup; eauto.
simpl in *; cleanup.
intros.
eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H9; 
eauto; cleanup.
eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H10; 
eauto; cleanup.
unfold same_for_user_except in *; cleanup.
eapply_fresh H14 in H11; eauto; cleanup.
unfold file_map_rep in *; cleanup.
eapply H17 in H9; eauto.
eapply H18 in H10; eauto.
unfold file_rep in *; cleanup; eauto.
}
Opaque write_inner.
Qed.

Lemma extend_inner_finished_not_crashed:
forall u o o' o1 o2 s1 s2 s1' s2' r v v' inum inum',
exec (TransactionalDiskLang FSParameters.data_length) 
u o s1 (extend_inner inum v)
(Finished s1' r) ->
o ++ o1 = o' ++ o2 ->
~exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2 (extend_inner inum' v')
(Crashed s2').
Proof.
    Transparent extend_inner.
unfold not, extend_inner.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec;
try solve [simpl in *; cleanup]);
try solve [ repeat rewrite <- app_assoc in H0; eauto;
eapply DiskAllocator.alloc_finished_not_crashed; eauto];

try solve [ 
repeat rewrite <- app_assoc in H0; eauto;
eapply DiskAllocator.alloc_finished_oracle_eq in H; eauto; subst;
cleanup; eauto;
eapply Inode.extend_finished_not_crashed; eauto;
intuition congruence ].

repeat rewrite <- app_assoc in H0; eauto;
eapply DiskAllocator.alloc_finished_oracle_eq in H; eauto; subst;
simpl in *; cleanup; eauto.

Unshelve.
all: eauto.
all: repeat econstructor; eauto.
Opaque extend_inner.
Qed.


Lemma change_owner_inner_finished_not_crashed:
forall u o o' o1 o2 s1 s2 s1' s2' r v v' inum inum',
exec (TransactionalDiskLang FSParameters.data_length) 
u o s1 (change_owner_inner inum v)
(Finished s1' r) ->
o ++ o1 = o' ++ o2 ->
~exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2 (change_owner_inner inum' v')
(Crashed s2').
Proof.
    Transparent change_owner_inner.
unfold not, change_owner_inner.
intros.
eapply Inode.change_owner_finished_not_crashed; eauto.
Opaque change_owner_inner.
Qed.

Lemma free_all_blocks_finished_not_crashed:
forall blocks blocks' u o o' o1 o2 s1 s2 s1' s2' r,
exec (TransactionalDiskLang FSParameters.data_length) 
u o s1 (free_all_blocks blocks)
(Finished s1' r) ->
o ++ o1 = o' ++ o2 ->
Forall (fun n => n < DiskAllocatorParams.num_of_blocks) blocks ->
Forall (fun n => n < DiskAllocatorParams.num_of_blocks) blocks' ->
~exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2 (free_all_blocks blocks')
(Crashed s2').
Proof.
    unfold not; induction blocks; simpl; intros;
    destruct blocks'; simpl in *;
    repeat invert_exec; simpl in *; cleanup;
    try solve [rewrite <- app_assoc in H0;
    unfold DiskAllocator.free in *; 
    cleanup; repeat invert_exec; simpl in *; cleanup].
    {
        rewrite <- app_assoc in H0.
        split_ors; cleanup;
         repeat invert_exec; simpl in *; cleanup.
        unfold DiskAllocator.free in *; 
        cleanup; repeat invert_exec.
        split_ors; cleanup;
         repeat invert_exec; simpl in *; cleanup.
         simpl in *; cleanup.
         unfold DiskAllocator.free in *; 
        cleanup; repeat invert_exec;
        simpl in *; cleanup.

        unfold DiskAllocator.free in *; 
        cleanup; repeat invert_exec;
        simpl in *; cleanup.
        inversion H2; eauto.
    }
    {
        repeat rewrite <- app_assoc in H0.
        split_ors; cleanup;
         repeat invert_exec; simpl in *; cleanup.
         eapply DiskAllocator.free_finished_not_crashed; eauto.
         eapply DiskAllocator.free_finished_oracle_eq in H; eauto; cleanup.
         eapply IHblocks.
         eauto.
         4: eauto.
         all: eauto.
         inversion H1; eauto.
         inversion H2; eauto.

         eapply DiskAllocator.free_finished_oracle_eq in H; eauto;
        cleanup; intuition congruence.
    }
    {
        repeat rewrite <- app_assoc in H0.
        split_ors; cleanup;
         repeat invert_exec; simpl in *; cleanup.
         eapply DiskAllocator.free_finished_not_crashed; eauto.
         eapply DiskAllocator.free_finished_oracle_eq in H; eauto; cleanup;
         intuition congruence.

         eapply DiskAllocator.free_finished_oracle_eq in H; eauto; cleanup.
         repeat invert_exec; simpl in *; cleanup.
    }
Qed.


Lemma delete_inner_finished_not_crashed:
forall u o o' o1 o2 s1 s2 s1' s2' r inum inum',
exec (TransactionalDiskLang FSParameters.data_length) 
u o s1 (delete_inner inum)
(Finished s1' r) ->
o ++ o1 = o' ++ o2 ->
(exists fm, files_inner_rep fm (fst s1)) ->
(exists fm, files_inner_rep fm (fst s2)) ->
~exec (TransactionalDiskLang FSParameters.data_length) 
u o' s2 (delete_inner inum')
(Crashed s2').
Proof.
Transparent delete_inner.
unfold not, delete_inner.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec;
try solve [simpl in *; cleanup]);
try solve [ repeat rewrite <- app_assoc in H0; eauto;
eapply Inode.get_all_block_numbers_finished_not_crashed; eauto];

try solve [ 
repeat rewrite <- app_assoc in H0; eauto;
eapply Inode.get_all_block_numbers_finished_oracle_eq in H; eauto; subst;
cleanup; eauto;
eapply free_all_blocks_finished_not_crashed; eauto;
intuition congruence ].

{
    repeat rewrite <- app_assoc in H0; eauto;
eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto; subst;
cleanup; eauto.
eapply free_all_blocks_finished_not_crashed.
eauto.
4: eauto.
all: eauto.
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H; eauto.
    cleanup; split_ors; cleanup.
    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H4; eauto.
    cleanup; split_ors; cleanup.

    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
}
{
    repeat rewrite <- app_assoc in H0; eauto;
    eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto; subst;
    cleanup; eauto.
    eapply free_all_blocks_finished_oracle_eq in H3; eauto.
    cleanup.
    eapply Inode.free_finished_not_crashed; eauto.
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H4; eauto.
    cleanup; split_ors; cleanup.
    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H; eauto.
    cleanup; split_ors; cleanup.

    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
}

{
    repeat rewrite <- app_assoc in H0; eauto;
    eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto; subst;
    cleanup; eauto.
    eapply free_all_blocks_finished_oracle_eq in H3; eauto.
    cleanup.
    intuition congruence.
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H4; eauto.
    cleanup; split_ors; cleanup.
    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H; eauto.
    cleanup; split_ors; cleanup.

    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
}
{
    repeat rewrite <- app_assoc in H0; eauto;
eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto; subst;
cleanup; eauto.
eapply free_all_blocks_finished_not_crashed.
eauto.
4: eauto.
all: eauto.
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H; eauto.
    cleanup; split_ors; cleanup.
    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H4; eauto.
    cleanup; split_ors; cleanup.

    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
}
{
    repeat rewrite <- app_assoc in H0; eauto;
eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto; subst;
cleanup; eauto.
eapply free_all_blocks_finished_oracle_eq in H3; eauto; cleanup.
intuition congruence.
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H4; eauto.
    cleanup; split_ors; cleanup.
    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H; eauto.
    cleanup; split_ors; cleanup.

    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
}
{
    repeat rewrite <- app_assoc in H0; eauto;
eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto; subst;
cleanup; eauto.
eapply free_all_blocks_finished_oracle_eq in H3; eauto; cleanup.
simpl in *; cleanup.
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H4; eauto.
    cleanup; split_ors; cleanup.
    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
    {
    unfold files_inner_rep in *; cleanup.
    eapply Inode.get_all_block_numbers_finished in H; eauto.
    cleanup; split_ors; cleanup.

    eapply all_block_numbers_in_bound. 
    4: eauto.
    3: eauto.
    2: eauto.
    eauto.
    }
}
{
    repeat rewrite <- app_assoc in H0; eauto;
eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H; eauto; subst;
cleanup; eauto.
simpl in *; cleanup.
}
Unshelve.
all: eauto.
repeat econstructor.
Qed.

Lemma map_app_ext:
forall T T' (f: T -> T') (l1 l2: list T) l3 l4,
map f l1 ++ l3 = map f l2 ++ l4 ->
(forall t1 t2, f t1 = f t2 -> t1 = t2) ->
exists l3' l4', l1 ++ l3' = l2 ++ l4'.
Proof.
    induction l1; simpl; intros; eauto.
    destruct l2; simpl in *; eauto.
    cleanup.
    erewrite H0 with (t1:= a)(t2:=t); eauto.
    edestruct IHl1; eauto.
    destruct H; eauto.
    do 2 eexists; eauto.
    rewrite H; eauto.
    Unshelve.
    all: eauto.
Qed.

Ltac solve_bounds:=
match goal with
|[H: forall _: nat , _ -> ?x _ = _ |- ?x _ = _ ] =>
    pose proof FSParameters.inodes_before_data;
    rewrite H;
    unfold DiskAllocatorParams.bitmap_addr,
    DiskAllocatorParams.num_of_blocks,
    Inode.InodeAllocatorParams.bitmap_addr,
    Inode.InodeAllocatorParams.num_of_blocks in *;
    try lia; eauto
end. 


Ltac solve_write :=
    repeat apply_specs; 
simpl in *; cleanup;
unfold refines, files_rep, files_crash_rep, files_inner_rep in *; 
repeat cleanup_pairs; repeat unify_invariants;
repeat match goal with
| [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
eapply FileInnerSpecs.write_inner_crashed in H;
[|
   unfold files_inner_rep in *; cleanup;
simpl; eexists; repeat (split; eauto);
simpl; eexists; split; eauto;
eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
intros; solve_bounds]
| [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
eapply FileInnerSpecs.write_inner_finished in H;
[|
   unfold files_inner_rep in *; cleanup;
simpl; eexists; repeat (split; eauto);
simpl; eexists; split; eauto;
eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
intros; solve_bounds]
end;
repeat cleanup_pairs; repeat unify_invariants;
repeat split_ors; cleanup;
unfold files_inner_rep in *; cleanup;
repeat cleanup_pairs; repeat unify_invariants;
match goal with
   | [H: Mem.upd ?m _ _ = ?m,
   H0: ?m _ = Some ?x3 |- _] =>
   apply upd_nop_rev in H;
   rewrite H0 in H; inversion H;
   unfold update_file in *; 
   destruct x3; simpl in *
   end;
match goal with 
[H: {| owner := ?owner; blocks := ?blocks |} =
{| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
inversion H
end;
exfalso; eapply list_extend_ne; eauto.   





    Ltac solve_extend :=
        repeat apply_specs; 
   simpl in *; cleanup;
   unfold refines, files_rep, files_crash_rep, files_inner_rep in *; 
   repeat cleanup_pairs; repeat unify_invariants;
   repeat match goal with
   | [H: exec (TransactionalDiskLang _) _ _ _ (extend_inner _ _) (Crashed _) |-_] =>
   eapply FileInnerSpecs.extend_inner_crashed in H;
   [|
       unfold files_inner_rep in *; cleanup;
    simpl; eexists; repeat (split; eauto);
    simpl; eexists; split; eauto;
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
 intros; solve_bounds]
 | [H: exec (TransactionalDiskLang _) _ _ _ (extend_inner _ _) (Finished _ _) |-_] =>
   eapply FileInnerSpecs.extend_inner_finished in H;
   [|
       unfold files_inner_rep in *; cleanup;
    simpl; eexists; repeat (split; eauto);
    simpl; eexists; split; eauto;
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
 intros; solve_bounds]
   end;
 repeat cleanup_pairs; repeat unify_invariants;
 repeat split_ors; cleanup;
 unfold files_inner_rep in *; cleanup;
 repeat cleanup_pairs; repeat unify_invariants;
   match goal with
       | [H: Mem.upd ?m _ _ = ?m,
       H0: ?m _ = Some ?x3 |- _] =>
       apply upd_nop_rev in H;
       rewrite H0 in H; inversion H;
       unfold extend_file in *; 
       destruct x3; simpl in *
       end;
   match goal with 
   [H: {| owner := ?owner; blocks := ?blocks |} =
   {| owner := ?owner; blocks := ?blocks ++ [_] |} |-_] =>
   inversion H
   end;
   exfalso; eapply list_extend_ne; eauto.   



   Ltac solve_change_owner :=
    repeat apply_specs; 
simpl in *; cleanup;
unfold refines, files_rep, files_crash_rep, files_inner_rep in *; 
repeat cleanup_pairs; repeat unify_invariants;
repeat match goal with
| [H: exec (TransactionalDiskLang _) _ _ _ (change_owner_inner _ _) (Crashed _) |-_] =>
eapply FileInnerSpecs.change_owner_inner_crashed in H;
[|
   unfold files_inner_rep in *; cleanup;
simpl; eexists; repeat (split; eauto);
simpl; eexists; split; eauto;
eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
intros; solve_bounds]
| [H: exec (TransactionalDiskLang _) _ _ _ (change_owner_inner _ _) (Finished _ _) |-_] =>
eapply FileInnerSpecs.change_owner_inner_finished in H;
[|
   unfold files_inner_rep in *; cleanup;
simpl; eexists; repeat (split; eauto);
simpl; eexists; split; eauto;
eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
intros; solve_bounds]
end;
repeat cleanup_pairs; repeat unify_invariants;
repeat split_ors; cleanup;
unfold files_inner_rep in *; cleanup;
repeat cleanup_pairs; repeat unify_invariants;
match goal with
   | [H: Mem.upd ?m _ _ = ?m,
   H0: ?m _ = Some ?x3 |- _] =>
   apply upd_nop_rev in H;
   rewrite H0 in H; inversion H;
   unfold change_file_owner in *; 
   destruct x3; simpl in *
   end;
match goal with 
[H: {| owner := _; blocks := ?blocks |} =
{| owner := _; blocks := ?blocks |} |-_] =>
inversion H; congruence
end.   


Ltac solve_delete :=
    repeat apply_specs; 
simpl in *; cleanup;
unfold refines, files_rep, files_crash_rep, files_inner_rep in *; 
repeat cleanup_pairs; repeat unify_invariants;
repeat match goal with
| [H: exec (TransactionalDiskLang _) _ _ _ (delete_inner _) (Crashed _) |-_] =>
eapply FileInnerSpecs.delete_inner_crashed in H;
[|
   unfold files_inner_rep in *; cleanup;
simpl; eexists; repeat (split; eauto);
simpl; eexists; split; eauto;
eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
intros; solve_bounds]
| [H: exec (TransactionalDiskLang _) _ _ _ (delete_inner _) (Finished _ _) |-_] =>
eapply FileInnerSpecs.delete_inner_finished in H;
[|
   unfold files_inner_rep in *; cleanup;
simpl; eexists; repeat (split; eauto);
simpl; eexists; split; eauto;
eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
intros; solve_bounds]
end;
repeat cleanup_pairs; repeat unify_invariants;
repeat split_ors; cleanup;
unfold files_inner_rep in *; cleanup;
repeat cleanup_pairs; repeat unify_invariants;
match goal with
   | [H: Mem.delete ?m _ = ?m,
   H0: ?m _ = Some ?x3 |- _] =>
   rewrite <- H in H0; 
   rewrite Mem.delete_eq in H0; eauto;
   congruence
   end.   


   Ltac solve_create :=
    repeat apply_specs; 
simpl in *; cleanup;
unfold refines, files_rep, files_crash_rep, files_inner_rep in *; 
repeat cleanup_pairs; repeat unify_invariants;
match goal with
   | [H: Mem.upd ?m ?inum _ = ?m,
   H0: ?m ?inum = None |- _] =>
   rewrite <- H in H0;
   rewrite Mem.upd_eq in H0; eauto; congruence
end.  

   Ltac invert_exec' :=
    match goal with
    |[H : recovery_exec _ _ _ _ _ _ _ _ |- _ ] =>
     invert_exec'' H
    | [ H: exec _ _ _ _ ?p _ |- _ ] =>
      match p with
      | Bind _ _ => fail
      | Op _ _ => invert_exec'' H
      | Ret _ => invert_exec'' H
      end
    | [ H: Language.exec' _ _ _ ?p _ |- _ ] =>
      match p with
      | Bind _ _ => fail
      | Op _ _ => invert_exec'' H
      | Ret _ => invert_exec'' H
      end
    | [ H: exec _ _ _ _ (lift_L1 _ _) (Finished _ _) |- _ ] =>
      eapply Automation.lift1_invert_exec in H; logic_clean
    | [ H: exec _ _ _ _ (lift_L2 _ _) (Finished _ _) |- _ ] =>
      eapply Automation.lift2_invert_exec in H; logic_clean
    | [ H: exec _ _ _ _ (lift_L1 _ _) (Crashed _) |- _ ] =>
      eapply Automation.lift1_invert_exec_crashed in H; logic_clean
    | [ H: exec _ _ _ _ (lift_L2 _ _) (Crashed _) |- _ ] =>
      eapply Automation.lift2_invert_exec_crashed in H; logic_clean
    | [ H: Language.exec' _ _ _ (lift_L1 _ _) (Finished _ _) |- _ ] =>
      eapply Automation.lift1_invert_exec in H; logic_clean
    | [ H: Language.exec' _ _ _ (lift_L2 _ _) (Finished _ _) |- _ ] =>
      eapply Automation.lift2_invert_exec in H; logic_clean
    | [ H: Language.exec' _ _ _ (lift_L1 _ _) (Crashed _) |- _ ] =>
      eapply Automation.lift1_invert_exec_crashed in H; logic_clean
    | [ H: Language.exec' _ _ _ (lift_L2 _ _) (Crashed _) |- _ ] =>
      eapply Automation.lift2_invert_exec_crashed in H; logic_clean
    | [H: Language.exec' _ _ _ (Op _ (P1 _)) _ |- _ ]=>
        invert_exec'' H
    | [H: Language.exec' _ _ _ (Op _ (P2 _)) _ |- _ ]=>
        invert_exec'' H
    | [ H: HorizontalComposition.exec' _ _ _ _ _ |- _ ] =>
      invert_exec'' H
    | [ H: Core.exec _ _ _ _ _ _ |- _ ] =>
      invert_exec'' H
    end.

    Ltac depth_first_crash_solve := 
    match goal with
    | [H: exec _ _ _ _ (Bind _ _) _,
    H0: exec _ _ _ _ (Bind _ _) _ |- _] =>
    invert_exec'' H; invert_exec'' H0
    | [H: Language.exec' _ _ _ (Bind _ _) _,
    H0: Language.exec' _ _ _ (Bind _ _) _ |- _] =>
    invert_exec'' H; invert_exec'' H0
    end; repeat split_crash; cleanup; simpl in *; repeat invert_exec'; 
    repeat invert_exec_local; repeat unify_invariants; solve_ret_iff_goal.

Lemma extend_crashed_exfalso:
    forall u' ex x x0 s1 s2 x3 inum v v' x2 sr2 o,
     same_for_user_except u' ex x x0 ->
   refines s1 x ->
    refines s2 x0 ->
   exec Definitions.impl (owner x3) o s1 (extend inum v) (Crashed x2) ->
   inum < FSParameters.inode_count ->
   x inum = Some x3 ->
   files_crash_rep (Mem.upd x inum (extend_file x3 v)) x2 ->
   exec Definitions.impl (owner x3) o s2 (extend inum v') (Crashed sr2) ->
   files_crash_rep x0 sr2 ->
   False.
   Proof. 
   intros;
    unfold refines, files_rep, files_inner_rep in *; cleanup.
    unfold extend, auth_then_exec in *.
   
    depth_first_crash_solve; try solve [solve_extend].
   
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H15; eauto;
       cleanup; subst.
   
       depth_first_crash_solve; try solve [ solve_extend ].
       depth_first_crash_solve; try solve [ solve_extend ].
   
       {
        cleanup.
        repeat rewrite <- app_assoc in H2.
        eapply_fresh map_app_ext in H2.
        logic_clean.
       eapply_fresh extend_inner_finished_oracle_eq in H20; eauto;
       cleanup; subst.
       depth_first_crash_solve; try solve [ solve_extend ].
       symmetry; eauto.
       intros; cleanup; congruence.
       }
       {
           cleanup.
           repeat rewrite <- app_assoc in H2.
           eapply_fresh map_app_ext in H2.
           logic_clean.
           eapply_fresh extend_inner_finished_oracle_eq in H20; eauto;
           cleanup; subst.
           intuition congruence.
           intros; cleanup; congruence.
       }
       {
           cleanup.
           repeat rewrite <- app_assoc in H2.
           eapply_fresh map_app_ext in H2.
           logic_clean.
           eapply_fresh extend_inner_finished_oracle_eq in H20; eauto;
           cleanup; subst.
           intuition congruence.
           intros; cleanup; congruence.
       }
       {
           cleanup.
           repeat rewrite <- app_assoc in H2.
           eapply_fresh map_app_ext in H2.
           logic_clean.
           eapply_fresh extend_inner_finished_oracle_eq in H20; eauto;
           cleanup; subst.
           depth_first_crash_solve; try solve [ solve_extend ].
           intros; cleanup; congruence.
       }
       {
            cleanup.
            repeat rewrite <- app_assoc in H2.
            eapply_fresh map_app_ext in H2.
            logic_clean.
            symmetry in H6.
           eapply extend_inner_finished_not_crashed; eauto.
           intros; cleanup; congruence.
       }
       {
            cleanup.
            repeat rewrite <- app_assoc in H2.
            eapply_fresh map_app_ext in H2.
            logic_clean.
            symmetry in H6.
        eapply extend_inner_finished_not_crashed; eauto.
        intros; cleanup; congruence.
       }
       depth_first_crash_solve; try solve [ solve_extend ].
       depth_first_crash_solve; try solve [ solve_extend ].
       {
         Transparent extend_inner.
             unfold extend_inner, DiskAllocator.alloc in *;
            repeat invert_exec; simpl in *; cleanup.
       }
       {
            unfold extend_inner, DiskAllocator.alloc in *;
            repeat invert_exec; simpl in *; cleanup.
       }
       {
        unfold extend_inner, DiskAllocator.alloc in *;
            repeat invert_exec; simpl in *; cleanup.
       }
       {
        unfold extend_inner, DiskAllocator.alloc in *;
            repeat invert_exec; simpl in *; cleanup.
            Opaque extend_inner.
       }
       depth_first_crash_solve; try solve [ solve_extend ].
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H15; eauto;
       cleanup; subst.
       intuition congruence.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H15; eauto;
       cleanup; subst.
       intuition congruence.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H15; eauto;
       cleanup; subst.
       depth_first_crash_solve; try solve [ solve_extend ].
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       exfalso; eapply Inode.get_owner_finished_not_crashed; [eauto| |eauto].
       symmetry; eauto.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       exfalso; eapply Inode.get_owner_finished_not_crashed; [eauto| |eauto].
       symmetry; eauto.
       intros; cleanup; congruence.
   }
   Unshelve.
   all: exact Definitions.impl.
   Qed.
   
   Lemma change_owner_crashed_exfalso:
    forall u' x x0 s1 s2 x3 inum v x2 sr2 o,
     same_for_user_except u' (Some inum) x x0 ->
   refines s1 x ->
    refines s2 x0 ->
   exec Definitions.impl (owner x3) o s1 (change_owner inum v) (Crashed x2) ->
   inum < FSParameters.inode_count ->
   x inum = Some x3 ->
   v<> owner x3 ->
   files_crash_rep (Mem.upd x inum (change_file_owner x3 v)) x2 ->
   exec Definitions.impl (owner x3) o s2 (change_owner inum v) (Crashed sr2) ->
   files_crash_rep x0 sr2 ->
   False.
   Proof. 
   intros;
    unfold refines, files_rep, files_inner_rep in *; cleanup.
    unfold change_owner, auth_then_exec in *.
   
    depth_first_crash_solve; try solve [solve_change_owner].
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H16; eauto;
       cleanup; subst.
   
       depth_first_crash_solve; try solve [ solve_change_owner ].
       depth_first_crash_solve; try solve [ solve_change_owner ].
   
       {
        cleanup.
        repeat rewrite <- app_assoc in H2.
        eapply_fresh map_app_ext in H2.
        logic_clean.
       eapply_fresh change_owner_inner_finished_oracle_eq in H21; eauto;
       cleanup; subst.
       depth_first_crash_solve; try solve [ solve_change_owner ].
       {
           cleanup.
           unfold files_crash_rep, files_inner_rep in *; cleanup.
           repeat cleanup_pairs; repeat unify_invariants.
           repeat apply_specs; cleanup; eauto;
           repeat split_ors; cleanup.
           simpl in *; cleanup.
           repeat cleanup_pairs; repeat unify_invariants.
           repeat match goal with
            | [H: exec (TransactionalDiskLang _) _ _ _ (change_owner_inner _ _) (Crashed _) |-_] =>
            eapply FileInnerSpecs.change_owner_inner_crashed in H;
            [|
            unfold files_inner_rep in *; cleanup;
            simpl; eexists; repeat (split; eauto);
            simpl; eexists; split; eauto;
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
            intros; solve_bounds]
            | [H: exec (TransactionalDiskLang _) _ _ _ (change_owner_inner _ _) (Finished _ _) |-_] =>
            eapply FileInnerSpecs.change_owner_inner_finished in H;
            [|
            unfold files_inner_rep in *; cleanup;
            simpl; eexists; repeat (split; eauto);
            simpl; eexists; split; eauto;
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
            intros; solve_bounds]
            end;
           eauto; simpl in *; cleanup;
           repeat split_ors; cleanup.
           simpl in *; cleanup.
           unfold files_inner_rep in *; cleanup;
           repeat cleanup_pairs; repeat unify_invariants.
           match goal with
           | [H: Mem.upd ?m _ _ = ?m,
           H0: ?m _ = Some ?x3 |- _] =>
           apply upd_nop_rev in H;
           rewrite H0 in H; inversion H;
           unfold change_file_owner in *; 
           destruct x3; simpl in *
           end.
           inversion H6; subst; try congruence.
           unfold file_map_rep in H11; cleanup.
           eapply H7 in H0; eauto.
           unfold file_rep in H0; cleanup;
           simpl in *; congruence.
       }
       { 
           cleanup.
           unfold files_crash_rep, files_inner_rep in *; cleanup.
           repeat cleanup_pairs; repeat unify_invariants.
           repeat apply_specs; cleanup; eauto;
           repeat split_ors; cleanup.
           simpl in *; cleanup.
           repeat cleanup_pairs; repeat unify_invariants.
           repeat match goal with
            | [H: exec (TransactionalDiskLang _) _ _ _ (change_owner_inner _ _) (Crashed _) |-_] =>
            eapply FileInnerSpecs.change_owner_inner_crashed in H;
            [|
            unfold files_inner_rep in *; cleanup;
            simpl; eexists; repeat (split; eauto);
            simpl; eexists; split; eauto;
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
            intros; solve_bounds]
            | [H: exec (TransactionalDiskLang _) _ _ _ (change_owner_inner _ _) (Finished _ _) |-_] =>
            eapply FileInnerSpecs.change_owner_inner_finished in H;
            [|
            unfold files_inner_rep in *; cleanup;
            simpl; eexists; repeat (split; eauto);
            simpl; eexists; split; eauto;
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
            intros; solve_bounds]
            end;
           eauto; simpl in *; cleanup;
           repeat split_ors; cleanup.
           simpl in *; cleanup.
           unfold files_inner_rep in *; cleanup;
           repeat cleanup_pairs; repeat unify_invariants.
           match goal with
           | [H: Mem.upd ?m _ _ = ?m,
           H0: ?m _ = Some ?x3 |- _] =>
           apply upd_nop_rev in H;
           rewrite H0 in H; inversion H;
           unfold change_file_owner in *; 
           destruct x3; simpl in *
           end.
           inversion H6; subst; try congruence.
           unfold file_map_rep in H11; cleanup.
           eapply H7 in H0; eauto.
           unfold file_rep in H0; cleanup;
           simpl in *; congruence.
       }
           intros; cleanup; congruence.
       }
       {
           cleanup.
           repeat rewrite <- app_assoc in H2.
           eapply_fresh map_app_ext in H2.
           logic_clean.
           eapply_fresh change_owner_inner_finished_oracle_eq in H21; eauto;
           cleanup; subst.
           intuition congruence.
           intros; cleanup; congruence.
       }
       {
           cleanup.
           repeat rewrite <- app_assoc in H2.
           eapply_fresh map_app_ext in H2.
           logic_clean.
           eapply_fresh change_owner_inner_finished_oracle_eq in H21; eauto;
           cleanup; subst.
           intuition congruence.
           intros; cleanup; congruence.
       }
       {
           cleanup.
           repeat rewrite <- app_assoc in H2.
           eapply_fresh map_app_ext in H2.
           logic_clean.
           eapply_fresh change_owner_inner_finished_oracle_eq in H21; eauto;
           cleanup; subst.
           depth_first_crash_solve; try solve [ solve_change_owner ].
           intros; cleanup; congruence.
       }
       {
            cleanup.
            repeat rewrite <- app_assoc in H2.
            eapply_fresh map_app_ext in H2.
            logic_clean.
            symmetry in H7.
           eapply change_owner_inner_finished_not_crashed; eauto.
           intros; cleanup; congruence.
       }
       {
            cleanup.
            repeat rewrite <- app_assoc in H2.
            eapply_fresh map_app_ext in H2.
            logic_clean.
            symmetry in H7.
        eapply change_owner_inner_finished_not_crashed; eauto.
        intros; cleanup; congruence.
       }
       depth_first_crash_solve; try solve [ solve_change_owner ].
       depth_first_crash_solve; try solve [ solve_change_owner ].
       {
         Transparent change_owner_inner Inode.change_owner.
             unfold change_owner_inner, Inode.change_owner, 
             Inode.get_inode, Inode.InodeAllocator.read in *.
            repeat invert_exec; simpl in *; cleanup.
       }
       {
        unfold change_owner_inner, Inode.change_owner, 
        Inode.get_inode, Inode.InodeAllocator.read in *.
       repeat invert_exec; simpl in *; cleanup.
       }
       {
        unfold change_owner_inner, Inode.change_owner, 
             Inode.get_inode, Inode.InodeAllocator.read in *.
            repeat invert_exec; simpl in *; cleanup.
       }
       {
        unfold change_owner_inner, Inode.change_owner, 
             Inode.get_inode, Inode.InodeAllocator.read in *.
            repeat invert_exec; simpl in *; cleanup.
            Opaque change_owner_inner Inode.change_owner.
       }
       depth_first_crash_solve; try solve [ solve_change_owner ].
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H16; eauto;
       cleanup; subst.
       intuition congruence.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H16; eauto;
       cleanup; subst.
       intuition congruence.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H16; eauto;
       cleanup; subst.
       depth_first_crash_solve; try solve [ solve_change_owner ].
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       exfalso; eapply Inode.get_owner_finished_not_crashed; 
       [eauto| |eauto].
       symmetry; eauto.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       exfalso; eapply Inode.get_owner_finished_not_crashed; 
       [eauto| |eauto].
       symmetry; eauto.
       intros; cleanup; congruence.
   }
   Unshelve.
   all: exact Definitions.impl.
   Qed.


   Opaque write_inner.
   Lemma write_crashed_exfalso:
   forall u' ex x x0 s1 s2 x3  f2 inum off v v' x2 sr2 o,
    same_for_user_except u' ex x x0 ->
  refines s1 x ->
   refines s2 x0 ->
  exec Definitions.impl (owner x3) o s1 (write inum off v) (Crashed x2) ->
  inum < FSParameters.inode_count ->
  x inum = Some x3 ->
  off < length (blocks x3) ->
  seln (blocks x3) off value0 <> v ->
  x0 inum = Some f2 ->
  seln (blocks f2) off value0 <> v' ->
  files_crash_rep (Mem.upd x inum (update_file x3 off v)) x2 ->
  exec Definitions.impl (owner x3) o s2 (write inum off v') (Crashed sr2) ->
  files_crash_rep x0 sr2 ->
  False.
  Proof. 
  intros;
   unfold refines, files_rep, files_inner_rep in *; cleanup.
   unfold write, auth_then_exec in *.
  
   depth_first_crash_solve; try solve [solve_write].
  {
      cleanup.
      repeat rewrite <- app_assoc in H2.
      eapply_fresh map_app_ext in H2.
      logic_clean.
      eapply_fresh Inode.get_owner_finished_oracle_eq in H19; eauto;
      cleanup; subst.
  
      depth_first_crash_solve; try solve [ solve_write ].
      depth_first_crash_solve; try solve [ solve_write ].
      {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
      eapply_fresh write_inner_finished_oracle_eq in H24; eauto;
      cleanup; subst.
      depth_first_crash_solve; try solve [ solve_write ].
      {
          cleanup.
          unfold files_crash_rep, files_inner_rep in *; cleanup.
          repeat cleanup_pairs; repeat unify_invariants.
          repeat apply_specs; cleanup; eauto;
          repeat split_ors; cleanup.
          simpl in *; cleanup.
          repeat cleanup_pairs; repeat unify_invariants.
          repeat match goal with
           | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
           eapply FileInnerSpecs.write_inner_crashed in H;
           [|
           unfold files_inner_rep in *; cleanup;
           simpl; eexists; repeat (split; eauto);
           simpl; eexists; split; eauto;
           eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
           intros; solve_bounds]
           | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
           eapply FileInnerSpecs.write_inner_finished in H;
           [|
           unfold files_inner_rep in *; cleanup;
           simpl; eexists; repeat (split; eauto);
           simpl; eexists; split; eauto;
           eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
           intros; solve_bounds]
           end;
          eauto; simpl in *; cleanup;
          repeat split_ors; cleanup.
          simpl in *; cleanup.
          unfold files_inner_rep in *; cleanup;
          repeat cleanup_pairs; repeat unify_invariants.
          match goal with
          | [H: Mem.upd ?m _ _ = ?m,
          H0: ?m _ = Some ?x3 |- _] =>
          apply upd_nop_rev in H;
          rewrite H0 in H; inversion H;
          unfold update_file in *; 
          destruct x3; simpl in *
          end.
          match goal with 
            [H: {| owner := ?owner; blocks := ?blocks |} =
            {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
            inversion H
          end.
          match goal with 
            [H: ?l = updn ?l _ _ |-_] =>
          symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
          end. 
      }
      {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat match goal with
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
         eapply FileInnerSpecs.write_inner_crashed in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
         eapply FileInnerSpecs.write_inner_finished in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         end;
        eauto; simpl in *; cleanup;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        unfold files_inner_rep in *; cleanup;
        repeat cleanup_pairs; repeat unify_invariants.
        match goal with
        | [H: Mem.upd ?m _ _ = ?m,
        H0: ?m _ = Some ?x3 |- _] =>
        apply upd_nop_rev in H;
        rewrite H0 in H; inversion H;
        unfold update_file in *; 
        destruct x3; simpl in *
        end.
        match goal with 
          [H: {| owner := ?owner; blocks := ?blocks |} =
          {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
          inversion H
        end.
        match goal with 
          [H: ?l = updn ?l _ _ |-_] =>
        symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
        end. 
      }
      {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat match goal with
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
         eapply FileInnerSpecs.write_inner_crashed in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
         eapply FileInnerSpecs.write_inner_finished in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         end;
        eauto; simpl in *; cleanup;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        unfold files_inner_rep in *; cleanup;
        repeat cleanup_pairs; repeat unify_invariants.
        match goal with
        | [H: Mem.upd ?m _ _ = ?m,
        H0: ?m _ = Some ?x3 |- _] =>
        apply upd_nop_rev in H;
        rewrite H0 in H; inversion H;
        unfold update_file in *; 
        destruct x3; simpl in *
        end.
        match goal with 
          [H: {| owner := ?owner; blocks := ?blocks |} =
          {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
          inversion H
        end.
        match goal with 
          [H: ?l = updn ?l _ _ |-_] =>
        symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
        end. 
      }
      
  {
    repeat cleanup_pairs;
      eapply_fresh Inode.get_owner_finished in H22; eauto.
      cleanup; subst.
      repeat cleanup_pairs;
       unfold files_crash_rep, files_inner_rep in *;
      cleanup; repeat unify_invariants; eauto.
      eexists; split; eauto.
      eexists; split; eauto.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; repeat solve_bounds.
  }
  {
    repeat cleanup_pairs;
      eapply_fresh Inode.get_owner_finished in H19; eauto.
      cleanup; subst.
      repeat cleanup_pairs;
       unfold files_crash_rep, files_inner_rep in *;
      cleanup; repeat unify_invariants; eauto.
      eexists; split; eauto.
      eexists; split; eauto.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; repeat solve_bounds.
  }
  intros; cleanup; congruence.
}
{
           cleanup.
           repeat rewrite <- app_assoc in H2.
           eapply_fresh map_app_ext in H2.
           logic_clean.
           eapply_fresh write_inner_finished_oracle_eq in H24; eauto;
           cleanup; subst.
           intuition congruence.
           {
                repeat cleanup_pairs;
                eapply_fresh Inode.get_owner_finished in H22; eauto.
                cleanup; subst.
                repeat cleanup_pairs;
                unfold files_crash_rep, files_inner_rep in *;
                cleanup; repeat unify_invariants; eauto.
                eexists; split; eauto.
                eexists; split; eauto.
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
                intros; repeat solve_bounds.
            }
            {
                repeat cleanup_pairs;
                eapply_fresh Inode.get_owner_finished in H19; eauto.
                cleanup; subst.
                repeat cleanup_pairs;
                unfold files_crash_rep, files_inner_rep in *;
                cleanup; repeat unify_invariants; eauto.
                eexists; split; eauto.
                eexists; split; eauto.
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
                intros; repeat solve_bounds.
            }
           intros; cleanup; congruence.
       }
       {
           cleanup.
           repeat rewrite <- app_assoc in H2.
           eapply_fresh map_app_ext in H2.
           logic_clean.
           eapply_fresh write_inner_finished_oracle_eq in H24; eauto;
           cleanup; subst.
           intuition congruence.
           {
                repeat cleanup_pairs;
                eapply_fresh Inode.get_owner_finished in H22; eauto.
                cleanup; subst.
                repeat cleanup_pairs;
                unfold files_crash_rep, files_inner_rep in *;
                cleanup; repeat unify_invariants; eauto.
                eexists; split; eauto.
                eexists; split; eauto.
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
                intros; repeat solve_bounds.
            }
            {
                repeat cleanup_pairs;
                eapply_fresh Inode.get_owner_finished in H19; eauto.
                cleanup; subst.
                repeat cleanup_pairs;
                unfold files_crash_rep, files_inner_rep in *;
                cleanup; repeat unify_invariants; eauto.
                eexists; split; eauto.
                eexists; split; eauto.
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
                intros; repeat solve_bounds.
            }
           intros; cleanup; congruence.
       }
        {
            depth_first_crash_solve; try solve [ solve_delete ].
            {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat match goal with
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
         eapply FileInnerSpecs.write_inner_crashed in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
         eapply FileInnerSpecs.write_inner_finished in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
        end.
        eauto; simpl in *; cleanup;
        repeat split_ors; cleanup;
        simpl in *; cleanup;
        unfold files_inner_rep in *; cleanup;
        repeat cleanup_pairs; repeat unify_invariants;
        match goal with
        | [H: Mem.upd ?m _ _ = ?m,
        H0: ?m _ = Some ?x3 |- _] =>
        apply upd_nop_rev in H;
        rewrite H0 in H; inversion H;
        unfold update_file in *; 
        destruct x3; simpl in *
        end;
        match goal with 
          [H: {| owner := ?owner; blocks := ?blocks |} =
          {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
          inversion H
        end;
        match goal with 
          [H: ?l = updn ?l _ _ |-_] =>
        symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
        end. 
      }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh write_inner_finished_oracle_eq in H24; eauto;
       cleanup; subst.
       simpl in *; cleanup.
       {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H22; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H19; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh write_inner_finished_oracle_eq in H24; eauto;
       cleanup; subst.
       simpl in *; cleanup.
       {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H22; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H19; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        intros; cleanup; congruence.
   }
   {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat match goal with
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
         eapply FileInnerSpecs.write_inner_crashed in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
         eapply FileInnerSpecs.write_inner_finished in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
        end.
        eauto; simpl in *; cleanup;
        repeat split_ors; cleanup;
        simpl in *; cleanup;
        unfold files_inner_rep in *; cleanup;
        repeat cleanup_pairs; repeat unify_invariants;
        match goal with
        | [H: Mem.upd ?m _ _ = ?m,
        H0: ?m _ = Some ?x3 |- _] =>
        apply upd_nop_rev in H;
        rewrite H0 in H; inversion H;
        unfold update_file in *; 
        destruct x3; simpl in *
        end;
        match goal with 
          [H: {| owner := ?owner; blocks := ?blocks |} =
          {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
          inversion H
        end;
        match goal with 
          [H: ?l = updn ?l _ _ |-_] =>
        symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
        end. 
      }
    }
    {
        cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       symmetry in H10; eapply write_inner_finished_not_crashed; eauto. 
       {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H22; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H19; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        intros; cleanup; congruence.
    }
    {
        cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       symmetry in H10; eapply write_inner_finished_not_crashed; eauto. 
       {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H22; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H19; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        intros; cleanup; congruence.
    }
    {
        cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply write_inner_finished_not_crashed. 
       5: eapply same_for_user_except_symmetry; eauto.
       all: eauto. 
       {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H19; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; 
            simpl in *; repeat cleanup_pairs;
            repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H22; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        intros; cleanup; congruence.
    }
    {
        cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply write_inner_finished_not_crashed. 
       5: eapply same_for_user_except_symmetry; eauto.
       all: eauto. 
       {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H19; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; 
            simpl in *; repeat cleanup_pairs;
            repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        {
            repeat cleanup_pairs;
            eapply_fresh Inode.get_owner_finished in H22; eauto.
            cleanup; subst.
            repeat cleanup_pairs;
            unfold files_crash_rep, files_inner_rep in *;
            cleanup; repeat unify_invariants; eauto.
            eexists; split; eauto.
            eexists; split; eauto.
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
            intros; repeat solve_bounds.
        }
        intros; cleanup; congruence.
    }
    {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat match goal with
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
         eapply FileInnerSpecs.write_inner_crashed in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
         eapply FileInnerSpecs.write_inner_finished in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
        end.
        eauto; simpl in *; cleanup;
        repeat split_ors; cleanup;
        simpl in *; cleanup;
        unfold files_inner_rep in *; cleanup;
        repeat cleanup_pairs; repeat unify_invariants;
        match goal with
        | [H: Mem.upd ?m _ _ = ?m,
        H0: ?m _ = Some ?x3 |- _] =>
        apply upd_nop_rev in H;
        rewrite H0 in H; inversion H;
        unfold update_file in *; 
        destruct x3; simpl in *
        end;
        match goal with 
          [H: {| owner := ?owner; blocks := ?blocks |} =
          {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
          inversion H
        end;
        match goal with 
          [H: ?l = updn ?l _ _ |-_] =>
        symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
        end. 
    } 
    {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        unfold same_for_user_except in *; cleanup.
        eapply_fresh H19 in H4; eauto.
        cleanup.
        subst.
        unfold file_map_rep in *; cleanup.
        eapply_fresh H36 in H29; eauto.
        unfold file_rep in *; cleanup; congruence.
    }
    {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        unfold same_for_user_except in *; cleanup.
        eapply_fresh H19 in H4; eauto.
        cleanup.
        subst.
        unfold file_map_rep in *; cleanup.
        eapply_fresh H35 in H28; eauto.
        unfold file_rep in *; cleanup; congruence.
    }
    {
        depth_first_crash_solve; try solve [ solve_write ].
        {
            cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat match goal with
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
         eapply FileInnerSpecs.write_inner_crashed in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
         eapply FileInnerSpecs.write_inner_finished in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
        end.
        eauto; simpl in *; cleanup;
        repeat split_ors; cleanup;
        simpl in *; cleanup;
        unfold files_inner_rep in *; cleanup;
        repeat cleanup_pairs; repeat unify_invariants;
        match goal with
        | [H: Mem.upd ?m _ _ = ?m,
        H0: ?m _ = Some ?x3 |- _] =>
        apply upd_nop_rev in H;
        rewrite H0 in H; inversion H;
        unfold update_file in *; 
        destruct x3; simpl in *
        end;
        match goal with 
          [H: {| owner := ?owner; blocks := ?blocks |} =
          {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
          inversion H
        end;
        match goal with 
          [H: ?l = updn ?l _ _ |-_] =>
        symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
        end. 
        }
        {
            cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat match goal with
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
         eapply FileInnerSpecs.write_inner_crashed in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
         eapply FileInnerSpecs.write_inner_finished in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
        end.
        eauto; simpl in *; cleanup;
        repeat split_ors; cleanup;
        simpl in *; cleanup;
        unfold files_inner_rep in *; cleanup;
        repeat cleanup_pairs; repeat unify_invariants;
        match goal with
        | [H: Mem.upd ?m _ _ = ?m,
        H0: ?m _ = Some ?x3 |- _] =>
        apply upd_nop_rev in H;
        rewrite H0 in H; inversion H;
        unfold update_file in *; 
        destruct x3; simpl in *
        end;
        match goal with 
          [H: {| owner := ?owner; blocks := ?blocks |} =
          {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
          inversion H
        end;
        match goal with 
          [H: ?l = updn ?l _ _ |-_] =>
        symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
        end. 
        }
    }
    {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat match goal with
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
         eapply FileInnerSpecs.write_inner_crashed in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
         eapply FileInnerSpecs.write_inner_finished in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
        end.
        eauto; simpl in *; cleanup;
        repeat split_ors; cleanup;
        simpl in *; cleanup;
        unfold files_inner_rep in *; cleanup;
        repeat cleanup_pairs; repeat unify_invariants;
        match goal with
        | [H: Mem.upd ?m _ _ = ?m,
        H0: ?m _ = Some ?x3 |- _] =>
        apply upd_nop_rev in H;
        rewrite H0 in H; inversion H;
        unfold update_file in *; 
        destruct x3; simpl in *
        end;
        match goal with 
          [H: {| owner := ?owner; blocks := ?blocks |} =
          {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
          inversion H
        end;
        match goal with 
          [H: ?l = updn ?l _ _ |-_] =>
        symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
        end. 
    }
    intros; cleanup; congruence.
  }
    {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H19; eauto;
       cleanup; subst.
       intuition congruence.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H19; eauto;
       cleanup; subst.
       intuition congruence.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H19; eauto;
       cleanup; subst.
       depth_first_crash_solve; try solve [ solve_write ].
       {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat match goal with
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
         eapply FileInnerSpecs.write_inner_crashed in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
         eapply FileInnerSpecs.write_inner_finished in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
        end.
        eauto; simpl in *; cleanup;
        repeat split_ors; cleanup;
        simpl in *; cleanup;
        unfold files_inner_rep in *; cleanup;
        repeat cleanup_pairs; repeat unify_invariants;
        match goal with
        | [H: Mem.upd ?m _ _ = ?m,
        H0: ?m _ = Some ?x3 |- _] =>
        apply upd_nop_rev in H;
        rewrite H0 in H; inversion H;
        unfold update_file in *; 
        destruct x3; simpl in *
        end;
        match goal with 
          [H: {| owner := ?owner; blocks := ?blocks |} =
          {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
          inversion H
        end;
        match goal with 
          [H: ?l = updn ?l _ _ |-_] =>
        symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
        end. 
       }
       {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat match goal with
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
         eapply FileInnerSpecs.write_inner_crashed in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
         | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
         eapply FileInnerSpecs.write_inner_finished in H;
         [|
         unfold files_inner_rep in *; cleanup;
         simpl; eexists; repeat (split; eauto);
         simpl; eexists; split; eauto;
         eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
         intros; solve_bounds]
        end.
        eauto; simpl in *; cleanup;
        repeat split_ors; cleanup;
        simpl in *; cleanup;
        unfold files_inner_rep in *; cleanup;
        repeat cleanup_pairs; repeat unify_invariants;
        match goal with
        | [H: Mem.upd ?m _ _ = ?m,
        H0: ?m _ = Some ?x3 |- _] =>
        apply upd_nop_rev in H;
        rewrite H0 in H; inversion H;
        unfold update_file in *; 
        destruct x3; simpl in *
        end;
        match goal with 
          [H: {| owner := ?owner; blocks := ?blocks |} =
          {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
          inversion H
        end;
        match goal with 
          [H: ?l = updn ?l _ _ |-_] =>
        symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
        end. 
       }
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       exfalso; eapply Inode.get_owner_finished_not_crashed; 
       [eauto| |eauto].
       symmetry; eauto.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       exfalso; eapply Inode.get_owner_finished_not_crashed; 
       [eauto| |eauto].
       symmetry; eauto.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       exfalso; eapply Inode.get_owner_finished_not_crashed; 
       [eauto| |eauto].
       symmetry; eauto.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       exfalso; eapply Inode.get_owner_finished_not_crashed; 
       [eauto| |eauto].
       symmetry; eauto.
       intros; cleanup; congruence.
   }
   {
    cleanup.
    unfold files_crash_rep, files_inner_rep in *; cleanup.
    repeat cleanup_pairs; repeat unify_invariants.
    repeat apply_specs; cleanup; eauto;
    repeat split_ors; cleanup.
    simpl in *; cleanup.
    repeat cleanup_pairs; repeat unify_invariants.
    repeat match goal with
     | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Crashed _) |-_] =>
     eapply FileInnerSpecs.write_inner_crashed in H;
     [|
     unfold files_inner_rep in *; cleanup;
     simpl; eexists; repeat (split; eauto);
     simpl; eexists; split; eauto;
     eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
     intros; solve_bounds]
     | [H: exec (TransactionalDiskLang _) _ _ _ (write_inner _ _ _) (Finished _ _) |-_] =>
     eapply FileInnerSpecs.write_inner_finished in H;
     [|
     unfold files_inner_rep in *; cleanup;
     simpl; eexists; repeat (split; eauto);
     simpl; eexists; split; eauto;
     eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
     intros; solve_bounds]
    end.
    eauto; simpl in *; cleanup;
    repeat split_ors; cleanup;
    simpl in *; cleanup;
    unfold files_inner_rep in *; cleanup;
    repeat cleanup_pairs; repeat unify_invariants;
    match goal with
    | [H: Mem.upd ?m _ _ = ?m,
    H0: ?m _ = Some ?x3 |- _] =>
    apply upd_nop_rev in H;
    rewrite H0 in H; inversion H;
    unfold update_file in *; 
    destruct x3; simpl in *
    end;
    match goal with 
      [H: {| owner := ?owner; blocks := ?blocks |} =
      {| owner := ?owner; blocks := updn ?blocks _ _ |} |-_] =>
      inversion H
    end;
    match goal with 
      [H: ?l = updn ?l _ _ |-_] =>
    symmetry in H; eapply seln_eq_updn_eq_rev in H; eauto
    end. 
   }
Unshelve.
all: exact Definitions.impl.
Qed.

    Opaque delete_inner.
   Lemma delete_crashed_exfalso:
    forall u' ex x x0 s1 s2 x3 inum inum' x2 sr2 o,
     same_for_user_except u' ex x x0 ->
   refines s1 x ->
    refines s2 x0 ->
   exec Definitions.impl (owner x3) o s1 (delete inum) (Crashed x2) ->
   inum < FSParameters.inode_count ->
   x inum = Some x3 ->
   files_crash_rep (Mem.delete x inum) x2 ->
   exec Definitions.impl (owner x3) o s2 (delete inum') (Crashed sr2) ->
   files_crash_rep x0 sr2 ->
   False.
   Proof. 
   intros;
    unfold refines, files_rep, files_inner_rep in *; cleanup.
    unfold delete, auth_then_exec in *.
   
    depth_first_crash_solve; try solve [solve_delete].
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H15; eauto;
       cleanup; subst.
   
       depth_first_crash_solve; try solve [ solve_delete ].
       depth_first_crash_solve; try solve [ solve_delete ].
       {
        cleanup.
        repeat rewrite <- app_assoc in H2.
        eapply_fresh map_app_ext in H2.
        logic_clean.
       eapply_fresh delete_inner_finished_oracle_eq in H20; eauto;
       cleanup; subst.
       depth_first_crash_solve; try solve [ solve_delete ].
       {
           cleanup.
           unfold files_crash_rep, files_inner_rep in *; cleanup.
           repeat cleanup_pairs; repeat unify_invariants.
           repeat apply_specs; cleanup; eauto;
           repeat split_ors; cleanup.
           simpl in *; cleanup.
           repeat cleanup_pairs; repeat unify_invariants;
           repeat match goal with
            | [H: exec (TransactionalDiskLang _) _ _ _ (delete_inner _) (Crashed _) |-_] =>
            eapply FileInnerSpecs.delete_inner_crashed in H;
            [|
            unfold files_inner_rep in *; cleanup;
            simpl; eexists; repeat (split; eauto);
            simpl; eexists; split; eauto;
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
            intros; solve_bounds]
            | [H: exec (TransactionalDiskLang _) _ _ _ (delete_inner _) (Finished _ _) |-_] =>
            eapply FileInnerSpecs.delete_inner_finished in H;
            [|
            unfold files_inner_rep in *; cleanup;
            simpl; eexists; repeat (split; eauto);
            simpl; eexists; split; eauto;
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
            intros; solve_bounds]
            end;
           eauto; simpl in *; cleanup;
           repeat split_ors; cleanup.
           simpl in *; cleanup.
           unfold files_inner_rep in *; cleanup;
           repeat cleanup_pairs; repeat unify_invariants.
           eapply FileInnerSpecs.inode_exists_then_file_exists in H26; eauto.
           cleanup.
           match goal with
            | [H: Mem.delete ?m _ = ?m,
            H0: ?m _ = Some ?x3 |- _] =>
            rewrite <- H in H0; 
            rewrite Mem.delete_eq in H0; eauto;
            congruence
            end. 
       }
       {
           cleanup.
           unfold files_crash_rep, files_inner_rep in *; cleanup.
           repeat cleanup_pairs; repeat unify_invariants.
           repeat apply_specs; cleanup; eauto;
           repeat split_ors; cleanup.
           simpl in *; cleanup.
           repeat cleanup_pairs; repeat unify_invariants;
           repeat match goal with
            | [H: exec (TransactionalDiskLang _) _ _ _ (delete_inner _) (Crashed _) |-_] =>
            eapply FileInnerSpecs.delete_inner_crashed in H;
            [|
            unfold files_inner_rep in *; cleanup;
            simpl; eexists; repeat (split; eauto);
            simpl; eexists; split; eauto;
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
            intros; solve_bounds]
            | [H: exec (TransactionalDiskLang _) _ _ _ (delete_inner _) (Finished _ _) |-_] =>
            eapply FileInnerSpecs.delete_inner_finished in H;
            [|
            unfold files_inner_rep in *; cleanup;
            simpl; eexists; repeat (split; eauto);
            simpl; eexists; split; eauto;
            eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
            intros; solve_bounds]
            end;
           eauto; simpl in *; cleanup;
           repeat split_ors; cleanup.
           simpl in *; cleanup.
           unfold files_inner_rep in *; cleanup;
           repeat cleanup_pairs; repeat unify_invariants.
           eapply FileInnerSpecs.inode_exists_then_file_exists in H26; eauto.
           cleanup.
           match goal with
            | [H: Mem.delete ?m _ = ?m,
            H0: ?m _ = Some ?x3 |- _] =>
            rewrite <- H in H0; 
            rewrite Mem.delete_eq in H0; eauto;
            congruence
            end. 
       }
       {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
           simpl in *; repeat cleanup_pairs; repeat unify_invariants.

        eexists; unfold files_inner_rep in *; cleanup;
        simpl; eexists; repeat (split; eauto);
        simpl; eexists; split; eauto;
        eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
        intros; solve_bounds.
       }
       {
        cleanup.
        unfold files_crash_rep, files_inner_rep in *; cleanup.
        repeat cleanup_pairs; repeat unify_invariants.
        repeat apply_specs; cleanup; eauto;
        repeat split_ors; cleanup.
        simpl in *; cleanup.
           simpl in *; repeat cleanup_pairs; repeat unify_invariants.

        eexists; unfold files_inner_rep in *; cleanup;
        simpl; eexists; repeat (split; eauto);
        simpl; eexists; split; eauto;
        eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
        intros; solve_bounds.
       }
       intros; cleanup; congruence.
       }
       {
           cleanup.
           repeat rewrite <- app_assoc in H2.
           eapply_fresh map_app_ext in H2.
           logic_clean.
           eapply_fresh delete_inner_finished_oracle_eq in H20; eauto;
           cleanup; subst.
           intuition congruence.
           {
                cleanup.
                unfold files_crash_rep, files_inner_rep in *; cleanup.
                repeat cleanup_pairs; repeat unify_invariants.
                repeat apply_specs; cleanup; eauto;
                repeat split_ors; cleanup.
                simpl in *; cleanup.
                simpl in *; repeat cleanup_pairs; repeat unify_invariants.

                eexists; unfold files_inner_rep in *; cleanup;
                simpl; eexists; repeat (split; eauto);
                simpl; eexists; split; eauto;
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
                intros; solve_bounds.
            }
            {
                cleanup.
                unfold files_crash_rep, files_inner_rep in *; cleanup.
                repeat cleanup_pairs; repeat unify_invariants.
                repeat apply_specs; cleanup; eauto;
                repeat split_ors; cleanup.
                simpl in *; cleanup.
                simpl in *; repeat cleanup_pairs; repeat unify_invariants.

                eexists; unfold files_inner_rep in *; cleanup;
                simpl; eexists; repeat (split; eauto);
                simpl; eexists; split; eauto;
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
                intros; solve_bounds.
            }
           intros; cleanup; congruence.
       }
       {
           cleanup.
           repeat rewrite <- app_assoc in H2.
           eapply_fresh map_app_ext in H2.
           logic_clean.
           eapply_fresh delete_inner_finished_oracle_eq in H20; eauto;
           cleanup; subst.
           intuition congruence.
           {
                cleanup.
                unfold files_crash_rep, files_inner_rep in *; cleanup.
                repeat cleanup_pairs; repeat unify_invariants.
                repeat apply_specs; cleanup; eauto;
                repeat split_ors; cleanup.
                simpl in *; cleanup.
                simpl in *; repeat cleanup_pairs; repeat unify_invariants.

                eexists; unfold files_inner_rep in *; cleanup;
                simpl; eexists; repeat (split; eauto);
                simpl; eexists; split; eauto;
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
                intros; solve_bounds.
            }
            {
                cleanup.
                unfold files_crash_rep, files_inner_rep in *; cleanup.
                repeat cleanup_pairs; repeat unify_invariants.
                repeat apply_specs; cleanup; eauto;
                repeat split_ors; cleanup.
                simpl in *; cleanup.
                simpl in *; repeat cleanup_pairs; repeat unify_invariants.

                eexists; unfold files_inner_rep in *; cleanup;
                simpl; eexists; repeat (split; eauto);
                simpl; eexists; split; eauto;
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
                intros; solve_bounds.
            }
           intros; cleanup; congruence.
       }
       {
           cleanup.
           repeat rewrite <- app_assoc in H2.
           eapply_fresh map_app_ext in H2.
           logic_clean.
           eapply_fresh delete_inner_finished_oracle_eq in H20; eauto;
           cleanup; subst.
           depth_first_crash_solve; try solve [ solve_delete ].
           {
                cleanup.
                unfold files_crash_rep, files_inner_rep in *; cleanup.
                repeat cleanup_pairs; repeat unify_invariants.
                repeat apply_specs; cleanup; eauto;
                repeat split_ors; cleanup.
                simpl in *; cleanup.
                simpl in *; repeat cleanup_pairs; repeat unify_invariants.

                eexists; unfold files_inner_rep in *; cleanup;
                simpl; eexists; repeat (split; eauto);
                simpl; eexists; split; eauto;
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
                intros; solve_bounds.
            }
            {
                cleanup.
                unfold files_crash_rep, files_inner_rep in *; cleanup.
                repeat cleanup_pairs; repeat unify_invariants.
                repeat apply_specs; cleanup; eauto;
                repeat split_ors; cleanup.
                simpl in *; cleanup.
                simpl in *; repeat cleanup_pairs; repeat unify_invariants.

                eexists; unfold files_inner_rep in *; cleanup;
                simpl; eexists; repeat (split; eauto);
                simpl; eexists; split; eauto;
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
                intros; solve_bounds.
            }
           intros; cleanup; congruence.
       }
       {
            cleanup.
            repeat rewrite <- app_assoc in H2.
            eapply_fresh map_app_ext in H2.
            logic_clean.
            symmetry in H6.
           eapply delete_inner_finished_not_crashed; eauto.
           {
                cleanup.
                unfold files_crash_rep, files_inner_rep in *; cleanup.
                repeat cleanup_pairs; repeat unify_invariants.
                repeat apply_specs; cleanup; eauto;
                repeat split_ors; cleanup.
                simpl in *; cleanup.
                simpl in *; repeat cleanup_pairs; repeat unify_invariants.

                eexists; unfold files_inner_rep in *; cleanup;
                simpl; eexists; repeat (split; eauto);
                simpl; eexists; split; eauto;
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
                intros; solve_bounds.
            }
            {
                cleanup.
                unfold files_crash_rep, files_inner_rep in *; cleanup.
                repeat cleanup_pairs; repeat unify_invariants.
                repeat apply_specs; cleanup; eauto;
                repeat split_ors; cleanup.
                simpl in *; cleanup.
                simpl in *; repeat cleanup_pairs; repeat unify_invariants.

                eexists; unfold files_inner_rep in *; cleanup;
                simpl; eexists; repeat (split; eauto);
                simpl; eexists; split; eauto;
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
                intros; solve_bounds.
            }
           intros; cleanup; congruence.
       }
       {
            cleanup.
            repeat rewrite <- app_assoc in H2.
            eapply_fresh map_app_ext in H2.
            logic_clean.
            symmetry in H6.
            eapply delete_inner_finished_not_crashed; eauto.
            {
                cleanup.
                unfold files_crash_rep, files_inner_rep in *; cleanup.
                repeat cleanup_pairs; repeat unify_invariants.
                repeat apply_specs; cleanup; eauto;
                repeat split_ors; cleanup.
                simpl in *; cleanup.
                simpl in *; repeat cleanup_pairs; repeat unify_invariants.

                eexists; unfold files_inner_rep in *; cleanup;
                simpl; eexists; repeat (split; eauto);
                simpl; eexists; split; eauto;
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
                intros; solve_bounds.
            }
            {
                cleanup.
                unfold files_crash_rep, files_inner_rep in *; cleanup.
                repeat cleanup_pairs; repeat unify_invariants.
                repeat apply_specs; cleanup; eauto;
                repeat split_ors; cleanup.
                simpl in *; cleanup.
                simpl in *; repeat cleanup_pairs; repeat unify_invariants.

                eexists; unfold files_inner_rep in *; cleanup;
                simpl; eexists; repeat (split; eauto);
                simpl; eexists; split; eauto;
                eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
                intros; solve_bounds.
            }
            intros; cleanup; congruence.
       }
       depth_first_crash_solve; try solve [ solve_delete ].
       depth_first_crash_solve; try solve [ solve_delete ].
       {
         Transparent delete_inner Inode.get_all_block_numbers.
             unfold delete_inner,
             Inode.get_all_block_numbers, 
             Inode.get_inode, Inode.InodeAllocator.read in *.
            repeat invert_exec; simpl in *; cleanup.
       }
       {
        unfold delete_inner,
             Inode.get_all_block_numbers, 
             Inode.get_inode, Inode.InodeAllocator.read in *.
            repeat invert_exec; simpl in *; cleanup.
       }
       {
        unfold delete_inner,
             Inode.get_all_block_numbers, 
             Inode.get_inode, Inode.InodeAllocator.read in *.
            repeat invert_exec; simpl in *; cleanup.
       }
       {
        unfold delete_inner,
             Inode.get_all_block_numbers, 
             Inode.get_inode, Inode.InodeAllocator.read in *.
            repeat invert_exec; simpl in *; cleanup.
            Opaque delete_inner Inode.get_all_block_numbers.
       }
       depth_first_crash_solve; try solve [ solve_delete ].
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H15; eauto;
       cleanup; subst.
       intuition congruence.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H15; eauto;
       cleanup; subst.
       intuition congruence.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       eapply_fresh Inode.get_owner_finished_oracle_eq in H15; eauto;
       cleanup; subst.
       depth_first_crash_solve; try solve [ solve_delete ].
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       exfalso; eapply Inode.get_owner_finished_not_crashed; 
       [eauto| |eauto].
       symmetry; eauto.
       intros; cleanup; congruence.
   }
   {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2.
       logic_clean.
       exfalso; eapply Inode.get_owner_finished_not_crashed; 
       [eauto| |eauto].
       symmetry; eauto.
       intros; cleanup; congruence.
   }
   Unshelve.
   all: exact Definitions.impl.
   Qed.

   Opaque Inode.alloc.
   Lemma create_crashed_exfalso:
   forall u u' ex x x0 s1 s2 inum own own' x2 sr2 o,
    same_for_user_except u' ex x x0 ->
  refines s1 x ->
   refines s2 x0 ->
  exec Definitions.impl u o s1 (create own) (Crashed x2) ->
  inum < FSParameters.inode_count ->
  x inum = None ->
  files_crash_rep (Mem.upd x inum (new_file own)) x2 ->
  exec Definitions.impl u o s2 (create own') (Crashed sr2) ->
  files_crash_rep x0 sr2 ->
  False.
  Proof. 
  intros;
   unfold refines, files_rep, files_inner_rep in *; cleanup.
   unfold create in *.
  
   depth_first_crash_solve; try solve [solve_create].
  {
      cleanup.
      repeat rewrite <- app_assoc in H2.
      eapply_fresh map_app_ext in H2.
      logic_clean.
      eapply_fresh Inode.alloc_finished_oracle_eq in H15; eauto;
      cleanup; subst.
      depth_first_crash_solve; try solve [ solve_create ].
      {
        repeat apply_specs; 
        simpl in *; cleanup;
        unfold refines, files_rep, files_crash_rep, files_inner_rep in *; 
        repeat split_ors; cleanup;
        repeat cleanup_pairs; repeat unify_invariants.
        
        unfold file_map_rep in *; cleanup.
        edestruct H0; edestruct H6.
        eapply H17; eauto.
        eapply H16; eauto.
        rewrite Mem.upd_eq; eauto.
        congruence.
      }
      {
        repeat apply_specs; 
        simpl in *; cleanup;
        unfold refines, files_rep, files_crash_rep, files_inner_rep in *; 
        repeat split_ors; cleanup;
        repeat cleanup_pairs; repeat unify_invariants.
        
        unfold file_map_rep in *; cleanup.
        edestruct H0; edestruct H6.
        eapply H17; eauto.
        eapply H16; eauto.
        rewrite Mem.upd_eq; eauto.
        congruence.
      }
      intros; cleanup; congruence.
    }
    {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2; subst.
       cleanup.
      eapply_fresh Inode.alloc_finished_oracle_eq in H15; eauto;
      cleanup; subst.
      intuition congruence.
      intros; cleanup; congruence.
    }
    {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2; subst.
       cleanup.
      eapply_fresh Inode.alloc_finished_oracle_eq in H15; eauto;
      cleanup; subst.
      intuition congruence.
      intros; cleanup; congruence.
    }
    {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2; subst.
       cleanup.
      eapply_fresh Inode.alloc_finished_oracle_eq in H15; eauto;
      cleanup; subst.
      depth_first_crash_solve; try solve [ solve_create ].
      intros; cleanup; congruence.
    }
    {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2; subst.
       cleanup.
       symmetry in H6;
      eapply Inode.alloc_finished_not_crashed; eauto.
      intros; cleanup; congruence.
    }
    {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2; subst.
       cleanup.
       symmetry in H6;
      eapply Inode.alloc_finished_not_crashed; eauto.
      intros; cleanup; congruence.
    }
    {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2; subst.
       cleanup.
      eapply Inode.alloc_finished_not_crashed; eauto.
      intros; cleanup; congruence.
    }
    {
       cleanup.
       repeat rewrite <- app_assoc in H2.
       eapply_fresh map_app_ext in H2; subst.
       cleanup.
      eapply Inode.alloc_finished_not_crashed; eauto.
      intros; cleanup; congruence.
    }
    {
       cleanup.
       repeat apply_specs; 
        simpl in *; cleanup;
        unfold refines, files_rep, files_crash_rep, files_inner_rep in *; 
        repeat split_ors; cleanup;
        repeat cleanup_pairs; repeat unify_invariants.

        eapply Inode.alloc_crashed in H15; eauto.
        eapply Inode.alloc_crashed in H18; eauto.

        unfold refines, files_rep, files_crash_rep, files_inner_rep in *; 
        repeat split_ors; cleanup;
        repeat cleanup_pairs; repeat unify_invariants.
        
        unfold file_map_rep in *; cleanup.
        rewrite <- H13 in H4; rewrite Mem.upd_eq in H4; eauto.
        congruence.
    }
  Unshelve.
  all: exact Definitions.impl.
  Qed.

 Lemma extend_crashed_same_token:
 forall u u' o s1 s2 x x0 inum v v' get_reboot_state sr1 sr2  ex tk1 tk2,
 same_for_user_except u' ex x x0 ->
  refines s1 x ->
     refines s2 x0 ->
  exec Definitions.impl u o s1 (extend inum v) (Crashed sr1) ->
  exec Definitions.impl u o s2 (extend inum v') (Crashed sr2) ->
  token_refines _ u s1 (Extend inum v) get_reboot_state o tk1 -> 
  token_refines _ u s2 (Extend inum v') get_reboot_state o tk2 -> 
  tk1 = tk2.
  Proof. 
 simpl; intros.
 repeat match goal with
 [H: refines ?s _ ,
 H0: forall _, files_rep _ ?s -> _ |- _] =>
 specialize H0 with (1:= H)
 end;
 repeat split_ors; cleanup;
 repeat unify_execs; cleanup;
 repeat split_ors; cleanup;
 eauto; try lia; try congruence;
 repeat unify_execs; cleanup;
 repeat split_ors; cleanup;
 eauto; try lia; 
 try congruence; eauto.
exfalso; eapply extend_crashed_exfalso; eauto.
exfalso; eapply extend_crashed_exfalso.
apply same_for_user_except_symmetry; eauto.
all: eauto.
  Qed.

  Lemma change_owner_crashed_same_token:
  forall u u' o s1 s2 x x0 inum v get_reboot_state sr1 sr2 tk1 tk2,
  same_for_user_except u' (Some inum) x x0 ->
   refines s1 x ->
      refines s2 x0 ->
   exec Definitions.impl u o s1 (change_owner inum v) (Crashed sr1) ->
   exec Definitions.impl u o s2 (change_owner inum v) (Crashed sr2) ->
   token_refines _ u s1 (ChangeOwner inum v) get_reboot_state o tk1 -> 
   token_refines _ u s2 (ChangeOwner inum v) get_reboot_state o tk2 -> 
   tk1 = tk2.
   Proof. 
  simpl; intros.
  repeat match goal with
  [H: refines ?s _ ,
  H0: forall _, files_rep _ ?s -> _ |- _] =>
  specialize H0 with (1:= H)
  end;
  repeat split_ors; cleanup;
  repeat unify_execs; cleanup;
  repeat split_ors; cleanup;
  eauto; try lia; try congruence;
  repeat unify_execs; cleanup;
  repeat split_ors; cleanup;
  eauto; try lia; 
  try congruence; eauto.
 exfalso; eapply change_owner_crashed_exfalso; eauto.
 exfalso; eapply change_owner_crashed_exfalso.
 apply same_for_user_except_symmetry; eauto.
 all: eauto.
   Qed.


   Lemma delete_crashed_same_token:
   forall u u' o s1 s2 x x0 inum inum' get_reboot_state sr1 sr2  ex tk1 tk2,
   same_for_user_except u' ex x x0 ->
    refines s1 x ->
       refines s2 x0 ->
    exec Definitions.impl u o s1 (delete inum) (Crashed sr1) ->
    exec Definitions.impl u o s2 (delete inum') (Crashed sr2) ->
    token_refines _ u s1 (Delete inum) get_reboot_state o tk1 -> 
    token_refines _ u s2 (Delete inum') get_reboot_state o tk2 -> 
    tk1 = tk2.
    Proof. 
   simpl; intros.
   repeat match goal with
   [H: refines ?s _ ,
   H0: forall _, files_rep _ ?s -> _ |- _] =>
   specialize H0 with (1:= H)
   end;
   repeat split_ors; cleanup;
   repeat unify_execs; cleanup;
   repeat split_ors; cleanup;
   eauto; try lia; try congruence;
   repeat unify_execs; cleanup;
   repeat split_ors; cleanup;
   eauto; try lia; 
   try congruence; eauto.
  exfalso; eapply delete_crashed_exfalso; eauto.
  exfalso; eapply delete_crashed_exfalso.
  apply same_for_user_except_symmetry; eauto.
  all: eauto.
    Qed.


    Lemma create_crashed_same_token:
   forall u u' o s1 s2 x x0 own own' get_reboot_state sr1 sr2  ex tk1 tk2,
   same_for_user_except u' ex x x0 ->
    refines s1 x ->
       refines s2 x0 ->
    exec Definitions.impl u o s1 (create own) (Crashed sr1) ->
    exec Definitions.impl u o s2 (create own') (Crashed sr2) ->
    token_refines _ u s1 (Create own) get_reboot_state o tk1 -> 
    token_refines _ u s2 (Create own') get_reboot_state o tk2 -> 
    tk1 = tk2.
    Proof. 
   simpl; intros.
   repeat match goal with
   [H: refines ?s _ ,
   H0: forall _, files_rep _ ?s -> _ |- _] =>
   specialize H0 with (1:= H)
   end;
   repeat split_ors; cleanup;
   repeat unify_execs; cleanup;
   repeat split_ors; cleanup;
   eauto; try lia; try congruence;
   repeat unify_execs; cleanup;
   repeat split_ors; cleanup;
   eauto; try lia; 
   try congruence; eauto.
  exfalso; eapply create_crashed_exfalso; eauto.
  exfalso; eapply create_crashed_exfalso.
  apply same_for_user_except_symmetry; eauto.
  all: eauto.
  {
      unfold same_for_user_except in *; cleanup.
      destruct (Compare_dec.lt_dec x3 x4).
        edestruct H; exfalso.
        eapply H14; eauto.
        destruct_fresh (x x3); eauto.
        exfalso; eapply H6; eauto.
        apply Compare_dec.not_lt in n.
        inversion n; subst; eauto.
        edestruct H; exfalso.
        eapply H9.
        instantiate (1:= x4); lia.
        destruct_fresh (x0 x4); eauto.
        exfalso; eapply H16.
        2: eauto.
        congruence.
  }
Qed.



Lemma write_crashed_same_token:
forall u u' o s1 s2 x x0 inum off v v' get_reboot_state sr1 sr2  ex tk1 tk2,
 same_for_user_except u' ex x x0 ->
 refines s1 x ->
 refines s2 x0 ->
 exec Definitions.impl u o s1 (write inum off v) (Crashed sr1) ->
 exec Definitions.impl u o s2 (write inum off v') (Crashed sr2) ->
 token_refines _ u s1 (Write inum off v) get_reboot_state o tk1 -> 
 token_refines _ u s2 (Write inum off v') get_reboot_state o tk2 -> 
 tk1 = tk2.
    Proof. 
        simpl; intros.
        repeat match goal with
        [H: refines ?s _ ,
        H0: forall _, files_rep _ ?s -> _ |- _] =>
        specialize H0 with (1:= H)
        end;
        repeat split_ors; cleanup;
        repeat unify_execs; cleanup;
        repeat split_ors; cleanup;
        eauto; try lia; try congruence;
        repeat unify_execs; cleanup;
        repeat split_ors; cleanup;
        eauto; try lia; 
        try congruence; eauto.
        {
            destruct_fresh (x0 inum).
            destruct (value_dec (seln (blocks f) off value0) v'); subst.
            
        }
       exfalso; eapply write_crashed_exfalso; eauto.
       exfalso; eapply write_crashed_exfalso.
       apply same_for_user_except_symmetry; eauto.
       all: eauto.
         Qed.
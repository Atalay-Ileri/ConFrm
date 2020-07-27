Require Import Framework FSParameters.
Require Import TransactionCacheLayer TransactionalDiskLayer Transaction.
Close Scope predicate_scope.
Import ListNotations.

Local Definition low_op := TransactionCacheOperation.
Local Definition high_op := (TransactionalDiskOperation data_length).
Local Definition low := TransactionCacheLang.
Local Definition high := (TransactionalDiskLang data_length).

Fixpoint apply_list {A AEQ V} (m: @mem A AEQ V) l :=
  match l with
  | nil =>
    m
  | av :: l' =>
    apply_list (upd m (fst av) (snd av)) l'
  end.

Definition compile  T (p2: Operation.prog high_op T) : prog low T.
  destruct p2.
  exact start.
  exact (read a).
  exact (write a v).
  exact commit.
  exact abort.
Defined.

Definition oracle_refines_to T (d1: state low) (p: Operation.prog high_op T) o1 o2 : Prop :=
     match p with
     | Start =>
       (exists d1' r,
          exec low o1 d1 start (Finished d1' r) /\
          o2 = [Cont] /\
          d1' = (Some [], snd d1)) \/
       
       (exists d1',
          exec low o1 d1 start (Crashed d1') /\
          ((o2 = [CrashBefore] /\
            d1' = d1) \/
           
           (o2 = [CrashAfter] /\
            d1' = (Some [], snd d1))))
         
     | Read a =>
       (exists d1' r,
          exec low o1 d1 (read a) (Finished d1' r) /\
          o2 = [Cont] /\
          d1' = d1) \/
       
       (exists d1',
          exec low o1 d1 (read a) (Crashed d1') /\
          (o2 = [CrashBefore] \/
          (o2 = [CrashAfter] /\
           exists l, fst d1 = Some l /\
           exists v, get_latest l a = Some v \/ (get_latest l a = None /\ (snd d1) a = Some v))) /\
          d1' = d1)
         
     | Write a v =>
       (exists d1' r,
          exec low o1 d1 (write a v) (Finished d1' r) /\          
          ((o2 = [Cont] /\
            a < data_length /\
            fst d1 <> None /\
            d1' = (option_map (fun l => (a, v)::l) (fst d1), snd d1)) \/
           (o2 = [Cont] /\
            a >= data_length /\
            d1' = d1) \/
           (exists l,
              o2 = [TxnFull] /\
              fst d1 = Some l /\
              a < data_length /\
              length l >= log_length /\
              d1' = d1)
          )
       ) \/
       
       (exists d1',
          exec low o1 d1 (write a v) (Crashed d1') /\
          ((o2 = [CrashBefore] /\
            d1' = d1) \/
           
           (o2 = [CrashAfter] /\
            fst d1 <> None /\
            d1' = (option_map (fun l => (a, v)::l) (fst d1), snd d1))))

     | Commit =>
       (exists d1' r,
          exec low o1 d1 commit (Finished d1' r) /\
          o2 = [Cont] /\
          (exists l, fst d1 = Some l /\
                d1' = (Some [], mem_union (apply_list empty_mem (rev l)) (snd d1)))) \/
       
       (exists d1',
          exec low o1 d1 commit (Crashed d1') /\
          ((o2 =[CrashBefore] /\
            d1' = d1) \/
            (o2 = [CrashDuringCommit] /\
            (exists l, fst d1 = Some l /\
                d1' = (Some l,  mem_union (apply_list empty_mem (rev l)) (snd d1) ))) \/
           (o2 = [CrashAfter] /\
            (exists l, fst d1 = Some l /\
                d1' = (Some [],  mem_union (apply_list empty_mem (rev l)) (snd d1) )))))
         
     | Abort =>
       (exists d1' r,
          exec low o1 d1 abort (Finished d1' r) /\
          o2 = [Cont] /\
          d1' = (Some [], snd d1)) \/
       
       (exists d1',
          exec low o1 d1 abort (Crashed d1') /\
          ((o2 = [CrashBefore] /\
           d1' = d1) \/
           (o2 = [CrashAfter] /\
          d1' = (Some [], snd d1))))
     end.

   Definition refines_to (d1: state low) (d2: state high) :=     
     exists l,
       fst d1 = Some l /\
       let txn_cache := apply_list empty_mem (rev l) in
       fst d2 = txn_cache /\
       addrs_match txn_cache (snd d1) /\
       snd d2 = snd d1 /\
       (forall a, a < data_length -> snd d1 a <> None).

   
  Definition TransactionalDiskOperationRefinement := Build_OperationRefinement compile refines_to oracle_refines_to.
  Definition TransactionalDiskRefinement := LiftRefinement high TransactionalDiskOperationRefinement.

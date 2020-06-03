Require Import Framework FSParameters.
Require Import TransactionCacheLayer TransactionalDiskLayer Transaction.
Close Scope pred_scope.
Import ListNotations.

Notation "'low_op'" := TransactionCacheOperation.
Notation "'high_op'" := (TransactionalDiskOperation data_length).
Notation "'low'" := TransactionCacheLang.
Notation "'high'" := (TransactionalDiskLang data_length).

Fixpoint apply_list {A AEQ V} (m: @mem A AEQ V) l :=
  match l with
  | nil =>
    m
  | av :: l' =>
    apply_list (upd m (fst av) (snd av)) l'
  end.

Fixpoint compile {T} (p2: prog high T) : prog low T.
  destruct p2.
  {
    destruct p.
    exact start.
    exact (read a).
    exact (write a v).
    exact commit.
    exact abort.
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
     | Start =>
       (exists d1' r,
          exec low o1 d1 start (Finished d1' r) /\
          o2 = [OpOracle high_op [Cont] ] /\
          d1' = (Some [], snd d1)) \/
       
       (exists d1',
          exec low o1 d1 start (Crashed d1') /\
          ((o2 = [OpOracle high_op [CrashBefore] ] /\
            d1' = d1) \/
           
           (o2 = [OpOracle high_op [CrashAfter] ] /\
            d1' = (Some [], snd d1))))
         
     | Read a =>
       (exists d1' r,
          exec low o1 d1 (read a) (Finished d1' r) /\
          o2 = [OpOracle high_op [Cont] ] /\
          d1' = d1) \/
       
       (exists d1',
          exec low o1 d1 (read a) (Crashed d1') /\
          (o2 = [OpOracle high_op [CrashBefore] ] \/
          (o2 = [OpOracle high_op [CrashAfter] ] /\
           exists l, fst d1 = Some l /\
           exists v, get_latest l a = Some v \/ (get_latest l a = None /\ Disk.read (snd d1) a = Some v))) /\
          d1' = d1)
         
     | Write a v =>
       (exists d1' r,
          exec low o1 d1 (write a v) (Finished d1' r) /\          
          ((o2 = [OpOracle high_op [Cont] ] /\
           d1' = (option_map (fun l => (a, v)::l) (fst d1), snd d1)) \/
          (o2 = [OpOracle high_op [TxnFull] ] /\
           d1' = d1)
          )
       ) \/
       
       (exists d1',
          exec low o1 d1 (write a v) (Crashed d1') /\
          ((o2 = [ OpOracle high_op [CrashBefore] ] /\
            d1' = d1) \/
           
           (o2 = [ OpOracle high_op [CrashAfter] ] /\
            fst d1 <> None /\
            d1' = (option_map (fun l => (a, v)::l) (fst d1), snd d1))))

     | Commit =>
       (exists d1' r,
          exec low o1 d1 commit (Finished d1' r) /\
          o2 = [OpOracle high_op [Cont] ] /\
          (exists l, fst d1 = Some l /\
                d1' = (None, merge (apply_list empty_mem (rev l)) (snd d1)))) \/
       
       (exists d1',
          exec low o1 d1 commit (Crashed d1') /\
          ((o2 = [OpOracle high_op [CrashBefore] ] /\
           d1' = d1) \/
           (o2 = [OpOracle high_op [CrashAfter] ] /\
            (exists l, fst d1 = Some l /\
                d1' = (None,  merge (apply_list empty_mem (rev l)) (snd d1) )))))
         
     | Abort =>
       (exists d1' r,
          exec low o1 d1 abort (Finished d1' r) /\
          o2 = [OpOracle high_op [Cont] ]) \/
       
       (exists d1',
          exec low o1 d1 abort (Crashed d1') /\
          ((o2 = [OpOracle high_op [CrashBefore] ] /\
           d1' = d1) \/
           (o2 = [OpOracle high_op [CrashAfter] ] /\
          d1' = (None, snd d1))))
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
     
     match fst d1 with
     | Some l =>
       let txn_cache := apply_list empty_mem (rev l) in
       fst d2 = txn_cache /\
       addrs_match txn_cache (snd d1)
     | None =>
       fst d2 = empty_mem
     end /\
     snd d2 = snd d1.

  Definition compilation_of T (p1: prog low T) (p2: prog high T) :=
    p1 = @compile T p2.

  Definition TransactionalDiskRefinement := Build_Refinement compilation_of refines_to oracle_refines_to.

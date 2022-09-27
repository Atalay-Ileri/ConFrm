Require Import Framework TotalMem CachedDiskLayer LoggedDiskLayer Log Log.RepImplications Log.Specs LogCache.
Require Import FSParameters FunctionalExtensionality Lia.
Close Scope predicate_scope.
Import ListNotations.

Local Definition impl_core := CachedDiskOperation.
Local Definition abs_core := LoggedDiskOperation log_length data_length.
Local Definition impl := CachedDiskLang.
Local Definition abs := LoggedDiskLang log_length data_length.

Definition compile T (p2: Core.operation abs_core T) : prog impl T.
 destruct p2.
 exact (read a).
 exact (write l l0).
 exact recover.
 exact (init l).
Defined.

Definition token_refines  T u (d1: state impl) (p: Core.operation abs_core T) get_reboot_state o1 o2 : Prop :=
  match p with
   | Read a =>
     (exists d1' r,
        exec impl u o1 d1 (read a) (Finished d1' r) /\
        o2 = Cont /\
        (forall merged_disk,
           cached_log_rep merged_disk d1 -> 
           cached_log_rep merged_disk d1')) \/
     (exists d1',
        exec impl u o1 d1 (read a) (Crashed d1') /\
        o2 = CrashBefore /\
        (forall merged_disk,
            cached_log_rep merged_disk d1 -> 
            cached_log_rep merged_disk d1'))
   | Write al vl =>
   forall merged_disk hdr txns,
   let c1 := length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl) in
    let c2 := count (current_part hdr) in
    let c3 := fold_left Nat.add (map (fun txnr => (addr_count txnr) * 2 + (data_count txnr) * 4 + 3) (records (current_part hdr))) 0 in
   (fst d1 = Mem.list_upd_batch empty_mem (map addr_list txns) (map data_blocks txns) /\
    log_header_rep hdr txns (snd d1) /\
    merged_disk = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd d1)) (map addr_list txns) (map data_blocks txns))) /\
    (forall a, a >= data_start -> snd ((snd (snd d1)) a) = [])) ->
     (exists d1' r,
          exec impl u o1 d1 (write al vl) (Finished d1' r) /\          
          o2 = Cont /\
          ((cached_log_rep merged_disk d1' \/
             cached_log_rep (upd_batch merged_disk al vl) d1'))) \/
     (exists d1',
        (exec impl u o1 d1 (write al vl) (Crashed d1') /\
         (o2 = CrashBefore /\
         ((cached_log_rep merged_disk d1' /\
         (
            o1 = [LayerImplementation.Crash CachedDiskOperation] \/ 

            (exists o', 
            o1 = map transform_token o' /\
            commit_crashed_oracle_is_1 o' (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) \/
        
            (count (current_part hdr) + length (addr_list_to_blocks 
              (map (Init.Nat.add data_start) al)) + length vl > log_length /\
              write_crashed_oracle_is_1 o1 hdr (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))
            )
          )) \/
          
          (cached_log_crash_rep (During_Apply merged_disk) d1' /\
          (exists o', 
            o1 = OpToken
            (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
            (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
              (Token2 CryptoOperation
                  (DiskOperation addr_dec value (fun a : addr => a < disk_size))
                  DiskLayer.Cont))
          :: LayerImplementation.Cont
              (HorizontalComposition (CacheOperation addr_dec value)
                  CryptoDiskOperation)
            :: LayerImplementation.Cont
                  (HorizontalComposition (CacheOperation addr_dec value)
                    CryptoDiskOperation)
                :: map transform_token o' /\
            (apply_log_crashed_oracle_is_3 o' hdr \/ 
            exists n, apply_log_crashed_oracle_is_1 o' hdr n)) /\
          count (current_part hdr) + length (addr_list_to_blocks 
              (map (Init.Nat.add data_start) al)) + length vl > log_length) \/
          
          (cached_log_crash_rep (After_Apply merged_disk) d1' /\ 
          write_crashed_oracle_is_5 o1 hdr /\
          count (current_part hdr) + length (addr_list_to_blocks 
          (map (Init.Nat.add data_start) al)) + length vl > log_length))) \/
        (exec impl u o1 d1 (write al vl) (Crashed d1') /\
         o2 = CrashAfter /\
         (
            cached_log_crash_rep (After_Commit (upd_batch merged_disk al vl)) d1' /\
            NoDup al /\
            length al = length vl /\
            Forall (fun a : nat => a < data_length) al /\
            length (addr_list_to_blocks al) + length vl <= log_length /\
            ((((exists o', 
            o1 = map transform_token o' /\
            commit_crashed_oracle_is_4 o'
           (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) \/
           (exists o', 
            o1 = map transform_token o' ++  [LayerImplementation.Crash
            (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)] /\
            commit_finished_oracle_is_true o'
           (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) \/
           (exists o1' o2' n, 
            o1 = map transform_token o1' ++  LayerImplementation.Cont
            (HorizontalComposition (CacheOperation addr_dec value)
               CryptoDiskOperation) :: o2' /\
            commit_finished_oracle_is_true o1'
           (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) /\
           write_batch_to_cache_crashed_oracle_is o2' n)) /\
            count (current_part hdr) + length (addr_list_to_blocks 
              (map (Init.Nat.add data_start) al)) + length vl <= log_length) \/
            
            (write_crashed_oracle_is_4 o1 hdr (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) /\
            count (current_part hdr) + length (addr_list_to_blocks 
              (map (Init.Nat.add data_start) al)) + length vl > log_length)))) \/
              
        (exec impl u o1 d1 (write al vl) (Crashed d1') /\
         (
           ((exists txns,
           log_crash_rep (During_Commit_Log_Write txns) (snd d1') /\
              merged_disk = total_mem_map fst (shift (plus data_start)
              (list_upd_batch_set (snd (snd d1')) (map addr_list txns) (map data_blocks txns))) /\
              (forall a, a >= data_start -> snd ((snd (snd d1')) a) = [])) /\
              o2 = CrashBefore /\
              (
                  ((exists o', 
                  o1 = map transform_token o' /\
                  commit_crashed_oracle_is_2 o'
                   (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) /\
                  count (current_part hdr) + length (addr_list_to_blocks 
                  (map (Init.Nat.add data_start) al)) + length vl <= log_length) \/
              
                  (write_crashed_oracle_is_2 o1 hdr (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) /\
                  count (current_part hdr) + length (addr_list_to_blocks 
                  (map (Init.Nat.add data_start) al)) + length vl > log_length)
              )
            ) \/
            (exists old_txns new_txn,
            let txns := old_txns ++ [new_txn] in
            (log_crash_rep (During_Commit_Header_Write old_txns txns) (snd d1') /\
              (upd_batch merged_disk al vl) = total_mem_map fst (shift (plus data_start)
              (list_upd_batch_set (snd (snd d1')) (map addr_list txns)
                  (map data_blocks txns))) /\

              merged_disk = total_mem_map fst (shift (plus data_start)
              (list_upd_batch_set (snd (snd d1')) (map addr_list old_txns)
                                  (map data_blocks old_txns))) /\
              (forall a, a >= data_start -> snd ((snd (snd d1')) a) = [])) /\
              (
                  ((exists o', 
                  o1 = map transform_token o' /\
                  commit_crashed_oracle_is_3 o'
                   (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) /\
                  count (current_part hdr) + length (addr_list_to_blocks 
                  (map (Init.Nat.add data_start) al)) + length vl <= log_length /\
                  (forall i, i < length (addr_list_to_blocks al) + length vl -> 
                    fst ((snd (snd d1')) (log_start + Log.count (Log.current_part hdr) + i)) = 
                    seln (map (encrypt (Log.key (Log.record new_txn)))
                    (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) i value0 /\
                    length (snd ((snd (snd d1')) (log_start + Log.count (Log.current_part hdr) + i))) = 1)) \/
              
                  (write_crashed_oracle_is_3 o1 hdr (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) /\
                  count (current_part hdr) + length (addr_list_to_blocks 
                  (map (Init.Nat.add data_start) al)) + length vl > log_length /\
                  (forall i, i < length (addr_list_to_blocks al) + length vl -> 
                  fst ((snd (snd d1')) (log_start +  i)) = 
                  seln (map (encrypt (Log.key (Log.record new_txn)))
                  (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) i value0 /\
                  length (snd ((snd (snd d1')) (log_start + i))) = 1))
              ) /\
              ((exists old_hdr new_hdr,
              (snd (snd d1')) hdr_block_num = (encode_header new_hdr, [encode_header old_hdr]) /\
              new_hdr <> old_hdr /\
              o2 = CrashBefore /\
              cached_log_reboot_rep_explicit_part old_hdr merged_disk Log.Current_Part (get_reboot_state d1') /\
              (snd (snd (get_reboot_state  d1'))) hdr_block_num = (encode_header old_hdr, [])) \/
            
              (exists old_hdr new_hdr,
              (snd (snd d1')) hdr_block_num = (encode_header new_hdr, [encode_header old_hdr]) /\
              new_hdr <> old_hdr /\
              cached_log_reboot_rep_explicit_part new_hdr merged_disk Log.Old_Part (get_reboot_state d1') /\
              o2 = CrashBefore /\
              (((exists o', 
              o1 = map transform_token o' /\
              commit_crashed_oracle_is_3 o'
               (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) /\
              (exists i, i < length (addr_list_to_blocks al) + length vl /\ 
              fst ((snd (snd (get_reboot_state  d1'))) (log_start + Log.count (Log.current_part hdr) + i)) <> 
              seln (map (encrypt (Log.key (Log.record new_txn)))
              (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) i value0)) \/
              
              (write_crashed_oracle_is_3 o1 hdr (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) /\
              (exists i, i < length (addr_list_to_blocks al) + length vl /\ 
              fst ((snd (snd (get_reboot_state  d1'))) (log_start + i)) <> 
              seln (map (encrypt (Log.key (Log.record new_txn)))
              (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) i value0)))) \/
              
            (exists old_hdr new_hdr,
            (snd (snd d1')) hdr_block_num = (encode_header new_hdr, [encode_header old_hdr]) /\
            new_hdr <> old_hdr /\
            cached_log_reboot_rep_explicit_part new_hdr (upd_batch merged_disk al vl) Log.Current_Part (get_reboot_state d1') /\
            o2 = CrashAfter /\
            (snd (snd (get_reboot_state  d1'))) hdr_block_num = (encode_header new_hdr, []) /\
            (((exists o', 
            o1 = map transform_token o' /\
            commit_crashed_oracle_is_3 o'
             (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) /\
              (forall i, i < length (addr_list_to_blocks al) + length vl ->
              fst ((snd (snd (get_reboot_state  d1'))) (log_start + Log.count (Log.current_part hdr) + i)) = 
              seln (map (encrypt (Log.key (Log.record new_txn)))
              (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) i value0)) \/
              
              (write_crashed_oracle_is_3 o1 hdr (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) /\
              (forall i, i < length (addr_list_to_blocks al) + length vl ->
              fst ((snd (snd (get_reboot_state  d1'))) (log_start + i)) =
              seln (map (encrypt (Log.key (Log.record new_txn)))
              (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) i value0))))) /\
            NoDup al /\
            length al = length vl /\
            Forall (fun a : nat => a < data_length) al /\
            length (addr_list_to_blocks al) + length vl <= log_length )))
            )
           ) 
   | Recover =>
     (exists d1',
        exec impl u o1 d1 recover (Finished d1' tt) /\
        o2 = Cont /\
        (forall merged_disk,
           cached_log_reboot_rep merged_disk d1 ->
           cached_log_rep merged_disk d1')) \/
     (exists d1',
        exec impl u o1 d1 recover (Crashed d1') /\
        o2 = CrashBefore /\
        (forall merged_disk,
           cached_log_reboot_rep merged_disk d1 ->
           (cached_log_reboot_rep merged_disk d1' \/
           cached_log_crash_rep (During_Recovery merged_disk) d1' \/
           cached_log_crash_rep (After_Commit merged_disk) d1')))

   | Init l_av =>
     let l_a := map fst l_av in
     let l_v := map snd l_av in
     (exists d1',
        exec impl u o1 d1 (init l_av) (Finished d1' tt) /\
        o2 = Cont /\
        length l_a = length l_v /\
        cached_log_rep (total_mem_map fst (shift (Nat.add data_start) (upd_batch_set (snd (snd d1)) (map (PeanoNat.Nat.add data_start) l_a) l_v))) d1') \/
     (exists d1',
        exec impl u o1 d1 (init l_av) (Crashed d1') /\
        o2 = CrashBefore)
   end.

  Definition refines (d1: state impl) (d2: state abs) :=
      cached_log_rep d2 d1.
  
  Definition refines_reboot (d1: state impl) (d2: state abs) :=
      cached_log_reboot_rep d2 d1 /\ (forall a vs, snd (snd d1) a = vs -> snd vs = nil).

  Set Nested Proofs Allowed.
  
  Lemma hashes_in_hashmap_subset:
    forall hl hm hm' h0,
      hashes_in_hashmap hm h0 hl ->
      subset hm hm' ->
      hashes_in_hashmap hm' h0 hl.
  Proof.
    induction hl; simpl; intros; cleanup; eauto.
    split; eauto.
    edestruct H0; eauto.
  Qed.
  
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
      unfold refines, cached_log_rep in *; cleanup.
      eapply recover_finished in H0; eauto.
      unfold cached_log_reboot_rep;
      eexists; intuition eauto.      
      eapply log_rep_to_reboot_rep_same; eauto.
    }
    {
      eapply init_finished in H0; eauto.
    }
  Qed.

  Definition LoggedDiskCoreRefinement := Build_CoreRefinement compile refines refines_reboot token_refines exec_compiled_preserves_refinement_finished_core.
  Definition LoggedDiskRefinement := LiftRefinement (LoggedDiskLang log_length data_length) LoggedDiskCoreRefinement.

  Notation "| p |" := (Op (LoggedDiskOperation log_length data_length) p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op (LoggedDiskOperation log_length data_length) p1) (fun x => p2))(right associativity, at level 60).

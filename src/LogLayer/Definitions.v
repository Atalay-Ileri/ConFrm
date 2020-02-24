(*
Require Import Primitives Simulation.
Import ListNotations.

Set Implicit Arguments.

Definition hashmap := @mem hash hash_dec (hash * value).
Definition encryptionmap := @mem value value_dec (key * value).
  
Section DiskLayer.  
  
  Inductive token :=
  | EncryptedBlocks : list value -> token
  | CrashBefore : token
  | CrashAfter : token
  | Success : token
  | Fail : token.

  Definition token_dec : forall (t t': token), {t=t'}+{t<>t'}.
    decide equality.
  Defined.

  Definition oracle := list token.
  
  Definition aux_state := (list key * encryptionmap * hashmap)%type.
  Definition disk_state := (set value * disk (set value) * disk (set value))%type.                                 
  Definition state := (aux_state * disk_state)%type.

  Definition commit (ds: disk_state) (encrypted_blocks: list value) : disk_state :=
    let '(headers, log_blocks, disk_blocks) := ds in
    let hdr := decode_header (fst headers) in
    let cur_hash := cur_hash hdr in
    let cur_count := cur_count hdr in
    let txns := txn_records hdr in
    let new_count := cur_count + (length addr_l + length data_l) in
    let new_txn := Build_txn_record new_key cur_count (length addr_l) (length data_l) in
    let new_hdr := Build_header cur_hash cur_count (length txns) new_hash new_count (txns++[new_txn]) in
    _ <- write_header new_hdr;
    Ret true
  else
    Ret false.
  
  Inductive prog : Type -> Type :=
  | Commit : list value -> list value -> prog bool
  | Apply : prog bool
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
  Inductive exec :
    forall T, oracle ->  state -> prog T -> @Result state T -> Prop :=
  | ExecCommitSuccess : 
      forall m d a v,
        exec [Cont] (m, d) (Read a) (Finished (m, d) v)
             
  | ExecWrite :
      forall m d a v,
        read d a <> None ->
        exec [Cont] (m, d) (Write a v) (Finished (m, (write d a v)) tt)

  | ExecHash : 
      forall em hm d h v,
        let hv := hash_function h v in
        consistent hm hv (h, v) ->
        exec [Cont] (em, hm, d) (Hash h v) (Finished (em, (upd hm hv (h, v)), d) hv)
             
  | ExecEncrypt : 
      forall kl em hm d k v,
        let ev := encrypt k v in
        consistent em ev (k, v) ->
        exec [Cont] (kl, em, hm, d) (Encrypt k v) (Finished (kl, (upd em ev (k, v)), hm, d) ev)

  | ExecDecrypt : 
      forall kl em hm d ev k v,
        ev = encrypt k v ->
        em ev = Some (k, v) ->
        exec [Cont] (kl, em, hm, d) (Decrypt k ev) (Finished (kl, em, hm, d) v)

  | ExecGetKey : 
      forall vl kl em hm d k,
        ~In k kl ->
        consistent_with_upds em
             (map (encrypt k) vl) (map (fun v => (k, v)) vl) ->
        exec [Key k] (kl, em, hm, d) (GetKey vl) (Finished ((k::kl), em, hm, d) k)
             
  | ExecRet :
      forall d T (v: T),
        exec [Cont] d (Ret v) (Finished d v)

  | ExecBind :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 d1 d1' o2 r ret,
        exec o1 d1 p1 (Finished d1' r) ->
        exec o2 d1' (p2 r) ret ->
        exec (o1++o2) d1 (Bind p1 p2) ret

  | ExecOpCrash :
      forall T d (p: prog T),
        (forall T' (p1: prog T') p2, p <> Bind p1 p2) ->
        exec [Crash] d p (Crashed d)
             
  | ExecBindCrash :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 d1 d1',
        exec o1 d1 p1 (Crashed d1') ->
        exec o1 d1 (Bind p1 p2) (Crashed d1').

  Fixpoint oracle_ok {T} (p: prog T) o s :=
    match p with
    | Bind p1 p2 =>
      exists o1 o2,
      o = o1++o2 /\
      oracle_ok p1 o1 s /\
      (forall s' r,
          exec o1 s p1 (Finished s' r) ->
          oracle_ok (p2 r) o2 s') /\
      (forall s',
          exec o1 s p1 (Crashed s') ->
          o2 = [])
    | GetKey vl =>
      (exists k, ~In k (fst(fst(fst s))) /\
            consistent_with_upds (snd(fst (fst s)))
                (map (encrypt k) vl) (map (fun v => (k,v)) vl) /\
            o = [Key k]) \/ o = [Crash]
    | _ =>
      o = [Cont] \/ o = [Crash]
    end.

  Definition layer1_lts := Build_LTS oracle state prog exec.
End DiskLayer.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
Hint Constructors exec.

*)
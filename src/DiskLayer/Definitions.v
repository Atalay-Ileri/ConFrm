Require Import Primitives Simulation Layer.
Import ListNotations.

Set Implicit Arguments.

Definition hashmap := @mem hash hash_dec (hash * value).
Definition encryptionmap := @mem value value_dec (key * value).
  
  Inductive token :=
  | Key : key -> token
  | Crash : token
  | Cont : token.

  Definition token_dec : forall (t t': token), {t=t'}+{t<>t'}.
    decide equality.
    apply key_dec.
  Defined.

  Definition oracle := list token.

  Definition state := (((list key * encryptionmap)* hashmap) * disk (set value))%type.
  
  Inductive op : Type -> Type :=
  | Read : addr -> op value
  | Write : addr -> value -> op unit
  | GetKey : list value -> op key
  | Hash : hash -> value -> op hash
  | Encrypt : key -> value -> op value
  | Decrypt : key -> value -> op value.
   
  Inductive exec :
    forall T, oracle ->  state -> op T -> @Result state T -> Prop :=
  | ExecRead : 
      forall m d a v,
        read d a = Some v ->
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
 
  | ExecCrash :
      forall T d (p: op T),
        exec [Crash] d p (Crashed d).

  Fixpoint oracle_ok T (p: op T) (o: oracle) (s: state) :=
   match p with
  | GetKey vl =>
      (exists k, ~In k (fst(fst(fst s))) /\
            @consistent_with_upds _ _ value_dec (snd(fst (fst s)))
                (map (encrypt k) vl) (map (fun v => (k,v)) vl) /\
            o = [Key k]) \/ o = [Crash]
    | _ =>
      o = [Cont] \/ o = [Crash]
    end.


  Theorem exec_deterministic_wrt_oracle :
    forall o s T (p: op T) ret1 ret2,
      exec o s p ret1 ->
      exec o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto.
  Qed.

  Theorem exec_then_oracle_ok:
    forall T (p: op T) o s r,
      exec o s p r ->
      oracle_ok p o s.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto.
  Qed.
  
Module DiskOperation <: Operation.
  Definition oracle := oracle.
  Definition oracle_dec:= list_eq_dec token_dec.
  Definition state := state.
  Definition op := op.
  Definition exec := exec.
  Definition oracle_ok := oracle_ok.
  Definition exec_deterministic_wrt_oracle :=
    exec_deterministic_wrt_oracle.
  Definition exec_then_oracle_ok :=
    exec_then_oracle_ok.
End DiskOperation.

Module DiskHL := HoareLogic DiskOperation.
Export DiskHL.

Definition layer1_lts := Build_LTS DiskHL.L.oracle state DiskHL.L.prog DiskHL.L.exec.

Notation "p >> s" := (p (snd s)) (right associativity, at level 60).
Hint Constructors exec.
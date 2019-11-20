Require Import Primitives Simulation.
Import ListNotations.

Set Implicit Arguments.


Variable hash : Type.
Variable hash_dec: forall h1 h2: hash, {h1 = h2}+{h1<>h2}.
Variable hash_function: hash -> value -> hash.

Variable encrypt: hash -> value -> value.
Axiom encrypt_ext: forall k v v', encrypt k v = encrypt k v' -> v = v'.

Definition hashmap := @mem hash hash_dec (hash * value).
Definition encryptionmap := @mem value value_dec (hash * value).
  
Section Layer1.  
  
  Inductive token :=
  | Crash : token
  | Cont : token.

  Definition token_dec : forall (t t': token), {t=t'}+{t<>t'}.
    decide equality.
  Defined.

  Definition oracle := list token.

  Definition state := ((encryptionmap * hashmap) * disk (set value))%type.
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog value
  | Write : addr -> value -> prog unit
  | Hash : hash -> value -> prog hash
  | Encrypt : hash -> value -> prog value
  | Decrypt : hash -> value -> prog value
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
  Inductive exec :
    forall T, oracle ->  state -> prog T -> @Result state T -> Prop :=
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
      forall em hm d k v,
        let ev := encrypt k v in
        consistent em ev (k, v) ->
        exec [Cont] (em, hm, d) (Encrypt k v) (Finished ((upd em ev (k, v)), hm, d) ev)

  | ExecDecrypt : 
      forall em hm d ev k v,
        ev = encrypt k v ->
        consistent em ev (k, v) ->
        exec [Cont] (em, hm, d) (Decrypt k ev) (Finished ((upd em ev (k, v)), hm, d) v)
             
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
    | _ =>
      o = [Cont] \/ o = [Crash]
    end.

  Definition layer1_lts := Build_LTS oracle state prog exec.
End Layer1.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
Hint Constructors exec.
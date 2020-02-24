Require Import Primitives Simulation.
Import ListNotations.

Set Implicit Arguments.
  
Section CacheLayer.  
  
  Inductive token :=
  | Crash : token
  | Cont : token.

  Definition token_dec : forall (t t': token), {t=t'}+{t<>t'}.
    decide equality.
  Defined.

  Definition oracle := list token.  

  (* Had  to put unit as aux_state to make it compliant to the structure of the rest *)
  Definition state := (unit * disk value)%type.
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog (option value)
  | Write : addr -> value -> prog unit
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
  Inductive exec :
    forall T, oracle ->  state -> prog T -> @Result state T -> Prop :=
  | ExecRead : 
      forall x d a,
        exec [Cont] (x, d) (Read a) (Finished (x, d) (d a))
             
  | ExecWrite :
      forall x d a v,
        exec [Cont] (x, d) (Write a v) (Finished (x, (upd d a v)) tt)

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

  Definition cache_layer_lts := Build_LTS oracle state prog exec.
End CacheLayer.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
Hint Constructors exec.
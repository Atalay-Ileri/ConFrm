Require Import List BaseTypes Memx CommonAutomation Disk Simulation.
Import ListNotations.

Set Implicit Arguments.

Section Layer1.

  Inductive token :=
  | Crash : token
  | Cont : token.

  Definition token_dec : forall (t t': token), {t=t'}+{t<>t'}. decide equality. Defined.
  Definition oracle := list token.

  Definition state := disk (set value).
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog value
  | Write : addr -> value -> prog unit
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
  Inductive exec :
    forall T, oracle ->  state -> prog T -> @Result state T -> Prop :=
  | ExecRead : 
      forall d a v,
        read d a = Some v ->
        exec [Cont] d (Read a) (Finished d v)
             
  | ExecWrite :
      forall d a v,
        read d a <> None ->
        exec [Cont] d (Write a v) (Finished (write d a v) tt)
             
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
        exec o1 d1 (Bind p1 p2) (Crashed d1')

  | ExecReadFail : 
      forall d a,
        read d a = None ->
        exec [Cont] d (Read a) (Failed d)
             
  | ExecWriteFail :
      forall d a v,
        read d a = None ->
        exec [Cont] d (Write a v) (Failed d)

  | ExecBindFail :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o st st1,
        exec o st p1 (Failed st1) ->
        exec o st (Bind p1 p2) (Failed st1).

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
          o2 = []) /\
      (forall s',
          exec o1 s p1 (Failed s') ->
          o2 = [])
    | _ =>
      o = [Cont] \/ o = [Crash]
    end.

  (*
  Variable op : Type -> Type.
  Inductive prog' : Type -> Type :=
  | Ret' : forall T, T -> prog' T
  | Bind' : forall T T', op T -> (T -> prog' T') -> prog' T'.

  Fixpoint bind {T1} (p1 : prog' T1): forall T2, (T1 -> prog' T2) -> prog' T2 :=
    match p1 with
    | Ret' x =>
      fun T p2 => p2 x
    | Bind' o px =>
      fun T p2 => Bind' o (fun x => bind (px x) p2)
    end.
   *)
  
End Layer1.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
Hint Constructors exec.
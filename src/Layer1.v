Require Import Streams BaseTypes Memx.
Require Import CommonAutomation Disk Simulation.

Set Implicit Arguments.

Section Layer1.

  Inductive token :=
  | Crash : token
  | Cont : token.

  Definition token_dec : forall (t t': token), {t=t'}+{t<>t'}. decide equality. Defined.

  Definition oracle := Stream token.

  Definition state := disk (set value).
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog value
  | Write : addr -> value -> prog unit
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
  Inductive exec :
    forall T, oracle ->  state -> prog T -> oracle -> @Result state T -> Prop :=
  | ExecRead : 
      forall o' d a v,
        read d a = Some v ->
        exec (Cons Cont o') d (Read a) o' (Finished d v)
             
  | ExecWrite :
      forall o' d a v,
        read d a <> None ->
        exec (Cons Cont o') d (Write a v) o' (Finished (write d a v) tt)
             
  | ExecRet :
      forall d T (v: T) o',
        exec (Cons Cont o') d (Ret v) o' (Finished d v)

  | ExecBind :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 o1' d1 d1' o2 r ret,
        exec o1 d1 p1 o1' (Finished d1' r) ->
        exec o1' d1' (p2 r) o2 ret ->
        exec o1 d1 (Bind p1 p2) o2 ret

  | ExecOpCrash :
      forall T o' d (p: prog T),
        (forall T' (p1: prog T') p2, p <> Bind p1 p2) ->
        exec (Cons Crash o') d p o' (Crashed d)
             
  | ExecBindCrash :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 o1' d1 d1',
        exec o1 d1 p1 o1' (Crashed d1') ->
        exec o1 d1 (Bind p1 p2) o1' (Crashed d1')

  | ExecBindFail :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o o' st st1,
        exec o st p1 o' (Failed st1) ->
        exec o st (Bind p1 p2) o' (Failed st1).
  (* TODO: add Failed cases *) 
End Layer1.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
Hint Constructors exec.
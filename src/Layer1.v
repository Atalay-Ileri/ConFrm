Require Import List BaseTypes Memx CommonAutomation Disk Simulation.
Import ListNotations.

Set Implicit Arguments.

Section Layer1.

  Inductive token :=
  | Crash : token
  | Cont : token.

  Definition state := disk (set value).
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog value
  | Write : addr -> value -> prog unit
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
  Inductive exec :
    forall T, oracle token ->  state -> prog T -> @Result state T -> Prop :=
  | ExecRead : 
      forall o d a v,
        o = [Cont] ->
        read d a = Some v ->
        exec o d (Read a) (Finished d v)
             
  | ExecWrite :
      forall o d a v,
        o = [Cont] ->
        read d a <> None ->
        exec o d (Write a v) (Finished (write d a v) tt)
             
  | ExecRet :
      forall o d T (v: T),
        o = [Cont] ->
        exec o d (Ret v) (Finished d v)

  | ExecBind :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 d1 d1' o2 r ret,
        exec o1 d1 p1 (Finished d1' r) ->
        exec o2 d1' (p2 r) ret ->
        exec (o1++o2) d1 (Bind p1 p2) ret

  | ExecReadCrash :
      forall o d a,
        o = [Crash] ->
        exec o d (Read a) (Crashed d)
             
  | ExecWriteCrash :
      forall o d a v,
        o = [Crash] ->
        exec o d (Write a v) (Crashed d)
             
  | ExecRetCrash :
      forall o d T (v: T),
        o = [Crash] ->
        exec o d (Ret v) (Crashed d)
             
  | ExecBindCrash :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 d1 d1',
        exec o1 d1 p1 (Crashed d1') ->
        exec o1 d1 (Bind p1 p2) (Crashed d1')

  | ExecBindFail :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o st st1,
        exec o st p1 (Failed st1) ->
        exec o st (Bind p1 p2) (Failed st1).
  (* TODO: add Failed cases *)
  
End Layer1.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
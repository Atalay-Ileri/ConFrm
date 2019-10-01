Require Import Primitives Disk Simulation.
Require Import Layer1 BlockAllocator.
Require Import Omega FunctionalExtensionality Memx.
Import ListNotations.
Close Scope pred_scope.
Set Implicit Arguments.

Section Layer2.

  Inductive token:=
  | BlockNum : addr -> token
  | DiskFull : token
  | Cont : token
  | Crash : token.

  Record oracle :=
    {
      token_list : list token;
      refinement_length : nat;
    }.
    
  Definition state := disk value.
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog (option value)
  | Write : addr -> value -> prog (option unit)
  | Alloc : value -> prog (option addr)
  | Free : addr -> prog unit
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
  Inductive exec :
    forall T, oracle -> state -> prog T -> @Result state T -> Prop :=
  | ExecRead : 
      forall o d a,
        token_list o = [Cont] ->
        exec o d (Read a) (Finished d (d a))
             
  | ExecWriteSucc :
      forall o d a v,
        token_list o = [Cont] ->
        d a <> None ->
        exec o d (Write a v) (Finished (upd d a v) (Some tt))

  | ExecWriteFail :
      forall o d a v,
        token_list o = [Cont] ->
        d a = None ->
        exec o d (Write a v) (Finished d None)

  | ExecAllocSucc :
      forall o d a v,
        token_list o = [BlockNum a] ->
        d a = None ->
        exec o d (Alloc v) (Finished (upd d a v) (Some a))

  | ExecAllocFail :
      forall o d v,
        token_list o = [DiskFull] ->
        exec o d (Alloc v) (Finished d None)

  | ExecFree :
      forall o d a,
        token_list o = [Cont] ->
        exec o d (Free a) (Finished (delete d a) tt)
             
  | ExecRet :
      forall o d T (v: T),
        token_list o = [Cont] ->
        exec o d (Ret v) (Finished d v)

  | ExecBind :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 o2 d d1 r ret,
        exec o1 d p1 (Finished d1 r) ->
        exec o2 d1 (p2 r) ret ->
        exec {| token_list := token_list o1 ++ token_list o2;
                refinement_length := refinement_length o1 + refinement_length o2; |} d (Bind p1 p2) ret
             
  | ExecOpCrash :
      forall T (p: prog T) o d,
        token_list o = [Crash] ->
        (forall T1 (p1: prog T1) p2, p <> Bind p1 p2) ->
        exec o d p (Crashed d)
             
  | ExecBindCrash :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o d d1,
        exec o d p1 (Crashed d1) ->
        exec o d (Bind p1 p2) (Crashed d1)

  | ExecBindFail :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o d d1,
        exec o d p1 (Failed d1) ->
        exec o d (Bind p1 p2) (Failed d1).
  (* TODO: add Failed cases *)
  
End Layer2.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).

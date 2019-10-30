Require Import Primitives Simulation Layer1.
Require Import Omega FunctionalExtensionality.
Import ListNotations.
Close Scope pred_scope.
Set Implicit Arguments.

Section Layer2.

  Inductive token:=
  | BlockNum : addr -> token
  | DiskFull : token
  | Cont : token
  | Crash1 : token
  | Crash2 : token
  | CrashAlloc: addr -> token.

  Definition oracle := list token.
    
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
      forall d a,
        exec [Cont] d (Read a) (Finished d (d a))
             
  | ExecWriteSucc :
      forall d a v,
        d a <> None ->
        exec [Cont] d (Write a v) (Finished (upd d a v) (Some tt))

  | ExecWriteFail :
      forall d a v,
        d a = None ->
        exec [Cont] d (Write a v) (Finished d None)

  | ExecAllocSucc :
      forall d a v,
        d a = None ->
        exec [BlockNum a] d (Alloc v) (Finished (upd d a v) (Some a))

  | ExecAllocFail :
      forall d v,
        exec [DiskFull] d (Alloc v) (Finished d None)

  | ExecFree :
      forall d a,
        exec [Cont] d (Free a) (Finished (delete d a) tt)
             
  | ExecRet :
      forall d T (v: T),
        exec [Cont] d (Ret v) (Finished d v)

  | ExecBind :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 o2 d d1 r ret,
        exec o1 d p1 (Finished d1 r) ->
        exec o2 d1 (p2 r) ret ->
        exec (o1 ++ o2) d (Bind p1 p2) ret
             
  | ExecReadCrash :
      forall d a,
        exec [Crash1] d (Read a) (Crashed d)

  | ExecWriteCrashBefore :
      forall d a v,
        exec [Crash1] d (Write a v) (Crashed d)

  | ExecWriteCrashAfter :
      forall d a v,
        exec [Crash2] d (Write a v) (Crashed (upd d a v))

  | ExecAllocCrashBefore :
      forall d v,
        exec [Crash1] d (Alloc v) (Crashed d)

  | ExecAllocCrashAfter :
      forall d a v,
        d a = None ->
        exec [CrashAlloc a] d (Alloc v) (Crashed (upd d a v))
             
  | ExecFreeCrashBefore :
      forall d a,
        exec [Crash1] d (Free a) (Crashed d)

  | ExecFreeCrashAfter :
      forall d a,
        exec [Crash2] d (Free a) (Crashed (delete d a))
             
  | ExecRetCrash :
      forall T d (a: T),
        exec [Crash1] d (Ret a) (Crashed d)
             
  | ExecBindCrash :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o d d1,
        exec o d p1 (Crashed d1) ->
        exec o d (Bind p1 p2) (Crashed d1)
.

  Definition layer2_lts := Build_LTS oracle state prog exec.
  
End Layer2.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
Hint Constructors exec.
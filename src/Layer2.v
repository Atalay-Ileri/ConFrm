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

  Definition oracle := list token.
  
  Definition state := (oracle * (disk value))%type.
  Definition get_oracle (st: state) := fst st.
  Definition get_disk (st: state) := snd st.
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog (option value)
  | Write : addr -> value -> prog (option unit)
  | Alloc : value -> prog (option addr)
  | Free : addr -> prog unit
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
  Inductive exec :
    forall T, state -> prog T -> @Result state T -> Prop :=
  | ExecRead : 
      forall st o' a,
        let o := fst st in
        let d := snd st in
        o = Cont::o' ->
        exec st (Read a) (Finished (o', d) (d a))
             
  | ExecWriteSucc :
      forall st o' a v,
        let o := fst st in
        let d := snd st in
        o = Cont::o' ->
        d a <> None ->
        exec st (Write a v) (Finished (o', (upd d a v)) (Some tt))

  | ExecWriteFail :
      forall st o' a v,
        let o := fst st in
        let d := snd st in
        o = Cont::o' ->
        d a = None ->
        exec st (Write a v) (Finished (o', d) None)

  | ExecAllocSucc :
      forall st o' a v,
        let o := fst st in
        let d := snd st in
        o = BlockNum a::o' ->
        d a = None ->
        exec st (Alloc v) (Finished (o', (upd d a v)) (Some a))

  | ExecAllocFail :
      forall st o' v,
        let o := fst st in
        let d := snd st in
        o = DiskFull::o' ->
        exec st (Alloc v) (Finished (o', d) None)

  | ExecFree :
      forall st o' a,
        let o := fst st in
        let d := snd st in
        o = Cont::o' ->
        exec st (Free a) (Finished (o', (delete d a)) tt)
             
  | ExecRet :
      forall st o' T (v: T),
        let o := fst st in
        let d := snd st in
        o = Cont::o' ->
        exec st (Ret v) (Finished (o', d) v)

  | ExecBind :
      forall T T' (p1: prog T) (p2: T -> prog T')
        st st1 r ret,
        exec st p1 (Finished st1 r) ->
        exec st1 (p2 r) ret ->
        exec st (Bind p1 p2) ret
             
  | ExecOpCrash :
      forall T st o' (p: prog T),
        let o := fst st in
        let d := snd st in
        o = Crash::o' ->
        (forall T1 (p1: prog T1) p2, p <> Bind p1 p2) ->
        exec st p (Crashed (o', d))
             
  | ExecBindCrash :
      forall T T' (p1: prog T) (p2: T -> prog T')
        st st1,
        exec st p1 (Crashed st1) ->
        exec st (Bind p1 p2) (Crashed st1)

  | ExecBindFail :
      forall T T' (p1: prog T) (p2: T -> prog T')
        st st1,
        exec st p1 (Failed st1) ->
        exec st (Bind p1 p2) (Failed st1).
  (* TODO: add Failed cases *)
  
End Layer2.

Notation "x <- p1 ;; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).

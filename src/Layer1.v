Require Import List BaseTypes Memx CommonAutomation Disk Simulation.
Import ListNotations.

Set Implicit Arguments.

Section Layer1.

  Definition state := (oracle * (disk (set value)))%type.
  Definition get_oracle (st: state) := fst st.
  Definition get_disk (st: state) := snd st.
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog value
  | Write : addr -> value -> prog unit
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
  Inductive exec :
    forall T, state -> prog T -> @Result state T -> Prop :=
  | ExecRead : 
      forall st o' a v,
        let o := fst st in
        let d := snd st in
        o = Cont::o' ->
        read d a = Some v ->
        exec st (Read a) (Finished (o', d) v)
             
  | ExecWrite :
      forall st o' a v,
        let o := fst st in
        let d := snd st in
        o = Cont::o' ->
        read d a <> None ->
        exec st (Write a v) (Finished (o', (write d a v)) tt)
             
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

  | ExecReadCrash :
      forall st o' a,
        let o := fst st in
        let d := snd st in
        o = Crash::o' ->
        exec st (Read a) (Crashed (o', d))
             
  | ExecWriteCrash :
      forall st o' a v,
        let o := fst st in
        let d := snd st in
        o = Crash::o' ->
        exec st (Write a v) (Crashed (o', d))
             
  | ExecRetCrash :
      forall st o' T (v: T),
        let o := fst st in
        let d := snd st in
        o = Crash::o' ->
        exec st (Ret v) (Crashed (o', d))
             
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
  
End Layer1.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
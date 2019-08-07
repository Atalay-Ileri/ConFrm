Require Import Primitives Simulation Confidentiality.
Require Import SimpleDisk Omega FunctionalExtensionality.
Import ListNotations.
Close Scope pred_scope.
Set Implicit Arguments.

Section ProgLimited.

  Inductive prog_limited : Type -> Type :=
  | Alloc : prog_limited (option addr)
  | Free : addr -> prog_limited unit
  | Read : addr -> prog_limited (option handle)
  | Write : addr -> handle -> prog_limited (option unit)
  | Ret : forall T, T -> prog_limited T
  | Bind : forall T T', prog_limited T -> (T -> prog_limited T') -> prog_limited T'.

  Fixpoint prog_limited_to_prog {T} (p: prog_limited T) : prog T :=
    match p with
    | Alloc => alloc
    | Free a => free a
    | Read a => read a
    | Write a h => write a h
    | Ret v => Prog.Ret v
    | Bind p1 p2 => Prog.Bind (prog_limited_to_prog p1) (fun x => prog_limited_to_prog (p2 x))
    end.
  
  Inductive exec_limited :
    forall T, state -> prog_limited T -> @Result state T -> Prop :=
  | ExecLimited :
      forall T (p: prog_limited T) st1 st2 tr,
      exec st1 (prog_limited_to_prog p) st2 tr ->
      exec_limited st1 p st2.

  Definition prog_limited_LTS := {| State:= state; Op:= prog_limited; transition := exec_limited |}.
  
  Definition state_noninterference {T} (p: prog_limited T) (valid: state -> Prop):=
  forall viewer st1 st1' st2,
    valid st1 ->
    valid st2 ->
    exec_limited st1 p st1' ->
    state_equivalent_for viewer st1 st2 ->
    exists st2',
      exec_limited st2 p st2' /\
      return_state_equivalent_for viewer st1' st2'.

  Definition ret_noninterference {T} (p: prog_limited T) (valid: state -> Prop) :=
    forall st1 st1' st2,
    valid st1 ->
    valid st2 ->
    exec_limited st1 p st1' ->
    state_equivalent_for (get_user st1) st1 st2 ->
    exists st2',
      exec_limited st2 p st2' /\
      return_equivalent_for (get_user st1) st1' st2'.

  Definition data_noninterference {T} (p: prog_limited T) (valid: state -> Prop) :=
    state_noninterference p valid /\
    ret_noninterference p valid.
  
End ProgLimited.


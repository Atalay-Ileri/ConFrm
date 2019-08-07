Require Import Primitives Simulation Confidentiality.
Require Import SimpleDisk Omega FunctionalExtensionality.
Require Import ProgLimited.
Import ListNotations.
Close Scope pred_scope.
Set Implicit Arguments.

Section Layer2.
(*
  Definition disk2 := @mem addr addr_dec sealed_value.
  Definition state2 := (user * oracle * disk2 * store)%type.
  Definition get_user (st: state2) := fst (fst (fst st)).
  Definition get_oracle (st: state2) := snd (fst (fst st)).
  Definition get_disk (st: state2) := snd (fst st).
  Definition get_store (st: state2) := snd st.
  *)
  Inductive exec2 :
    forall T, state -> prog_limited T -> @Result state T -> Prop :=
  | Exec2Finished :
      forall T (p: prog_limited T) u o d dh s o' d' dh' s' r,
      exec_limited (u, o, d, s) p (Finished (u, o', d', s') r) ->
      rep dh d ->
      rep dh' d' ->
      exec2 (u, o, dh, s) p (Finished (u, o', dh', s') r)
  | Exec2Crashed :
      forall T (p: prog_limited T) u o d dh s o' d' dh' s',
      exec_limited (u, o, d, s) p (Crashed (u, o', d', s')) ->
      rep dh d ->
      rep dh' d' ->
      exec2 (u, o, dh, s) p (Crashed (u, o', dh', s')).

  Definition prog2_LTS := {| State:= state; Op:= prog_limited; transition := exec2 |}.

  (*
  Definition state_equivalent_for u (st1 st2: state2) :=
  let '(u1, o1, d1, s1) := st1 in
  let '(u2, o2, d2, s2) := st2 in
  u1 = u2 /\
  o1 = o2 /\
  @equivalent_for _ addr_dec _ u d1 d2 /\
  @equivalent_for _ handle_dec _ u s1 s2.

  Definition return_equivalent_for {T} u (ret1 ret2: @Result state2 T) :=
    match ret1, ret2 with
    |Finished st1 r1, Finished st2 r2 =>
     state_equivalent_for u st1 st2 /\ r1 = r2
    |Crashed st1, Crashed st2 =>
     state_equivalent_for u st1 st2
    |_, _ => False
    end.
  
  Definition return_state_equivalent_for {T} u (ret1 ret2: @Result state2 T) :=
    match ret1, ret2 with
    |Finished s1' _, Finished s2' _
    |Crashed s1', Crashed s2' =>
     state_equivalent_for u s1' s2'
    | _, _ => False
    end.
   *)
  
  Definition state_noninterference {T} (p: prog_limited T) (valid: state -> Prop):=
  forall viewer st1 st1' st2,
    valid st1 ->
    valid st2 ->
    exec2 st1 p st1' ->
    state_equivalent_for viewer st1 st2 ->
    exists st2',
      exec2 st2 p st2' /\
      return_state_equivalent_for viewer st1' st2'.

  Definition ret_noninterference {T} (p: prog_limited T) (valid: state -> Prop) :=
    forall st1 st1' st2,
    valid st1 ->
    valid st2 ->
    exec2 st1 p st1' ->
    state_equivalent_for (get_user st1) st1 st2 ->
    exists st2',
      exec2 st2 p st2' /\
      return_equivalent_for (get_user st1) st1' st2'.

  Definition data_noninterference {T} (p: prog_limited T) (valid: state -> Prop) :=
    state_noninterference p valid /\
    ret_noninterference p valid.
End Layer2.

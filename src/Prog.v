Require Import List BaseTypes Memx CommonAutomation.
Require Import Confidentiality Disk Simulation.
Import ListNotations.

Set Implicit Arguments.

Section Prog.

  Definition state := (user * oracle * disk * store)%type.
  Definition get_user (st: state) := fst (fst (fst st)).
  Definition get_oracle (st: state) := snd (fst (fst st)).
  Definition get_disk (st: state) := snd (fst st).
  Definition get_store (st: state) := snd st.
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog handle
  | Write : addr -> handle -> prog unit
  
  | Auth : permission -> prog bool
  | Seal : permission -> value -> prog handle
  | Unseal : handle -> prog value
  
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.

                               
  Inductive exec :
    forall T, state -> prog T -> @Result state T -> trace -> Prop :=
  | ExecRead : 
      forall st o' a v h,
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = (Handle h)::o' ->
        s h = None ->
        read d a = Some v ->
        exec st (Read a) (Finished (u, o', d, (upd_store s h v)) h) []
             
  | ExecWrite :
      forall st o' a v h,
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = Cont::o' ->
        s h = Some v ->
        read d a <> None ->
        exec st (Write a h) (Finished (u, o, (write d a v), s) tt) []
             
  | ExecAuthSucc :
      forall st o' p,
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = Cont::o' ->
        can_access u p ->
        exec st (Auth p) (Finished (u, o, d, s) true) []

  | ExecAuthFail :
      forall st o' p,
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = Cont::o' ->
        ~can_access u p ->
        exec st (Auth p) (Finished (u, o, d, s) false) []

  | ExecSeal :
      forall st o' p v h,
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = (Handle h)::o' ->
        s h = None ->
        exec st (Seal p v) (Finished (u, o', d, (upd_store s h (p, v))) h) []

  | ExecUnseal :
      forall st o' v h,
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = Cont::o' ->
        s h = Some v ->
        exec st (Unseal h) (Finished (u, o, d, s) (snd v)) [Uns u (fst v)]

  | ExecRet :
      forall st o' T (v: T),
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = Cont::o' ->
        exec st (Ret v) (Finished (u, o, d, s) v) []

  | ExecBind :
      forall T T' (p1: prog T) (p2: T -> prog T')
        st st1 r tr1 ret tr2,
        exec st p1 (Finished st1 r) tr1 ->
        exec st1 (p2 r) ret tr2 ->
        exec st (Bind p1 p2) ret (tr1++tr2)

  | ExecReadCrash :
      forall st o' a,
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = Crash::o' ->
        exec st (Read a) (Crashed (u, o', d, s)) []
             
  | ExecWriteCrash :
      forall st o' a h,
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = Crash::o' ->
        exec st (Write a h) (Crashed (u, o', d, s)) []
             
  | ExecAuthCrash :
      forall st o' p,
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = Crash::o' ->
        exec st (Auth p) (Crashed (u, o', d, s)) []
             
  | ExecSealCrash :
      forall st o' p v,
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = Crash::o' ->
        exec st (Seal p v) (Crashed (u, o', d, s)) []
             
  | ExecUnsealCrash :
      forall st o' h,
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = Crash::o' ->
        exec st (Unseal h) (Crashed (u, o', d, s)) []
             
  | ExecRetCrash :
      forall st o' T (v: T),
        let u := fst (fst (fst st)) in
        let o := snd (fst (fst st)) in
        let d := snd (fst st) in
        let s := snd st in
        o = Crash::o' ->
        exec st (Ret v) (Crashed (u, o', d, s)) []
             
  | ExecBindCrash :
      forall T T' (p1: prog T) (p2: T -> prog T')
        st st1 tr1,
        exec st p1 (Crashed st1) tr1 ->
        exec st (Bind p1 p2) (Crashed st1) tr1.


  Inductive exec_lts :
    forall T, state -> prog T -> @Result state T -> Prop :=
  | Exec : 
      forall T (p: prog T) st st' tr,
        exec st p st' tr ->
        exec_lts st p st'.

  Definition prog_LTS := {| State:= state; Op:= prog; transition := exec_lts |}.
  

  Definition state_equivalent_for u (st1 st2: state) :=
  let '(u1, o1, d1, s1) := st1 in
  let '(u2, o2, d2, s2) := st2 in
  u1 = u2 /\
  o1 = o2 /\
  @equivalent_for_fst _ addr_dec _ u d1 d2 /\
  @equivalent_for _ handle_dec _ u s1 s2.

  Definition return_equivalent_for {T} u (ret1 ret2: @Result state T) :=
    match ret1, ret2 with
    |Finished st1 r1, Finished st2 r2 =>
     state_equivalent_for u st1 st2 /\ r1 = r2
    |Crashed st1, Crashed st2 =>
     state_equivalent_for u st1 st2
    |_, _ => False
    end.
  
  Definition return_state_equivalent_for {T} u (ret1 ret2: @Result state T) :=
    match ret1, ret2 with
    |Finished s1' _, Finished s2' _
    |Crashed s1', Crashed s2' =>
     state_equivalent_for u s1' s2'
    | _, _ => False
    end.
  
  Definition state_noninterference {T} (p: prog T) (valid: state -> Prop):=
    forall viewer st1 st1' st2 tr,
      valid st1 ->
      (* valid st2 -> *)
      exec st1 p st1' tr ->
      state_equivalent_for viewer st1 st2 ->
      exists st2' tr2,
        exec st2 p st2' tr2 /\
        return_state_equivalent_for viewer st1' st2'.

  Definition ret_noninterference {T} (p: prog T) (valid: state -> Prop):=
    forall st1 st1' st2 tr,
      valid st1 ->
      (* valid st2 -> *)
      exec st1 p st1' tr ->
      state_equivalent_for (get_user st1) st1 st2 ->
    exists st2',
      exec st2 p st2' tr /\
      return_equivalent_for (get_user st1) st1' st2'.

  Definition data_noninterference {T} (p: prog T) (valid: state -> Prop) :=
    state_noninterference p valid /\
    ret_noninterference p valid.
  
End Prog.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
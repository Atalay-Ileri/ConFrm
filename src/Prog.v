Require Import List BaseTypes Memx Disk.
Import ListNotations.

Set Implicit Arguments.

Section Prog.
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog handle
  | Write : addr -> handle -> prog unit
  
  | Auth : permission -> prog bool
  | Seal : permission -> value -> prog handle
  | Unseal : handle -> prog value
  
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.

  Inductive result : Type -> Type :=
  | Finished : forall T, oracle -> disk -> store -> T -> result T
  | Crashed : forall T, oracle -> disk -> store -> result T.
                               
  Inductive exec :
    forall T, user -> oracle -> disk -> store -> prog T -> result T -> trace -> Prop :=
  | ExecRead : 
      forall u o o' d s a v h,
        o = (Handle h)::o' ->
        s h = None ->
        read d a = Some v ->
        exec u o d s (Read a) (Finished o' d (upd_store s h v) h) []
             
  | ExecWrite :
      forall u o o' d s a v h,
        o = Cont::o' ->
        s h = Some v ->
        read d a <> None ->
        exec u o d s (Write a h) (Finished o (write d a v) s tt) []
             
  | ExecAuthSucc :
      forall u o o' d s p,
        o = Cont::o' ->
        can_access u p ->
        exec u o d s (Auth p) (Finished o d s true) []

  | ExecAuthFail :
      forall u o o' d s p,
        o = Cont::o' ->
        ~can_access u p ->
        exec u o d s (Auth p) (Finished o d s false) []

  | ExecSeal :
      forall u o o' d s p v h,
        o = (Handle h)::o' ->
        s h = None ->
        exec u o d s (Seal p v) (Finished o' d (upd_store s h (p, v)) h) []

  | ExecUnseal :
      forall u o o' d s v h,
        o = Cont::o' ->
        s h = Some v ->
        exec u o d s (Unseal h) (Finished o d s (snd v)) [Uns u (fst v)]

  | ExecRet :
      forall T u o o' d s (v: T),
        o = Cont::o' ->
        exec u o d s (Ret v) (Finished o d s v) []

  | ExecBind :
      forall T T' (p1: prog T) (p2: T -> prog T')
        u o d s o1 d1 s1 r tr1 ret tr2,
        exec u o d s p1 (Finished o1 d1 s1 r) tr1 ->
        exec u o1 d1 s1 (p2 r) ret tr2 ->
        exec u o d s (Bind p1 p2) ret (tr1++tr2)

  | ExecReadCrash :
      forall u o d s o' a,
        o = Crash::o' ->
        exec u o d s (Read a) (Crashed _ o' d s) []
             
  | ExecWriteCrash :
      forall u o d s o' a h,
        o = Crash::o' ->
        exec u o d s (Write a h) (Crashed _ o' d s) []
             
  | ExecAuthCrash :
      forall u o d s o' p,
        o = Crash::o' ->
        exec u o d s (Auth p) (Crashed _ o' d s) []
             
  | ExecSealCrash :
      forall u o d s o' p v,
        o = Crash::o' ->
        exec u o d s (Seal p v) (Crashed _ o' d s) []
             
  | ExecUnsealCrash :
      forall u o d s o' h,
        o = Crash::o' ->
        exec u o d s (Unseal h) (Crashed _ o' d s) []
             
  | ExecRetCrash :
      forall T u o d s o' (v: T),
        o = Crash::o' ->
        exec u o d s (Ret v) (Crashed _ o' d s) []
             
  | ExecBindCrash :
      forall T T' (p1: prog T) (p2: T -> prog T')
        u o d s o1 d1 s1 tr1,
        exec u o d s p1 (Crashed _ o1 d1 s1) tr1 ->
        exec u o d s (Bind p1 p2) (Crashed _ o1 d1 s1) tr1.

  
End Prog.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
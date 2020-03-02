Require Import Primitives Simulation DiskLayer CacheLayer.
Close Scope pred_scope.
Import ListNotations.

Set Implicit Arguments.
  
Section CachedDiskLayer.  
  
  Inductive token :=
  | DiskOracle : DiskLayer.oracle -> token
  | CacheOracle : CacheLayer.oracle -> token
  | Cont : token
  | Crash : token.

  Definition token_dec : forall (t t': token), {t=t'}+{t<>t'}.
    repeat decide equality.
    apply key_dec.
  Defined.

  Definition oracle := list token.  

  (* Had  to put unit as aux_state to make it compliant to the structure of the rest *)
  Definition state := (unit * (DiskLayer.state * CacheLayer.state))%type.
  
  Inductive prog : Type -> Type :=
  | DiskProg : forall T, DiskLayer.prog T -> prog T
  | CacheProg : forall T, CacheLayer.prog T -> prog T
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
  Inductive exec :
    forall T, oracle ->  state -> prog T -> @Result state T -> Prop :=
  | ExecDiskProg : 
      forall T (p : DiskLayer.prog T) x d c o d' r,
        DiskLayer.exec o d p (Finished d' r) ->
        exec [DiskOracle o] (x, (d, c)) (DiskProg p) (Finished (x, (d', c)) r)

  | ExecCacheProg : 
      forall T (p : CacheLayer.prog T) x d c o c' r,
        CacheLayer.exec o c p (Finished c' r) ->
        exec [CacheOracle o] (x, (d, c)) (CacheProg p) (Finished (x, (d, c')) r)

  | ExecRet :
      forall d T (v: T),
        exec [Cont] d (Ret v) (Finished d v)

  | ExecBind :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 d1 d1' o2 r ret,
        exec o1 d1 p1 (Finished d1' r) ->
        exec o2 d1' (p2 r) ret ->
        exec (o1++o2) d1 (Bind p1 p2) ret

  | ExecRetCrash :
      forall T d (v: T),
        exec [Crash] d (Ret v) (Crashed d)

  | ExecDiskProgCrash : 
      forall T (p : DiskLayer.prog T) x d c o d',
        DiskLayer.exec o d p (Crashed d') ->
        exec [DiskOracle o] (x, (d, c)) (DiskProg p) (Crashed (x, (d', c)))

  | ExecCacheProgCrash : 
      forall T (p : CacheLayer.prog T) x d c o c',
        CacheLayer.exec o c p (Crashed c') ->
        exec [CacheOracle o] (x, (d, c)) (CacheProg p) (Crashed (x, (d, c')))
             
  | ExecBindCrash :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 d1 d1',
        exec o1 d1 p1 (Crashed d1') ->
        exec o1 d1 (Bind p1 p2) (Crashed d1').

  Fixpoint oracle_ok {T} (p: prog T) o s :=
    match p with
    | Bind p1 p2 =>
      exists o1 o2,
      o = o1++o2 /\
      oracle_ok p1 o1 s /\
      (forall s' r,
          exec o1 s p1 (Finished s' r) ->
          oracle_ok (p2 r) o2 s') /\
      (forall s',
          exec o1 s p1 (Crashed s') ->
          o2 = [])
    | DiskProg p  =>
      exists o',
      o = [DiskOracle o'] /\
      DiskLayer.oracle_ok p o' (fst (snd s))
    | CacheProg p =>
      exists o',
      o = [CacheOracle o'] /\
      CacheLayer.oracle_ok p o' (snd (snd s))
    | Ret _ =>
      o = [Cont] \/ o = [Crash]
    end.

  Definition cached_disk_layer_lts := Build_LTS oracle state prog exec.
End CachedDiskLayer.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
Hint Constructors exec.
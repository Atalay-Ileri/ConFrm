Inductive prog_get_block : Type -> Type :=
| L0 : forall T, L0.prog T -> prog_get_block T
| GetThenL0 : forall T, addr -> (resource -> L0.prog T) -> get_block_prog T.

(* This complicated condition states that, after running Get,
   running L0 executes successfully on all equivalent states *)
Definition runs_on_all_equivalent {T} u rs1 cs1 i p :=
    (forall u' rs r,
        equivalent u' rs1 rs ->
        rs i = Some r ->
        exists rs2 cs2 ret2,
          L0.exec u rs cs1 (p (snd r)) rs2 cs2 ret2) ->

Inductive exec:=
| ExecGetThenL0: forall T u (p: resource -> L0.prog T) rs1 cs1 rs1' cs1' i r1 ret1,
    runs_on_all_equivalent u rs1 cs1 i p ->
    rs1 i = Some r1 ->
    can_access u (fst r1) ->
    L0.exec u rs1 cs1 (p (snd r1)) rs1' cs1' ret1 ->
    exec u rs1 cs1 (GetThenL0 i p) rs1' cs1' ret1.

Inductive prog' : Type -> Type :=
| Ret' : forall T, T -> prog' T
| Bind' : forall T T', get_block_prog T -> (T -> prog' T') -> prog' T'.

Fixpoint prog'_rebind {T T'} (p1: prog' T) (p2: T -> prog' T'): prog' T' :=
  match p1 with
  | Ret' t => p2 t
  | Bind' gbp p' => Bind' gbp (fun x => prog'_rebind (p' x) p2)
  end.

Inductive prog : Type -> Type :=
| GetBlock : forall T, get_block_prog T -> prog T
| Ret : forall T, T -> prog T
| Bind : forall T T', prog T -> (T -> prog T') -> prog T'.


Fixpoint prog'2prog {T} (p: prog' T) : prog T :=
  match p with
  | Ret' t => Ret t
  | Bind' gbp p' => Bind (GetBlock gbp) (fun x => prog'2prog (p' x))
  end.

Fixpoint prog2prog' {T} (p: prog T) : prog' T :=
  match p with
  | Ret t => Ret' t
  | GetBlock gbp => Bind' gbp (fun x => Ret' x)
  | Bind p1 p2 => prog'_rebind (prog2prog' p1) (fun x => prog2prog' (p' x))
  end.


Theorem DNI_holds:
  forall T (p: prog' T), data_noninterference p.

(* Can there be states that is stuck indefinitely for some users? For all users? *)
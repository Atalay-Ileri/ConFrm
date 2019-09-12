Require Import Primitives Layer1 BlockAllocator Layer2.

Section Layer1to2Refinement.
  
  Fixpoint prog2to1 {T} (p1: Layer2.prog T) : Layer1.prog T :=
    match p1 with
    | Read a => read a
    | Write a v => write a v
    | Alloc v => alloc v
    | Free a => free a
    | Ret v => Layer1.Ret v
    | Bind px py => Layer1.Bind (prog2to1 px) (fun x => prog2to1 (py x))
    end.
  
  Fixpoint oracle_matches {T} (st1: Layer1.state) (o2: Layer2.oracle) (p: Layer2.prog T) :=
    match p with
    | Alloc v =>
      forall o1' d1',
        (Layer1.exec st1 (prog2to1 (Alloc v)) (Crashed (o1', d1')) ->
         o2 = [Crash]) /\
        (forall r, Layer1.exec st1 (prog2to1 (Alloc v)) (Finished (o1', d1') r) ->
         match r with
         | Some a =>
           o2 = [BlockNum a]
         | None =>
           o2 = [DiskFull]
         end)
    | Bind p1 p2 =>
       forall o1' d1',
        (Layer1.exec st1 (prog2to1 p1) (Crashed (o1', d1')) ->
         o2 = [Crash]) /\
        (forall r o2' o2'',
            Layer1.exec st1 (prog2to1 p1) (Finished (o1', d1') r) ->
            oracle_matches st1 o2' p1 ->
            oracle_matches (o1', d1') o2'' (p2 r) ->
            o2 = o2'++o2'')
    | _ =>
      forall o1' d1',
        (Layer1.exec st1 (prog2to1 p) (Crashed (o1', d1')) ->
         o2 = [Crash]) /\
        (forall r, Layer1.exec st1 (prog2to1 p) (Finished (o1', d1') r) ->
         o2 = [Cont])
    end.
 
  Check oracle_matches.

  Definition refines_to {T} st1 st2 (p: Layer2.prog T) :=
    let '(o1, d1) := st1 in
    let '(o2, d2) := st2 in
    rep d2 d1 /\
    oracle_matches st1 o2 p.

  
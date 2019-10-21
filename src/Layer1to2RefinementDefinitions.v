Require Import Primitives Layer1 Layer2 BlockAllocatorDefinitions.
Close Scope pred_scope.
Import ListNotations.

Fixpoint compile {T} (p2: Layer2.prog T) : Layer1.prog T :=
    match p2 with
    | Read a => read a
    | Write a v => write a v
    | Alloc v => alloc v
    | Free a => free a
    | Ret v => Layer1.Ret v
    | Bind px py => Layer1.Bind (compile px) (fun x => compile (py x))
    end.

(* October 12: I need oracle_ok in here because specifications of block allocator requires it as a precondition *)
  Fixpoint oracle_refines_to T (d1: Layer1.state) (p: Layer2.prog T)  (o1: Layer1.oracle) (o2: Layer2.oracle) : Prop :=
    oracle_ok (compile p) o1 d1 /\
    match p with
    | Alloc v =>
      if (in_dec Layer1.token_dec Layer1.Crash o1) then
        forall d1',
          Layer1.exec o1 d1 (compile p) (Crashed d1') ->
          let sv := Disk.read d1 0 in
          let sv' := Disk.read d1' 0 in
          match sv, sv' with
          | Some v, Some v' =>
            (v = v' ->
             o2 = [Crash1]) /\
            (v <> v' ->
             let bits := bits (value_to_bits v) in
             let index := get_first_zero bits in
             o2 = [CrashAlloc index])
          | _, _ => False
          end
      else
        let sv := Disk.read d1 0 in
        match sv with
        | Some v =>
          let bits := bits (value_to_bits v) in
          let index := get_first_zero bits in
          
          if Compare_dec.lt_dec index block_size then
            o2 = [BlockNum index]
          else
            o2 = [DiskFull]
        | None => False
        end
    | @Bind T1 T2 p1 p2 =>
      exists o1' o1'',
      o1 = o1'++o1'' /\
      (forall d1', Layer1.exec o1 d1 (compile p1) (Crashed d1') ->
         oracle_refines_to T1 d1 p1 o1 o2 /\ o1'' = []) /\
      (forall d1' r,
         Layer1.exec o1' d1 (compile p1) (Finished d1' r) ->
         exists o2' o2'',
         oracle_refines_to T1 d1 p1 o1' o2' /\
         oracle_refines_to T2 d1' (p2 r) o1'' o2'' /\
         o2 = o2' ++ o2'')
    | Read _ =>
      if (in_dec Layer1.token_dec Layer1.Crash o1) then
        o2 = [Crash1]
      else
        o2 = [Cont]
    | Ret _ =>
      if (in_dec Layer1.token_dec Layer1.Crash o1) then
        o2 = [Crash1]
      else
        o2 = [Cont]
    | Free _ =>
      if (in_dec Layer1.token_dec Layer1.Crash o1) then
        o2 = [Crash1]
      else
        o2 = [Cont]
    | Write a _ =>
      if (in_dec Layer1.token_dec Layer1.Crash o1) then
         forall d1',
          Layer1.exec o1 d1 (compile p) (Crashed d1') ->
          let sv := d1 a in
          let sv' := d1' a in
          match sv, sv' with
          | Some v, Some v' =>
            (v = v' ->
             o2 = [Crash1]) /\
            (v <> v' ->
             o2 = [Crash2])
          | _, _ => False
          end
      else
        o2 = [Cont]
    end.

  Definition refines_to d1 d2 :=
    exists F, (F * rep d2)%pred d1.

  Definition compilation_of T p1 p2 :=
    p1 = @compile T p2.
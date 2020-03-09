Require Import List Mem BaseTypes.
Import ListNotations.

Set Implicit Arguments.

Section Disk.
  (* maybe rename better *)
  Definition set V := (V * list V)%type.

  Definition set_dec {V} (value_dec : forall (v v': V),{v=v'}+{v<>v'}): forall s s': set V, {s=s'}+{s<>s'}.
    decide equality.
    decide equality.
  Defined.
    
  Definition disk V := @mem addr addr_dec V.
  Definition upd_disk {V} := @upd addr V addr_dec.
  
  Definition store V := @mem handle handle_dec V.
  Definition upd_store {V} := @upd handle V handle_dec.

  

  Definition read {V} (d: disk (set V)) (a: addr) :=
    match d a with
    | None => None
    | Some vs => Some (fst vs)
    end.
  
  Definition write {V} (d: disk (set V)) (a: addr) (v: V) : disk (set V) :=
    match d a with
    | None => d
    | Some vs => upd_disk d a (v, fst vs::snd vs)
    end.


  Definition sync {V} (d: disk (set V)) (a: addr) : disk (set V) :=
    match d a with
    | None => d
    | Some vs => upd_disk d a (fst vs, [])
    end.

  (* TODO Fix this 
  Definition sync_all (d: disk) : disk := mem_read (sync d a) a.
   *)
End Disk.
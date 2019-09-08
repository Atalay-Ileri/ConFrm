Require Import List Memx BaseTypes.
Import ListNotations.

Set Implicit Arguments.

Section Disk.
  (* maybe rename better *)
  Definition set V := (V * list V)%type.
  Definition disk V := @mem addr addr_dec (set V).
  
  Definition store V := @mem handle handle_dec V.
  Definition upd_store {V} := @upd handle V handle_dec.

  Definition upd_disk {V} := @upd addr V addr_dec.

  Definition read {V} (d: disk V) (a: addr) :=
    match d a with
    | None => None
    | Some vs => Some (fst vs)
    end.
  
  Definition write {V} (d: disk V) (a: addr) (v: V) : disk V :=
    match d a with
    | None => d
    | Some vs => upd_disk d a (v, fst vs::snd vs)
    end.


  Definition sync {V} (d: disk V) (a: addr) : disk V :=
    match d a with
    | None => d
    | Some vs => upd_disk d a (fst vs, [])
    end.

  (* TODO Fix this 
  Definition sync_all (d: disk) : disk := mem_read (sync d a) a.
   *)
End Disk.
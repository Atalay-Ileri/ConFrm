Require Import List Memx BaseTypes.
Import ListNotations.

Set Implicit Arguments.

Section Disk.
  (* maybe rename better *)
  Definition set V := (V * list V)%type.
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
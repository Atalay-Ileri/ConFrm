Require Import List Memx BaseTypes.
Import ListNotations.

Set Implicit Arguments.

Section Disk.
  (* maybe rename better *)
  Definition valueset := (sealed_value * list sealed_value)%type.
  Definition disk := @mem addr addr_dec valueset.

  Definition upd_disk := @upd addr valueset addr_dec.

  Definition read (d: disk) (a: addr) :=
    match d a with
    | None => None
    | Some vs => Some (fst vs)
    end.
  
  Definition write (d: disk) (a: addr) (v: sealed_value) : disk :=
    match d a with
    | None => d
    | Some vs => upd_disk d a (v, fst vs::snd vs)
    end.


  Definition sync (d: disk) (a: addr) : disk :=
    match d a with
    | None => d
    | Some vs => upd_disk d a (fst vs, [])
    end.

  (* TODO Fix this 
  Definition sync_all (d: disk) : disk := mem_read (sync d a) a.
   *)
End Disk.

Section Store.
  
  Definition store := @mem handle handle_dec sealed_value.
  Definition upd_store := @upd handle sealed_value handle_dec.
  
End Store.
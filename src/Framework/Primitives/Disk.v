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
  
  

  Definition read {V} (d: disk (set V)) (a: addr) :=
    match d a with
    | None => None
    | Some vs => Some (fst vs)
    end.
  
  Definition write {V} (d: disk (set V)) (a: addr) (v: V) : disk (set V) :=
    match d a with
    | None => d
    | Some vs => upd d a (v, fst vs::snd vs)
    end.

  Fixpoint write_all {V} (d: disk (set V)) (la: list addr) (lv: list V) : disk (set V) :=
    match la, lv with
    | a::la', v::lv' =>
      match d a with
      | None => d
      | Some vs => write_all (upd d a (v, fst vs::snd vs)) la' lv'
      end
    | _, _ => d
    end.

  Fixpoint write_all_to_set {V} (vl: list V) (vsl: list (set V)) :=
    match vl, vsl with
    | v::vl', vs::vsl' =>
      (v, fst vs::snd vs)::write_all_to_set vl' vsl'
    | _, _ =>
      nil
    end.

End Disk.

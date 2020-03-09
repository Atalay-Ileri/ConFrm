Require Import Datatypes PeanoNat Primitives Log.
Require Import DiskLayer CacheLayer CachedDiskLayer.
Import CachedDiskOperation CachedDiskHL.

Axiom addr_list_to_blocks : list addr -> list value.

Definition apply_log := P2 apply_log.

Fixpoint write_batch al vl :=
  match al, vl with
  | a::al', v::vl' =>
    _ <-| P1 (CacheHL.Lang.Op (Write a v));
    _ <- write_batch al' vl';
    Ret tt            
  | _, _ => Ret tt
  end.

Definition commit addr_l (data_l: list value) :=
  _ <- write_batch addr_l data_l;
  _ <-| P2 (commit (addr_list_to_blocks addr_l) data_l);
  Ret tt.

Definition read a :=
  mv <-| P1 (CacheHL.Lang.Op (Read a));
  match mv with
  | Some v =>
    Ret v
  | None =>
    v <-| P2 (DiskHL.Lang.Op (DiskLayer.Definitions.Read a));
    Ret v
  end. 
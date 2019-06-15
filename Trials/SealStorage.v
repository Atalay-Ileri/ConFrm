Require Import StorageType PolicyType MemStorage.

Set Implicit Arguments.

Record SealPrimitives (S: StoragePrimitives) (P: PolicyPrimitives) := {
  key : Type;
  value := (permission P * value S)%type;
  key_eq : forall k k' : key, {k=k'}+{k<>k'}
}.

Definition seal_primitives2storage_primitives {S P} (SP : SealPrimitives S P) :=
  Build_StoragePrimitives
    (key SP)
    (value SP)
    (key_eq SP).

Definition SealStorage {S P} (SP: SealPrimitives S P) := MemStorage (seal_primitives2storage_primitives SP).
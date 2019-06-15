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

Module PermissionStorage  <: Policy MemStorage.
  Import MemStorage.
  
  Parameter can_read : user -> storage -> key -> Prop.
  Parameter can_write : user -> storage -> key -> Prop.
  Parameter can_change : user -> storage -> key -> Prop.
  Parameter change_permission : user -> storage -> key -> user -> storage.

  Notation "s [ u 'R?' k ]" := (can_read u s k) (at level 4, u at next level): storage_scope.
  Notation "s [ u 'W?' k ]" := (can_write u s k) (at level 4, u at next level): storage_scope.
  Notation "s [ u 'C?' k ]" := (can_change u s k) (at level 4, u at next level): storage_scope.
  Notation "s < k ':=' u >" := (change_permission s k u) (at level 3, u at next level): storage_scope.















  

Module RelSec (S: Storage) (P : Policy).
  
  Module Pol := P S.
  Module SealStore := SealStorage S P.
  Import Pol SealStore S.

  Inductive prog : Type -> Type :=
  | Read : key -> prog SealStore.handle
  | Write : key -> SealStore.handle -> prog unit
  | Seal : permission -> value -> prog SealStore.handle
  | Unseal : SealStore.handle -> prog value
  | Auth : key -> prog unit
  | ChDom : key -> user -> prog unit
  | Ret : forall T, T -> prog T
  | Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.

  Inductive result {T: Type} : Type :=
  | Finished : storage -> SealStore.storage -> T -> result
  | Crashed : storage -> SealStore.storage -> result.
  
  Inductive exec:
    forall T, user -> storage -> SealStore.storage -> prog T -> @result T -> Prop :=
  | ExecRead    : forall u d bm a i bs,
      SealStore.get bm i = None ->
      d[a] = Some bs ->
      can_read u d a ->
      exec u d bm (Read a) (Finished d (SealStore.put bm i bs) i)
           
  | ExecWrite   : forall u d bm dm a i b,
      bm i = Some b ->
      d a <> None ->
      exec u d bm dm (Write a i) (Finished (update_disk d a b) bm dm tt) nil
           
  | ExecSeal : forall u d bm dm i t b,
      bm i = None ->
      dm t <> None ->
      exec u d bm dm (Seal t b) (Finished d (update_blockmem bm i (t,b)) dm i) nil
           
  | ExecUnseal : forall u d bm dm i b t,
      bm i = Some b ->
      dm (fst b) = Some t ->
      exec u d bm dm (Unseal i) (Finished d bm dm (snd b)) [Uns t]

  | ExecAuthSucc : forall u d bm dm t,
      can_access u t ->
      exec u d bm dm (Auth t) (Finished d bm dm true) nil

  | ExecAuthFail : forall u d bm dm t,
      ~can_access u t ->
      exec u d bm dm (Auth t) (Finished d bm dm false) nil

  | ExecChDom : forall u d bm dm t t' a,
      dm a = Some t' ->
      exec u d bm dm (ChDom a t) (Finished d bm (update_domainmem dm a t) tt) [Chd t' t]
           
  | ExecRet : forall T u d bm dm (r: T),
      exec u d bm dm (Ret r) (Finished d bm dm r) nil
           
  | ExecBind : forall T T' u (p1 : prog T) (p2: T -> prog T') d bm dm d' bm' dm' v r t1 t2,
      exec u d bm dm p1 (Finished d' bm' dm' v) t1 ->
      exec u d' bm' dm' (p2 v) r t2 ->
      exec u d bm dm (Bind p1 p2) r (t2++t1)

  | FailRead    : forall u d bm dm a,
      d a = None ->
      exec u d bm dm (Read a) Failed nil

  | FailWrite    : forall u d bm dm a i,
      bm i = None \/ d a = None ->
      exec u d bm dm (Write a i) Failed nil
           
  | FailUnseal : forall u d bm dm i,
      bm i = None \/ (exists b, bm i = Some b /\ dm (fst b) = None) ->
      exec u d bm dm (Unseal i) Failed nil

  | FailChDom : forall u d bm dm t a,
      dm a = None ->
      exec u d bm dm (ChDom a t) Failed nil

  | FailBind : forall T T' u (p1 : prog T) (p2: T -> prog T') d bm dm tr',
      exec u d bm dm p1 (@Failed T) tr' ->
      exec u d bm dm (Bind p1 p2) (@Failed T') tr'.
  

(* Type of the basic storage unit *)
Parameter block : Type.

(* Type for ownership *)
Parameter owner : Type.

(* Type of the basic unit stored on the disk *)
Definition sealed_block := (id * block)%type.

(* Types of storage units in the system *)
Definition disk := addr -> option sealed_block.
Definition blockmem := handle -> option sealed_block. 

(* update functions for storage units. I made them explicitly separate 
   because of the possible future changes to the structures *)
Parameter update_disk : disk -> addr -> sealed_block -> disk.
Axiom update_disk_eq: forall d a sb, update_disk d a sb a = Some sb.
Axiom update_disk_neq : forall d a a' sb, a<> a' -> update_disk d a sb a' = d a'.

Parameter update_blockmem : blockmem -> handle -> sealed_block -> blockmem.
Axiom update_blockmem_eq: forall d a sb, update_blockmem d a sb a = Some sb.
Axiom update_blockmem_neq : forall d a a' sb, a<> a' -> update_blockmem d a sb a' = d a'.

Parameter update_domainmem : domainmem -> id -> owner -> domainmem.
Axiom update_domainmem_eq: forall d a sb, update_domainmem d a sb a = Some sb.
Axiom update_domainmem_neq : forall d a a' sb, a<> a' -> update_domainmem d a sb a' = d a'.

(* Type for users in the system *)
Parameter user : Type.

(* A relation that determines what user can access *)
Parameter can_access: user -> owner -> Prop.

(* operations for traces *)
Inductive op :=
| Chd : owner -> owner -> op
| Uns : owner -> op.

Definition trace := list op.

(* Language *)
Inductive prog : Type -> Type :=
| Read : addr -> prog handle
| Write : addr -> handle -> prog unit
| Seal : id -> block -> prog handle
| Unseal : handle -> prog block
| Auth : owner -> prog bool
| ChDom : id -> owner -> prog unit
| Ret : forall T, T -> prog T
| Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.

(* result of an execution *)


(* Operational semantics *)
Inductive exec:
  forall T, user -> disk -> blockmem -> domainmem -> prog T -> @result T -> trace -> Prop :=
| ExecRead    : forall u d bm dm a i bs,
                  bm i = None ->
                  d a = Some bs ->
                  exec u d bm dm (Read a) (Finished d (update_blockmem bm i bs) dm i) nil
                       
| ExecWrite   : forall u d bm dm a i b,
                  bm i = Some b ->
                  d a <> None ->
                  exec u d bm dm (Write a i) (Finished (update_disk d a b) bm dm tt) nil
                       
| ExecSeal : forall u d bm dm i t b,
               bm i = None ->
               dm t <> None ->
               exec u d bm dm (Seal t b) (Finished d (update_blockmem bm i (t,b)) dm i) nil
                    
| ExecUnseal : forall u d bm dm i b t,
                 bm i = Some b ->
                 dm (fst b) = Some t ->
                 exec u d bm dm (Unseal i) (Finished d bm dm (snd b)) [Uns t]

| ExecAuthSucc : forall u d bm dm t,
               can_access u t ->
               exec u d bm dm (Auth t) (Finished d bm dm true) nil

| ExecAuthFail : forall u d bm dm t,
               ~can_access u t ->
               exec u d bm dm (Auth t) (Finished d bm dm false) nil

| ExecChDom : forall u d bm dm t t' a,
               dm a = Some t' ->
               exec u d bm dm (ChDom a t) (Finished d bm (update_domainmem dm a t) tt) [Chd t' t]
                    
| ExecRet : forall T u d bm dm (r: T),
              exec u d bm dm (Ret r) (Finished d bm dm r) nil
                   
| ExecBind : forall T T' u (p1 : prog T) (p2: T -> prog T') d bm dm d' bm' dm' v r t1 t2,
               exec u d bm dm p1 (Finished d' bm' dm' v) t1 ->
               exec u d' bm' dm' (p2 v) r t2 ->
               exec u d bm dm (Bind p1 p2) r (t2++t1)

| FailRead    : forall u d bm dm a,
                  d a = None ->
                  exec u d bm dm (Read a) Failed nil

| FailWrite    : forall u d bm dm a i,
                  bm i = None \/ d a = None ->
                  exec u d bm dm (Write a i) Failed nil
                    
| FailUnseal : forall u d bm dm i,
                 bm i = None \/ (exists b, bm i = Some b /\ dm (fst b) = None) ->
                 exec u d bm dm (Unseal i) Failed nil

| FailChDom : forall u d bm dm t a,
               dm a = None ->
               exec u d bm dm (ChDom a t) Failed nil

| FailBind : forall T T' u (p1 : prog T) (p2: T -> prog T') d bm dm tr',
                exec u d bm dm p1 (@Failed T) tr' ->
                exec u d bm dm (Bind p1 p2) (@Failed T') tr'.

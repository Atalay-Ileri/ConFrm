Require Import StorageType.
Open Scope storage_scope.

Set Implicit Arguments.

Definition mem_storage P := key P -> option (value P).
Definition put {P} := fun (s: mem_storage P) k v k' => if (k =? k') then Some v else s k'.
Definition get {P}:= fun (s: mem_storage P) k => s k.
Definition delete {P} := fun (s: mem_storage P) k k' => if (k =? k') then None else s k'.

Lemma get_after_put_eq:
  forall P (s: mem_storage P) k v,
    get (put s k v) k = Some v.
Proof.
  unfold put, get; intros; simpl.
  destruct (k =? k); eauto.
  intuition.
Qed.

Lemma get_after_put_ne:
  forall P (s: mem_storage P) k k' v,
    k <> k' ->
    get (put s k v) k' = get s k'.
Proof.
  unfold put, get; intros; simpl.
  destruct (k =? k'); eauto.
  intuition.
Qed.

Lemma get_after_delete_eq:
  forall P (s: mem_storage P) k,
    get (delete s k) k  = None.
Proof.
  unfold delete, get; intros; simpl.
  destruct (k =? k); eauto.
  intuition.
Qed.

Lemma get_after_delete_ne:
  forall P (s: mem_storage P) k k',
    k <> k' ->
    get (delete s k) k' = get s k'.
Proof.
  unfold delete, get; intros; simpl.
  destruct (k =? k'); eauto.
  intuition.
Qed.

Definition MemStorage (P: StoragePrimitives) : Storage P :=
  Build_Storage P
    (mem_storage P)
    put
    get
    delete
    (@get_after_put_eq P)
    (@get_after_put_ne P)
    (@get_after_delete_eq P)
    (@get_after_delete_ne P).
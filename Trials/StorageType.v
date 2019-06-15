Record StoragePrimitives := {
    key : Type;
    value : Type;
    key_eq : forall (k k': key), {k=k'}+{k<>k'}
}.

Arguments key_eq {_}.

Notation "k =? k'" := (key_eq k k') (at level 5) : storage_scope.

Record Storage (P: StoragePrimitives) := {
  storage : Type;
  put : storage -> key P -> value P -> storage;
  get : storage -> key P -> option (value P);
  delete : storage -> key P -> storage;

  get_after_put_eq:
    forall s k v,
      get (put s k v) k = Some v;
  
  get_after_put_ne:
    forall s k k' v,
      k <> k' ->
      get (put s k v) k' = get s k';
  
  get_after_delete_eq:
    forall s k,
      get (delete s k) k  = None;
  
  get_after_delete_ne:
    forall s k k',
      k <> k' ->
      get (delete s k) k' = get s k';
  }.

  Arguments get {_}.
  Arguments put {_}.
  Arguments delete {_}.
  
  Notation "s [ k ]" := (get s k) (at level 1, k at next level, left associativity): storage_scope.
  Notation "s [ k := v ]" := (put s k v) (at level 1, k at next level, left associativity): storage_scope.
  Notation "s [ k ':=' - ]" := (delete s k) (at level 1, k at next level, left associativity): storage_scope.

  (* Notation "s [ k | def ]" := (get_or_default s k def) (at level 1, k at next level, left associativity): storage_scope. *)
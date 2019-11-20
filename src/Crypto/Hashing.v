Require Import Primitives.

Module Type HashingSignature.
  Parameter hash: Type.
  Parameter data : Type.
  Parameter hash_function : hash -> data -> hash.
  Parameter hash_dec: forall h1 h2: hash, {h1=h2}+{h1<>h2}.
End HashingSignature.


Module Hashing (HS: HashingSignature).
  Import HS.
  
  Definition hashmap := @mem hash hash_dec (hash * data).

  Definition hashmap_valid (hm: hashmap) :=
    forall h hd d, hm h = Some (hd, d) -> hash_function hd d = h.
  
  Definition hashing_is_safe hdef d (hm: hashmap) :=
    let h := hash_function hdef d in
    hm h = None \/ hm h = Some (hdef, d).
End Hashing.

  
  
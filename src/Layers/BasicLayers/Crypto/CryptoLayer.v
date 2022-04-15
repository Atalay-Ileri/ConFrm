Require Import Framework.
Import ListNotations.
Import Mem.

Set Implicit Arguments.

Instance value_eq_dec: EqDec value := value_dec.
Instance hash_eq_dec: EqDec hash := hash_dec.

Definition hashmap := @mem hash hash_dec (hash * value).
Definition encryption_map:= @mem value value_dec (key * value).

  Inductive token' :=
  | Key : key -> token'
  | Crash : token'
  | Cont : token'.

  Definition state' := (list key * hashmap * encryption_map)%type.

  Inductive crypto_prog : Type -> Type :=
  | GetKey : crypto_prog key
  | Hash : hash -> value -> crypto_prog hash
  | Encrypt : key -> value -> crypto_prog value
  | Decrypt : key -> value -> crypto_prog value.
   
  Inductive exec' :
    forall T, user -> token' ->  state' -> crypto_prog T -> @Result state' T -> Prop :=

  | ExecHash : 
      forall s h v u,
        let kl := fst (fst s) in
        let hm := snd (fst s) in
        let em := snd s in
        let hv := hash_function h v in
        consistent hm hv (h, v) ->
        exec' u Cont s (Hash h v) (Finished (kl, (upd hm hv (h, v)), em) hv)
             
  | ExecEncrypt : 
      forall s k v u,
        let kl := fst (fst s) in
        let hm := snd (fst s) in
        let em := snd s in
        consistent em (encrypt k v) (k, v) -> 
        exec' u Cont s (Encrypt k v) (Finished (kl, hm, upd em (encrypt k v) (k, v)) (encrypt k v))

  | ExecDecrypt : 
      forall s ev k u,
        let kl := fst (fst s) in
        let hm := snd (fst s) in
        let em := snd s in
        consistent em ev (k, decrypt k ev) ->
        exec' u Cont s (Decrypt k ev) (Finished (kl, hm, upd em ev (k, decrypt k ev)) (decrypt k ev))

  | ExecGetKey : 
      forall s k u,
        let kl := fst (fst s) in
        let hm := snd (fst s) in
        let em := snd s in
        ~In k kl ->
        exec' u (Key k) s GetKey (Finished ((k::kl), hm, em) k)
 
  | ExecCrash :
      forall T d (p: crypto_prog T) u,
        exec' u Crash d p (Crashed d).

  Hint Constructors exec' : core.
  
  Theorem exec_deterministic_wrt_token' :
    forall u o s T (p: crypto_prog T) ret1 ret2,
      exec' u o s p ret1 ->
      exec' u o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto.
  Qed.

  
  Definition CryptoOperation :=
    Build_Core
      crypto_prog
      exec'
      exec_deterministic_wrt_token'.
  
  Definition CryptoLang := Build_Layer CryptoOperation.

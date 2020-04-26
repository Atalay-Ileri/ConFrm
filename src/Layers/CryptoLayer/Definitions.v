Require Import Framework.
Import ListNotations.

Set Implicit Arguments.

Instance value_eq_dec: EqDec value := value_dec.
Instance hash_eq_dec: EqDec hash := hash_dec.

Definition hashmap := @mem hash hash_dec (hash * value).
Definition encryptionmap := @mem value value_dec (key * value).
  
  Inductive token :=
  | Key : key -> token
  | Crash : token
  | Cont : token.

  Definition token_dec : forall (t t': token), {t=t'}+{t<>t'}.
    decide equality.
    apply key_dec.
  Defined.

  Definition oracle := list token.

  Definition state := ((list key * encryptionmap)* hashmap)%type.
  
  Inductive prog : Type -> Type :=
  | GetKey : list value -> prog key
  | Hash : hash -> value -> prog hash
  | Encrypt : key -> value -> prog value
  | Decrypt : key -> value -> prog value.
   
  Inductive exec :
    forall T, oracle ->  state -> prog T -> @Result state T -> Prop :=

  | ExecHash : 
      forall em hm h v,
        let hv := hash_function h v in
        consistent hm hv (h, v) ->
        exec [Cont] (em, hm) (Hash h v) (Finished (em, (upd hm hv (h, v))) hv)
             
  | ExecEncrypt : 
      forall kl em hm k v,
        let ev := encrypt k v in
        consistent em ev (k, v) ->
        exec [Cont] (kl, em, hm) (Encrypt k v) (Finished (kl, (upd em ev (k, v)), hm) ev)

  | ExecDecrypt : 
      forall kl em hm ev k v,
        ev = encrypt k v ->
        em ev = Some (k, v) ->
        exec [Cont] (kl, em, hm) (Decrypt k ev) (Finished (kl, em, hm) v)

  | ExecGetKey : 
      forall vl kl em hm k,
        ~In k kl ->
        consistent_with_upds em
             (map (encrypt k) vl) (map (fun v => (k, v)) vl) ->
        exec [Key k] (kl, em, hm) (GetKey vl) (Finished ((k::kl), em, hm) k)
 
  | ExecCrash :
      forall T d (p: prog T),
        exec [Crash] d p (Crashed d).

  Hint Constructors exec : core.

  Definition weakest_precondition T (p: prog T) :=
    match p in prog T' return (T' -> state -> Prop) -> oracle -> state -> Prop with
    | Hash h v =>
      fun Q o s =>
        let '(em, hm) := s in
        o = [Cont] /\
        let hv := hash_function h v in
        consistent hm hv (h, v) /\
        Q hv (em, (upd hm hv (h, v)))

    | Encrypt k v => 
      fun Q o s =>
        let '(kl, em, hm) := s in
        let ev := encrypt k v in
        o = [Cont] /\
        consistent em ev (k, v) /\
        Q ev (kl, (upd em ev (k, v)), hm)

    | Decrypt k ev => 
      fun Q o s =>
        let '(kl, em, hm) := s in
        exists v,
          o = [Cont] /\
          ev = encrypt k v /\
          em ev = Some (k, v) /\
          Q v s
          
    | GetKey vl =>
      fun Q o s =>
        let '(kl, em, hm) := s in
        (exists k,
           o = [Key k] /\
           ~In k kl /\
           consistent_with_upds em (map (encrypt k) vl) (map (fun v => (k,v)) vl) /\
           Q k ((k::kl), em, hm))
    end.


  Definition weakest_crash_precondition T (p: prog T) :=
    fun Q o (s: state) => o = [Crash] /\ Q s.

  Theorem exec_deterministic_wrt_oracle :
    forall o s T (p: prog T) ret1 ret2,
      exec o s p ret1 ->
      exec o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto.
  Qed.

  Theorem wp_complete:
    forall T (p: prog T) H Q,
      (forall o s, H o s -> weakest_precondition p Q o s) <->
      (forall o s, H o s -> (exists s' v, exec o s p (Finished s' v) /\ Q v s')).
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;
    inversion H0; cleanup; eauto.
  Qed.
  
  Theorem wcp_complete:
    forall T (p: prog T) H C,
      (forall o s, H o s -> weakest_crash_precondition p C o s) <->
      (forall o s, H o s -> (exists s', exec o s p (Crashed s') /\ C s')).
  Proof.
    unfold weakest_crash_precondition;
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;
    inversion H0; cleanup; eauto.
  Qed.

  
  Definition CryptoOperation :=
    Build_Operation
      (list_eq_dec token_dec)
      prog
      exec
      weakest_precondition
      weakest_crash_precondition
      wp_complete
      wcp_complete
      exec_deterministic_wrt_oracle.
  
  Definition CryptoLang := Build_Language CryptoOperation.
  Definition CryptoHL := Build_HoareLogic CryptoLang.

Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).

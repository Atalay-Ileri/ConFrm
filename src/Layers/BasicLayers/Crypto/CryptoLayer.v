Require Import Framework.
Import ListNotations.

Set Implicit Arguments.

Instance value_eq_dec: EqDec value := value_dec.
Instance hash_eq_dec: EqDec hash := hash_dec.

Definition hashmap := @mem hash hash_dec (hash * value).
Definition encryptionmap := @mem value value_dec (key * value).
  
  Inductive token' :=
  | Key : key -> token'
  | Crash : token'
  | Cont : token'.

  Definition state' := ((list key * encryptionmap)* hashmap)%type.

  Inductive crypto_prog : Type -> Type :=
  | GetKey : list value -> crypto_prog key
  | Hash : hash -> value -> crypto_prog hash
  | Encrypt : key -> value -> crypto_prog value
  | Decrypt : key -> value -> crypto_prog value.
   
  Inductive exec' :
    forall T, token' ->  state' -> crypto_prog T -> @Result state' T -> Prop :=

  | ExecHash : 
      forall s h v,
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        let hv := hash_function h v in
        consistent hm hv (h, v) ->
        exec' Cont s (Hash h v) (Finished (kl, em, (upd hm hv (h, v))) hv)
             
  | ExecEncrypt : 
      forall s k v,
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        let ev := encrypt k v in
        consistent em ev (k, v) ->
        exec' Cont s (Encrypt k v) (Finished (kl, (upd em ev (k, v)), hm) ev)

  | ExecDecrypt : 
      forall s ev k v,
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        ev = encrypt k v ->
        em ev = Some (k, v) ->
        exec' Cont s (Decrypt k ev) (Finished s v)

  | ExecGetKey : 
      forall vl s k,
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        ~In k kl ->
        consistent_with_upds em
             (map (encrypt k) vl) (map (fun v => (k, v)) vl) ->
        exec' (Key k) s (GetKey vl) (Finished ((k::kl), em, hm) k)
 
  | ExecCrash :
      forall T d (p: crypto_prog T),
        exec' Crash d p (Crashed d).

  Hint Constructors exec' : core.

  Definition weakest_precondition' T (p: crypto_prog T) :=
    match p in crypto_prog T' return (T' -> state' -> Prop) -> token' -> state' -> Prop with
    | Hash h v =>
      fun Q o s =>
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        let hv := hash_function h v in
        o = Cont /\
        consistent hm hv (h, v) /\
        Q hv (kl, em, (upd hm hv (h, v)))

    | Encrypt k v => 
      fun Q o s =>
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        let ev := encrypt k v in
        o = Cont /\
        consistent em ev (k, v) /\
        Q ev (kl, (upd em ev (k, v)), hm)

    | Decrypt k ev => 
      fun Q o s =>
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        exists v,
          o = Cont /\
          ev = encrypt k v /\
          em ev = Some (k, v) /\
          Q v s
          
    | GetKey vl =>
      fun Q o s =>
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        exists k,
          o = Key k /\
          ~In k kl /\
          consistent_with_upds em (map (encrypt k) vl) (map (fun v => (k,v)) vl) /\
          Q k ((k::kl), em, hm)
    end.


  Definition weakest_crash_precondition' T (p: crypto_prog T) :=
    fun Q o (s: state') => o = Crash /\ Q s.

  Definition strongest_postcondition' T (p: crypto_prog T) :=
    match p in crypto_prog T' return (token' -> state' -> Prop) -> T' -> state' -> Prop with
    | Hash h v =>
      fun P t s' =>
        exists s,
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        let hv := hash_function h v in
        P Cont s /\
        consistent hm hv (h, v) /\
        t = hv /\
        s' = (kl, em, (upd hm hv (h, v)))
               
    | Encrypt k v => 
      fun P t s' =>
        exists s,
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        let ev := encrypt k v in
        P Cont s /\
        consistent em ev (k, v) /\
        t = ev /\
        s' = (kl, (upd em ev (k, v)), hm)

    | Decrypt k ev => 
      fun P t s' =>
        exists s v,
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        P Cont s /\
        ev = encrypt k v /\
        em ev = Some (k, v) /\
        t = v /\ s' = s
          
    | GetKey vl =>
      fun P t s' =>
        exists s k,
        let kl := fst (fst s) in
        let em := snd (fst s) in
        let hm := snd s in
        P (Key k) s /\
        ~In k kl /\
        consistent_with_upds em (map (encrypt k) vl) (map (fun v => (k,v)) vl) /\
        t = k /\
        s' = ((k::kl), em, hm)
    end.

  Definition strongest_crash_postcondition' T (p: crypto_prog T) :=
    fun (P: token' -> state' -> Prop) s' => P Crash s'.

  Theorem exec_deterministic_wrt_token' :
    forall o s T (p: crypto_prog T) ret1 ret2,
      exec' o s p ret1 ->
      exec' o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto.
  Qed.

  Theorem sp_complete':
    forall T (p: crypto_prog T) P (Q: _ -> _ -> Prop),
      (forall t s', strongest_postcondition' p P t s' -> Q t s') <->
      (forall o s s' t, P o s -> exec' o s p (Finished s' t) -> Q t s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try inversion H1; cleanup;
    eapply H; eauto;
    do 2 eexists; eauto.    
  Qed.

  Theorem scp_complete':
    forall T (p: crypto_prog T) P (Q:  _ -> Prop),
      (forall s', strongest_crash_postcondition' p P s' -> Q s') <->
      (forall o s s', P o s -> exec' o s p (Crashed s') -> Q s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try inversion H1; cleanup;
    eapply H; eauto.
  Qed.

  Theorem wp_complete':
    forall T (p: crypto_prog T) H Q,
      (forall o s, H o s -> weakest_precondition' p Q o s) <->
      (forall o s, H o s -> (exists s' v, exec' o s p (Finished s' v) /\ Q v s')).
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;
    inversion H0; cleanup; eauto.    
  Qed.
  
  Theorem wcp_complete':
    forall T (p: crypto_prog T) H C,
      (forall o s, H o s -> weakest_crash_precondition' p C o s) <->
      (forall o s, H o s -> (exists s', exec' o s p (Crashed s') /\ C s')).
  Proof.
    unfold weakest_crash_precondition';
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;
    inversion H0; cleanup; eauto.
  Qed.
  
  Definition CryptoOperation :=
    Build_Core
      crypto_prog
      exec'
      weakest_precondition'
      weakest_crash_precondition'
      strongest_postcondition'
      strongest_crash_postcondition'
      wp_complete'
      wcp_complete'
      sp_complete'
      scp_complete'
      exec_deterministic_wrt_token'.
  
  Definition CryptoLang := Build_Language CryptoOperation.

Notation "| p |" := (Op CryptoOperation p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op CryptoOperation p1) (fun x => p2))(right associativity, at level 60).
Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).

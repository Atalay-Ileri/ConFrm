Require Import Primitives.
Import ListNotations.

Set Implicit Arguments.

Record Operation :=
  {
    oracle : Type;
    oracle_dec: forall (o o': oracle), {o = o'}+{o <> o'};
    state : Type;
    prog : Type -> Type;
    exec: forall T, oracle -> state -> prog T -> @Result state T -> Prop;
    weakest_precondition: forall T, prog T -> (T -> state -> Prop) -> (oracle -> state -> Prop);
    weakest_crash_precondition: forall T, prog T -> (state -> Prop) -> (oracle -> state -> Prop);
    wp_complete:
      forall T (p: prog T) H Q,
        (forall o s, H o s -> weakest_precondition p Q o s) <->
        (forall o s, H o s ->
                (exists s' v, exec o s p (Finished s' v) /\ Q v s'));
    wcp_complete:
      forall T (p: prog T) H C,
        (forall o s, H o s -> weakest_crash_precondition p C o s) <->
        (forall o s, H o s ->
            (exists s', exec o s p (Crashed s') /\ C s'));
      exec_deterministic_wrt_oracle :
        forall o s T (p: prog T) ret1 ret2,
          exec o s p ret1 ->
          exec o s p ret2 ->
          ret1 = ret2;
  }.

Arguments exec _ {T}.
Arguments weakest_precondition _ {T}.
Arguments weakest_crash_precondition _ {T}.

Lemma wp_to_exec:
  forall O T (p: @prog O T) Q o s,
    weakest_precondition _ p Q o s -> (exists s' v, exec _ o s p (Finished s' v) /\ Q v s').
Proof.
  intros. eapply wp_complete; eauto.
Qed.

Lemma exec_to_wp:
  forall O T (p: @prog O T) (Q: T -> state _ -> Prop) o s s' v,
    exec _ o s p (Finished s' v) ->
    Q v s' ->
    weakest_precondition _ p Q o s.
Proof.
  intros.
  eapply wp_complete; intros.
  apply X.
  simpl; eauto.
Qed.

Lemma wcp_to_exec:
  forall O T (p: O.(@prog) T) Q o s,
    weakest_crash_precondition _ p Q o s -> (exists s', exec _ o s p (Crashed s') /\ Q s').
Proof.
  intros. eapply wcp_complete; eauto.
Qed.
  
Lemma exec_to_wcp:
  forall O T (p: O.(@prog) T) (Q: state _ -> Prop) o s s',
    exec _ o s p (Crashed s') ->
    Q s' ->
    weakest_crash_precondition _ p Q o s.
Proof.
  intros.
  eapply wcp_complete; intros.
  apply X.
  simpl; eauto.
Qed.

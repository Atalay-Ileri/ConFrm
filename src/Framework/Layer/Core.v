Require Import Primitives.
Import ListNotations.

Set Implicit Arguments.

Record Core :=
  {
    token : Type;
    state : Type;
    operation : Type -> Type;
    exec: forall T, token -> state -> operation T -> @Result state T -> Prop;
    
    exec_deterministic_wrt_token :
      forall o s T (p: operation T) ret1 ret2,
        exec o s p ret1 ->
        exec o s p ret2 ->
        ret1 = ret2;
  }.

Arguments exec _ {T}.

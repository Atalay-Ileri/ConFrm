Require Import Mem.
Set Implicit Arguments.

Section Defs.

  Record Layer :=
    {
      side_result : Type;
      state : Type;
      prog: Type -> Type;
      exec: forall T, state -> prog T -> state -> T -> side_result -> Prop;
    }.

  Record Refinement (low high : Layer) :=
    {
      R : state low -> state high -> Prop;
      compile : forall TL TH, state high -> prog high TH -> prog low TL;
      convert_result : forall TL TH, state low -> TL -> TH;

      exec_compat:
        forall TL TH ls hs ls' r p lt ht,
          R ls hs ->
          exec low ls (compile TL TH hs p) ls' r lt ->
          exists hs',
            exec high hs p hs' (convert_result TH ls r) ht /\
            R ls' hs';
    }.
End Defs.
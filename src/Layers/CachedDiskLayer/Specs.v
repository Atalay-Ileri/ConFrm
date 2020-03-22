Require Import Framework CacheLayer DiskLayer.
Require Import CachedDiskLayer.Definitions.
Import ListNotations CachedDiskOperation CachedDiskHL.
Close Scope pred_scope.
Open Scope type_scope.

Theorem p1_ok:
  forall T (p: CacheHL.Lang.prog T)
    (opre: oracle_pre_condition) (pre: pre_condition)
    (post: post_condition) (opost: oracle_post_condition)
    (crash: crash_condition) (ocrash: oracle_crash_condition)
    opre1 pre1 post1 opost1 crash1 ocrash1
    lifted_o o (s: state),
    CacheHL.hoare_triple opre1 pre1 p post1 crash1 opost1 ocrash1 o (fst s) ->
    (opre lifted_o (|P1 p|) s ->
     opre1 o p (fst s) ->
     lifted_o = [ OpOracle [Oracle1 o] ]) ->
    (opre lifted_o (|P1 p|) s -> opre1 o p (fst s)) ->
    (pre s -> pre1 (fst s)) ->
    (forall r s', post1 r s' -> post r (s', snd s)) ->
    (forall r s', opost1 o (fst s) r s' -> opost lifted_o s r (s', snd s)) ->
    (forall s', crash1 s' -> crash (s', snd s)) ->
    (forall s', ocrash1 o (fst s) s' -> ocrash lifted_o s (s', snd s)) ->
    hoare_triple opre pre (|P1 p|) post crash opost ocrash lifted_o s.
Proof.
  unfold hoare_triple, CacheHL.hoare_triple; intros.
  intuition; cleanup.

  split_ors.
  {
    eexists; intuition eauto.
    left; do 2 eexists; intuition eauto.
  }

  {
    eexists; intuition eauto.
    eapply ExecOpCrash; eauto.
    right; eexists; intuition eauto.
  }
Qed.


Theorem p2_ok:
  forall T (p: DiskHL.Lang.prog T)
    (opre: oracle_pre_condition) (pre: pre_condition)
    (post: post_condition) (opost: oracle_post_condition)
    (crash: crash_condition) (ocrash: oracle_crash_condition)
    opre2 pre2 post2 opost2 crash2 ocrash2
    lifted_o o (s: state),
    
    DiskHL.hoare_triple opre2 pre2 p post2 crash2 opost2 ocrash2 o (snd s) ->
    (opre lifted_o (|P2 p|) s ->
     opre2 o p (snd s) ->
     lifted_o = [OpOracle [Oracle2 o] ]) ->
    (opre lifted_o (|P2 p|) s -> opre2 o p (snd s)) ->
    (pre s -> pre2 (snd s)) ->
    (forall r s', post2 r s' -> post r (fst s, s')) ->
    (forall r s', opost2 o (snd s) r s' -> opost lifted_o s r (fst s, s')) ->
    (forall s', crash2 s' -> crash (fst s, s')) ->
    (forall s', ocrash2 o (snd s) s' -> ocrash lifted_o s (fst s, s')) ->
    hoare_triple opre pre (|P2 p|) post crash opost ocrash lifted_o s.
Proof.
  unfold hoare_triple, DiskHL.hoare_triple; intros.
  intuition; cleanup.

  split_ors.
  {
    eexists; intuition eauto.
    left; do 2 eexists; intuition eauto.
  }

  {
    eexists; intuition eauto.
    eapply ExecOpCrash; eauto.
    right; eexists; intuition eauto.
  }
Qed.


Hint Extern 1 (hoare_triple _ _ (|P1 _ |) _ _ _ _ _ _) => eapply p1_ok : specs.
Hint Extern 1 (hoare_triple _ _ (|P2 _ |) _ _ _ _ _ _) => eapply p2_ok : specs.

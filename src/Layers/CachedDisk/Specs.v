(*
Require Import Framework CacheLayer CryptoDiskLayer.
Require Import CryptoDiskLayer.Definitions.
Close Scope pred_scope.
Open Scope type_scope.

Theorem p1_ok:
  forall T (p: Language.prog CacheLang T)
    (opre: oracle_pre_condition CachedDiskHL _) (pre: pre_condition CachedDiskHL)
    (post: post_condition CachedDiskHL _) (opost: oracle_post_condition CachedDiskHL _)
    (crash: crash_condition CachedDiskHL) (ocrash: oracle_crash_condition CachedDiskHL)
    opre1 pre1 post1 opost1 crash1 ocrash1
    lifted_o o s,
    CacheHL.(hoare_triple) opre1 pre1 p post1 crash1 opost1 ocrash1 o (fst s) ->
    (opre lifted_o (|P1 p|) s ->
     opre1 o p (fst s) ->
     lifted_o = [ OpOracle CachedDiskOperation [Oracle1 _ o] ]) ->
    (opre lifted_o (|P1 p|) s -> opre1 o p (fst s)) ->
    (pre s -> pre1 (fst s)) ->
    (forall r s', post1 r s' -> post r (s', snd s)) ->
    (forall r s', opost1 o (fst s) r s' -> opost lifted_o s r (s', snd s)) ->
    (forall s', crash1 s' -> crash (s', snd s)) ->
    (forall s', ocrash1 o (fst s) s' -> ocrash lifted_o s (s', snd s)) ->
    CachedDiskHL.(hoare_triple) opre pre (|P1 p|) post crash opost ocrash lifted_o s.
Proof.
  unfold hoare_triple, hoare_triple'; intros.
  intuition; cleanup.

  split_ors.
  {
    eexists; intuition eauto.
    repeat econstructor; eauto.
    left; do 2 eexists; intuition eauto.
  }

  {
    eexists; intuition eauto.
    eapply ExecOpCrash; econstructor; eauto.
    right; eexists; intuition eauto.
  }
Qed.


Theorem p2_ok:
  forall T (p: Language.prog DiskLang T)
    (opre: oracle_pre_condition CachedDiskHL _) (pre: pre_condition CachedDiskHL)
    (post: post_condition CachedDiskHL _) (opost: oracle_post_condition CachedDiskHL _)
    (crash: crash_condition CachedDiskHL) (ocrash: oracle_crash_condition CachedDiskHL)
    opre2 pre2 post2 opost2 crash2 ocrash2
    lifted_o o s,
    
    DiskHL.(hoare_triple) opre2 pre2 p post2 crash2 opost2 ocrash2 o (snd s) ->
    (opre lifted_o (|P2 p|) s ->
     opre2 o p (snd s) ->
     lifted_o = [OpOracle CachedDiskOperation [Oracle2 _ o] ]) ->
    (opre lifted_o (|P2 p|) s -> opre2 o p (snd s)) ->
    (pre s -> pre2 (snd s)) ->
    (forall r s', post2 r s' -> post r (fst s, s')) ->
    (forall r s', opost2 o (snd s) r s' -> opost lifted_o s r (fst s, s')) ->
    (forall s', crash2 s' -> crash (fst s, s')) ->
    (forall s', ocrash2 o (snd s) s' -> ocrash lifted_o s (fst s, s')) ->
    CachedDiskHL.(hoare_triple) opre pre (|P2 p|) post crash opost ocrash lifted_o s.
Proof.
  unfold hoare_triple, hoare_triple'; intros.
  intuition; cleanup.

  split_ors.
  {
    eexists; intuition eauto.
    repeat econstructor; eauto.
    left; do 2 eexists; intuition eauto.
  }

  {
    eexists; intuition eauto.
    eapply ExecOpCrash; econstructor; eauto.
    right; eexists; intuition eauto.
  }
Qed.


Hint Extern 1 (hoare_triple _ _ _ (|P1 _ |) _ _ _ _ _ _) => eapply p1_ok : specs.
Hint Extern 1 (hoare_triple _ _ _ (|P2 _ |) _ _ _ _ _ _) => eapply p2_ok : specs.
*)

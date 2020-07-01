Require Import RelationClasses.
Require Import Morphisms.
Require Import FunctionalExtensionality.
Require Import Mem Pred SepStar.

(** =*=> **)
Instance pimpl_preorder {AT AEQ V} :
  PreOrder (@pimpl AT AEQ V).
Proof.
  firstorder.
Qed.

Instance pimpl_pimpl_proper1 {AT AEQ V} :
  Proper (pimpl ==> Basics.flip pimpl ==> Basics.flip Basics.impl) (@pimpl AT AEQ V).
Proof.
  firstorder.
Qed.

Instance pimpl_pimpl_proper2 {AT AEQ V} :
  Proper (Basics.flip pimpl ==> pimpl ==> Basics.impl) (@pimpl AT AEQ V).
Proof.
  firstorder.
Qed.

(** <=*=> *)
Instance piff_equiv {AT AEQ V} :
  Equivalence (@piff AT AEQ V).
Proof.
  firstorder.
Qed.

(** =*=> and <=*=> **)
Instance piff_pimpl_subrelation {AT AEQ V} :
  subrelation (@piff AT AEQ V) (@pimpl AT AEQ V).
Proof.
  firstorder.
Qed.

Instance piff_flip_pimpl_subrelation {AT AEQ V} :
  subrelation (@piff AT AEQ V) (Basics.flip (@pimpl AT AEQ V)).
Proof.
  firstorder.
Qed.

Instance pimpl_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> Basics.flip Basics.impl) (@pimpl AT AEQ V).
Proof.
  firstorder.
Qed.

(**| =*=> and * |**)
Instance sep_star_apply_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> eq ==> Basics.impl) (@sep_star AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  apply pimpl_sep_star; assumption.
Qed.

Instance sep_star_apply_pimpl_proper' {AT AEQ V} :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl ==> eq ==> Basics.flip Basics.impl) (@sep_star AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  apply pimpl_sep_star; assumption.
Qed.

Instance sep_star_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@sep_star AT AEQ V).
Proof.
  intros a b H c d H'.
  apply pimpl_sep_star; assumption.
Qed.

Instance sep_star_pimpl_proper' {AT AEQ V} :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl ==> Basics.flip pimpl) (@sep_star AT AEQ V).
Proof.
  intros a b H c d H'.
  apply pimpl_sep_star; assumption.
Qed.

(**| <=*=> and * |**)
Instance sep_star_apply_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> eq ==> Basics.impl) (@sep_star AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  apply pimpl_sep_star. 
  apply Hp.
  apply Hq.
Qed.

Instance sep_star_apply_piff_proper' {AT AEQ V} :
  Proper (piff ==> piff ==> eq ==> iff) (@sep_star AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm.
  subst; split; intros.
  - eapply pimpl_apply; [| eassumption ]. apply pimpl_sep_star. apply Hp. apply Hq.
  - eapply pimpl_apply; [| eassumption ]. apply pimpl_sep_star. apply Hp. apply Hq.
Qed.

Instance sep_star_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> piff) (@sep_star AT AEQ V).
Proof.
  intros a b H c d H'.
  split; ( apply pimpl_sep_star; [ apply H | apply H' ] ).
Qed.


(**| = and * |**)
Instance sep_star_apply_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq ==> eq) (@sep_star AT AEQ V).
Proof.
  congruence.
Qed.

Instance sep_star_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq) (@sep_star AT AEQ V).
Proof.
  congruence.
Qed.


(**| =*=> and --* |**)
Instance septract_apply_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> eq ==> Basics.impl) (@septract AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  erewrite septract_pimpl_l; eauto.
  erewrite septract_pimpl_r; eauto.
Qed.

Instance septract_apply_pimpl_proper' {AT AEQ V} :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl ==> eq ==> Basics.flip Basics.impl) (@septract AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  erewrite septract_pimpl_l; eauto.
  erewrite septract_pimpl_r; eauto.
Qed.

Instance septract_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@septract AT AEQ V).
Proof.
  intros a b H c d H'.  
  erewrite septract_pimpl_l; eauto.
  erewrite septract_pimpl_r; eauto.
Qed.

Instance septract_pimpl_proper' {AT AEQ V} :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl ==> Basics.flip pimpl) (@septract AT AEQ V).
Proof.
  intros a b H c d H'.
  unfold Basics.flip in *.  
  erewrite septract_pimpl_l; eauto.
  erewrite septract_pimpl_r; eauto.
Qed.

(**| <=*=> and --* |**)
Instance septract_apply_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> eq ==> Basics.impl) (@septract AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  rewrite Hp.
  rewrite Hq; eauto.
Qed.

Instance septract_apply_piff_proper' {AT AEQ V} :
  Proper (piff ==> piff ==> eq ==> iff) (@septract AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm.
  subst; split; intros.
  - eapply pimpl_apply; [| eassumption ]. rewrite Hp. rewrite Hq. eauto.
  - eapply pimpl_apply; [| eassumption ]. rewrite Hp. rewrite Hq. eauto.
Qed.

Instance septract_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> piff) (@septract AT AEQ V).
Proof.
  intros a b H c d H'.
  split; ( rewrite H; rewrite H'; eauto).
Qed.


(**| = and --* |**)
Instance septract_apply_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq ==> eq) (@septract AT AEQ V).
Proof.
  congruence.
Qed.

Instance septract_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq) (@septract AT AEQ V).
Proof.
  congruence.
Qed.


(**| /*\ |**)
Instance and_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq) (@and AT AEQ V).
Proof.
  congruence.
Qed.

Instance and_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> piff) (@and AT AEQ V).
Proof.
  firstorder.
Qed.

Instance and_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@and AT AEQ V).
Proof.
  firstorder.
Qed.


(**| \*/ |**)
Instance or_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq) (@or AT AEQ V).
Proof.
  congruence.
Qed.

Instance or_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> piff) (@or AT AEQ V).
Proof.
  firstorder.
Qed.

Instance or_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@or AT AEQ V).
Proof.
  firstorder.
Qed.


Example pimpl_rewrite : forall AT AEQ V a b (p : @predicate AT AEQ V) q x y,
                          p =*=> q
  -> (x /*\ a * p * b \*/ y =*=> x /*\ a * q * b \*/ y).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

(**| = and exists* |**)
Instance exists_proper_eq {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A eq ==> eq) (@exis AT AEQ V A).
Proof.
  intros pf qf Heq.
  assert (pf = qf) by (apply functional_extensionality; congruence); subst.
  reflexivity.
Qed.

(**| <=*=> and exists* |**)
Instance exists_proper_piff {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A piff ==> piff) (@exis AT AEQ V A).
Proof.
  firstorder.
Qed.

(**| =*=> and exists* |**)
Instance exists_proper_pimpl {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A pimpl ==> pimpl) (@exis AT AEQ V A).
Proof.
  firstorder.
Qed.

Example pimpl_exists_rewrite : forall AT AEQ V (p : @predicate AT AEQ V) q, p =*=> q
  -> (exists* x, p * x) =*=> (exists* x, q * x).
Proof.
  intros.
  setoid_rewrite H.
  reflexivity.
Qed.

(**
 * The following variation is needed for situations where a [predicate] containing
 * an [exis] is applied to a [mem], and [setoid_rewrite] tries to rewrite the
 * term that appears under [exis].
 *)
Instance exists_proper_pimpl_impl {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A piff ==> eq ==> iff) (@exis AT AEQ V A).
Proof.
  intros a b Hab m1 m2 Hm.
  split; unfold Basics.impl, exis; intros; deex; eexists.
  eapply Hab; eauto.
  eapply Hab; eauto.
Qed.



(**
 * The following instance is needed to make [setoid_rewrite] fast on terms
 * that involve [lift_empty].  Otherwise, typeclass search takes forever.
 *)
Instance lift_empty_proper_iff {AT AEQ V} :
  Proper (iff ==> @piff _ _ _) (@lift_empty AT AEQ V).
Proof.
  firstorder.
Qed.

(**
 * The following instances are needed to rewrite under [lift_empty].
 *)
Instance lift_empty_proper_impl {AT AEQ V} :
  Proper (Basics.impl ==> @pimpl _ _ _) (@lift_empty AT AEQ V).
Proof.
  firstorder.
Qed.

Instance lift_empty_proper_eq {AT AEQ V} :
  Proper (eq ==> eq) (@lift_empty AT AEQ V).
Proof.
  congruence.
Qed.

Instance lift_empty_proper_expanded_impl {AT AEQ V} :
  Proper (Basics.impl ==> eq ==> Basics.impl) (@lift_empty AT AEQ V).
Proof.
  unfold lift_empty.
  intros a b Hab m1 m2 Hm H; subst.
  intuition.
Qed.

Instance lift_empty_proper_expanded_flipimpl {AT AEQ V} :
  Proper (Basics.flip Basics.impl ==> eq ==> Basics.flip Basics.impl) (@lift_empty AT AEQ V).
Proof.
  unfold lift_empty.
  intros a b Hab m1 m2 Hm H; subst.
  intuition.
Qed.

Instance lift_empty_proper_expanded_iff {AT AEQ V} :
  Proper (iff ==> eq ==> iff) (@lift_empty AT AEQ V).
Proof.
  unfold lift_empty.
  intros a b Hab m1 m2 Hm; subst.
  intuition.
Qed.


(**
 * This instance in effect tells [setoid_rewrite] about functional extensionality.
 *)
Instance funext_subrelation {A f R} {subf : subrelation R eq}:
  subrelation (@pointwise_relation A f R) eq.
Proof.
  unfold pointwise_relation.
  intros a b Hab.
  apply functional_extensionality; auto.
Qed.

(**
 * This helps rewrite using [eq] under deep predicateicates, [prog]s, etc.
 * See https://coq.inria.fr/bugs/show_bug.cgi?id=3795
 *)
Global Program Instance eq_equivalence {A} : Equivalence (@eq A) | 0.

Instance predicate_apply_pimpl_proper {AT AEQ V} :
  Proper (eq ==> pimpl ==> Basics.impl) (@predicate_apply AT AEQ V).
Proof.
  unfold predicate_apply.
  intros ma mb Hmab p q Hpq H.
  subst.
  auto.
Qed.

Instance predicate_apply_pimpl_flip_proper {AT AEQ V} :
  Proper (eq ==> Basics.flip pimpl ==> Basics.flip Basics.impl) (@predicate_apply AT AEQ V).
Proof.
  unfold predicate_apply.
  intros ma mb Hmab p q Hpq H.
  subst.
  auto.
Qed.

Instance predicate_apply_piff_proper {AT AEQ V} :
  Proper (eq ==> piff ==> iff) (@predicate_apply AT AEQ V).
Proof.
  unfold predicate_apply.
  intros ma mb Hmab p q Hpq.
  subst. destruct Hpq.
  intuition.
Qed.

Example predicate_apply_rewrite : forall AT AEQ V (p q: predicate) (m : @mem AT AEQ V),
  m ## (p * q)%predicate -> m ## (q * p)%predicate.
Proof.
  intros.
  rewrite sep_star_comm1 in H.
  auto.
Qed.


Instance predicate_except_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> eq ==> eq ==> pimpl) (@predicate_except AT AEQ V).
Proof.
  intros F F' HF a a' Ha v v' Hv.
  subst.
  firstorder.
Qed.

Instance predicate_except_piff_proper {AT AEQ V} :
  Proper (piff ==> eq ==> eq ==> piff) (@predicate_except AT AEQ V).
Proof.
  intros F F' HF a a' Ha v v' Hv.
  subst.
  firstorder.
Qed.

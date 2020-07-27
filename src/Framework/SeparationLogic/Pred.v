Require Import Arith.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import Mem.
Require Import RelationClasses.
Require Import Morphisms.
Require Import List.
Require Import BaseTypes.
Set Implicit Arguments.


(** ** Predicates *)

Section GeneralizedPredicate.

Variable AT : Type.
Variable AEQ : EqDec AT.
Variable V : Type.

Definition predicate := @mem AT AEQ V -> Prop.

(** Primitive predicates **)
Definition ptsto (a : AT) (v : V) : predicate :=
  fun m => m a = Some v /\ forall a', a <> a' -> m a' = None.

Definition emp : predicate :=
  fun m => forall a, m a = None.

Definition any : predicate :=
  fun m => True.

Definition lift (P : Prop) : predicate :=
  fun m => P.

Definition lift_empty (P : Prop) : predicate :=
  fun m => P /\ forall a, m a = None.

Definition indomain (a: AT) (m: @mem AT AEQ V) :=
  exists (v:V), m a = Some v.

Definition notindomain (a : AT) (m : @mem AT AEQ V) :=
  m a = None.

Definition diskIs (m : @mem AT AEQ V) : predicate :=
  fun m' => m = m'.


(** Predicate transformers **)
Definition impl (p q : predicate) : predicate :=
  fun m => p m -> q m.

Definition and (p q : predicate) : predicate :=
  fun m => p m /\ q m.

Definition or (p q : predicate) : predicate :=
  fun m => p m \/ q m.

Definition foral_ A (p : A -> predicate) : predicate :=
  fun m => forall x, p x m.

Definition exis A (p : A -> predicate) : predicate :=
  fun m => exists x, p x m.

Definition uniqpredicate A (p : A -> predicate) (x : A) : predicate :=
  fun m => p x m /\ (forall (x' : A), p x' m -> x = x').

Definition pimpl (p q : predicate) := forall m, p m -> q m.

Definition piff (p q : predicate) : Prop := (pimpl p q) /\ (pimpl q p).

Definition mem_disjoint (m1 m2 : @mem AT AEQ V) :=
  ~ exists a (v1 v2 : V), m1 a = Some v1 /\ m2 a = Some v2.

Definition sep_star_impl (p1: predicate) (p2: predicate) : predicate :=
  fun m => exists m1 m2, m = mem_union m1 m2 /\ mem_disjoint m1 m2 /\ p1 m1 /\ p2 m2.

Definition septract (p q : predicate) : predicate :=
  fun m => exists m1, mem_disjoint m m1 /\ p m1 /\ q (mem_union m m1).

Definition predicate_apply (m : @mem AT AEQ V) (p : predicate) := p m.

Definition strictly_exact (p : predicate) : Prop :=
  forall m1 m2, p m1 -> p m2 -> m1 = m2.

Definition exact_domain (p : predicate) : Prop :=
  forall m1 m2, p m1 -> p m2 -> (forall a, m1 a = None <-> m2 a = None).

Definition precise (p : predicate) : Prop :=
  forall m1 m1' m2 m2',
  mem_union m1 m1' = mem_union m2 m2' ->
  mem_disjoint m1 m1' ->
  mem_disjoint m2 m2' ->
  p m1 -> p m2 -> m1 = m2.

(* exclude an address from a predicate *)
Definition predicate_except (F : predicate) a v : predicate :=
  fun m => m a = None /\ F (insert m a v).


End GeneralizedPredicate.

Arguments predicate {AT AEQ V}.
Arguments emp {AT AEQ V} _.
Arguments any {AT AEQ V} _.
Arguments pimpl {AT AEQ V} _ _.
Arguments piff {AT AEQ V} _ _.
Arguments sep_star_impl {AT AEQ V} _ _ _.
Arguments septract {AT AEQ V} _ _ _.
Arguments indomain {AT AEQ V} _ _.
Arguments notindomain {AT AEQ V} _ _.
Arguments diskIs {AT AEQ V} _ _.
Arguments predicate_apply {AT AEQ V} _ _.
Arguments strictly_exact {AT AEQ V} _.
Arguments exact_domain {AT AEQ V} _.
Arguments precise {AT AEQ V} _.

Hint Unfold pimpl.
Hint Unfold piff.

Infix "|->" := ptsto (at level 35) : predicate_scope.

Bind Scope predicate_scope with predicate.
Delimit Scope predicate_scope with predicate.

Infix "-*->" := impl (right associativity, at level 95) : predicate_scope.
Infix "/*\" := and (at level 85): predicate_scope.
Infix "\*/" := or (at level 85): predicate_scope.
Notation "'forall*' x .. y , p" := (foral_ (fun x => .. (foral_ (fun y => p)) ..)) (at level 200, x binder, right associativity) : predicate_scope.
Notation "'exists*' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) (at level 200, x binder, right associativity): predicate_scope.
Notation "'exists*' ! x .. y , p" := (exis (uniqpredicate (fun x => .. (exis (uniqpredicate (fun y => p))) ..))) (at level 200, x binder, right associativity) : predicate_scope.
Notation "a |->?" := (exists* v, a |-> v)%predicate (at level 35) : predicate_scope.
Notation "[ P ]" := (lift P) : predicate_scope.
Notation "[[ P ]]" := (lift_empty P) : predicate_scope.
Notation "p =*=> q" := (pimpl p%predicate q%predicate) (right associativity, at level 90).
Notation "p <=*=> q" := (piff p%predicate q%predicate) (at level 90).
Notation "m ## p" := (predicate_apply m p%predicate) (at level 90).

Global Opaque predicate.

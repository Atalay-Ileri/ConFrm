Require Import Primitives Omega Disk FunctionalExtensionality.
Require Import BlockAllocatorDefinitions ListUtils.


Lemma delete_eq:
  forall A AEQ V (m: @mem A AEQ V) a,
    delete m a a = None.
Proof.
  intros; unfold delete; simpl.
  destruct (AEQ a a); intuition.
Qed.

Lemma delete_ne:
  forall A AEQ V (m: @mem A AEQ V) a a',
    a <> a' ->
    delete m a a' = m a'.
Proof.
  intros; unfold delete; simpl.
  destruct (AEQ a' a); subst; intuition.
Qed.
        

Lemma star_split:
    forall (AT : Type) (AEQ : EqDec AT) (V : Type)
      (p q : @pred AT AEQ V) (m : @mem AT AEQ V),
      (p * q)%pred m ->
      (exists m1 m2, mem_disjoint m1 m2 /\ p m1 /\ q m2 /\ mem_union m1 m2 = m)%type.
  Proof.
    intros; unfold sep_star in *; rewrite sep_star_is in *;
      destruct H; cleanup; eauto.
    do 2 eexists; intuition eauto.
  Qed.

Theorem hoare_triple_pre_ex':
  forall T V (p: prog T) pre post crash,
  (forall (v: V), hoare_triple (fun a d => pre v a d) p post crash) ->
  hoare_triple (fun a d => (exists (v: V), pre v a) d) p post crash.
Proof.
  unfold hoare_triple; intros.
  destruct_lift H0; cleanup.
  eapply H; eauto.
Qed.

Theorem hoare_triple_pre_ex:
  forall T V (p: prog T) pre post crash F P,
  (forall (v: V), hoare_triple (fun a d => ((F * (fun d' => pre v a d')) * [[ P a d ]]) d) p post crash) ->
  hoare_triple (fun a d => ((F * (fun d' => (exists (v: V), pre v a) d')) * [[ P a d ]]) d) p post crash.
Proof.
  intros.
  eapply hoare_triple_strengthen_pre.
  apply hoare_triple_pre_ex'.
  instantiate (1:= fun v a d => ((F * (pre v a)) * [[ P a d ]]) d).
  simpl; eauto.
  intros; norm.
  unfold stars; simpl.
  intros mx Hmx; simpl in *.
  destruct_lift Hmx.
  destruct_lift H0.
  destruct_lift H0.
  exists dummy.
  pred_apply' H0; norm.
  cancel.
  all: eauto.
Qed.

Lemma upd_eq':
  forall (A V : Type) (AEQ : EqDec A) (m : mem) (a : A) (v : V),
    @upd _ _ AEQ m a v a = Some v.
Proof.
  intros; apply upd_eq; eauto.
Qed.

Lemma ptsto_bits'_app_split:
  forall l1 l2 n dh,
    ptsto_bits' dh (l1++l2) n =p=>
    (ptsto_bits' dh l1 n * ptsto_bits' dh l2 (n + length l1))%pred.
Proof.
  unfold ptsto_bits; induction l1;
    simpl; intros; eauto.
  rewrite Nat.add_0_r; cancel.
  rewrite IHl1; cancel.
  rewrite Nat.add_succ_r; eauto.
Qed.

Lemma ptsto_bits'_app_merge:
  forall l1 l2 n dh,
    (ptsto_bits' dh l1 n * ptsto_bits' dh l2 (n + length l1))%pred =p=>
     ptsto_bits' dh (l1++l2) n.
Proof.
  unfold ptsto_bits; induction l1;
    simpl; intros; eauto.
  rewrite Nat.add_0_r; cancel.
  rewrite <- IHl1; cancel.
  rewrite Nat.add_succ_r; eauto.
Qed.

Lemma ptsto_bits'_inbound:
  forall l n dh a F d,
    a < length l + n ->
    a >= n ->
    (F * ptsto_bits' dh l n)%pred d ->
    (exists vs, d (S a) = Some vs /\
           (nth (a - n) l 0 = 0 -> dh a = None) /\
           (nth (a - n) l 0 = 1 -> dh a = Some (fst vs)) /\
           (nth (a - n) l 0 < 2))%type.
Proof.
   eapply (rev_ind
             (fun l =>
                forall (n : nat) (dh : disk value) (a : nat) (F : pred) (d : mem),
  a < length l + n ->
  a >= n ->
  (F ✶ ptsto_bits' dh l n) d ->
  exists vs : set value,
    (d (S a) = Some vs /\
     (nth (a - n) l 0 = 0 -> dh a = None) /\
     (nth (a - n) l 0 = 1 -> dh a = Some (fst vs)) /\
     (nth (a - n) l 0 < 2))%type
));
     simpl; intros.
   omega.

   rewrite app_length in *; simpl in *.
   rewrite ptsto_bits'_app_split in *; simpl in *.
   destruct (addr_dec a (n + length l)); subst.
   - rewrite minus_plus.
     rewrite app_nth2; try omega.
     rewrite Nat.sub_diag; simpl.
     destruct_lifts.
     eexists; split.
     eapply ptsto_valid; pred_apply; cancel.
     intuition; subst;
       destruct_lifts; eauto.
     destruct x; eauto.
     destruct x; eauto.
     destruct_lifts; tauto.
   - destruct_lifts.
     rewrite app_nth1; try omega.
     eapply H; eauto.
     omega.
     pred_apply' H2; cancel.
Qed.

Lemma septract_sep_star_extract :
  forall AT AEQ V (p q: @pred AT AEQ V),
    q =p=> (exists F, F * p) ->
    q =p=> (p --* q) * p.
Proof.
  intros.
  intros m Hm.
  eapply_fresh H in Hm.
  destruct_lift Hx.
  apply star_split in H0; cleanup.
  
  unfold sep_star; rewrite sep_star_is.
  unfold sep_star_impl.
  unfold septract.
  do 2 eexists; intuition.
  eexists; intuition eauto.
Qed.

Lemma septract_sep_star_extract' :
  forall AT AEQ V (p q: @pred AT AEQ V) m,
    (exists F, F * p)%pred m ->
    q m ->
    ((p --* q) * p)%pred m.
Proof.
  intros.
  destruct_lift H.
  apply star_split in H; cleanup.
  
  unfold sep_star; rewrite sep_star_is.
  unfold sep_star_impl.
  unfold septract.
  do 2 eexists; intuition.
  eexists; intuition eauto.
Qed.

Lemma septract_sep_star_merge :
  forall AT AEQ V (p q: @pred AT AEQ V),
    (forall m m', p m -> p m' -> m = m') ->
    (p --* q) * p =p=> q.
Proof.
  unfold septract; intros.
  intros m Hm.
  apply star_split in Hm; cleanup.
  erewrite (H x0); eauto.
Qed.

Lemma ptsto_bits'_extract:
  forall l n dh a,
    a < length l + n ->
    a >= n ->
    ptsto_bits' dh l n =p=> exists vs, (((S a |-> vs) --* ptsto_bits' dh l n) * (S a |-> vs)).
Proof.
  intros.
  intros m Hm.
  edestruct ptsto_bits'_inbound; eauto.
  pred_apply' Hm; eassign dh; cancel.
  cleanup.
  exists x.
  
  eapply septract_sep_star_extract' in Hm; eauto.
  exists (diskIs (mem_except m (S a))).
  eapply diskIs_extract' in H1.
  assert (A: diskIs m m).
  unfold diskIs; eauto.
  apply H1 in A; eauto.
Qed.

Lemma ptsto_bits'_merge:
  forall l n dh a vs,
    ((S a |-> vs) --* ptsto_bits' dh l n) * (S a |-> vs) =p=> ptsto_bits' dh l n.
Proof.
  intros.
  unfold septract; intros.
  intros m Hm.
  apply star_split in Hm; cleanup.
  destruct_lift H3.
  eapply ptsto_complete in H3; eauto; subst; eauto.
Qed.

Lemma rep_eq:
  forall d s1 s2 F F',
    (F * rep s1)%pred d ->
    (F' * rep s2)%pred d ->
    s1 = s2.
Proof.
  intros.
  extensionality k.
  unfold rep in *; simpl in *.
  
  destruct_lift H; destruct_lift H0.
  assert_fresh (d 0 = Some (dummy,dummy0)).
  eapply ptsto_valid'; pred_apply' H; cancel.
  assert_fresh (d 0 = Some (dummy1,dummy2)).
  eapply ptsto_valid'; pred_apply' H0; cancel.
  cleanup.

  destruct (lt_dec k block_size).
  
  unfold ptsto_bits in *.
  eapply (@ptsto_bits'_inbound _ _ _ k) in H; try omega; cleanup.
  eapply (@ptsto_bits'_inbound _ _ _ k) in H0; try omega; cleanup.
  rewrite Nat.sub_0_r in *.
  
  destruct_fresh (nth k (bits (value_to_bits dummy1)) 0).
  rewrite H1, H6; eauto.
  destruct n; try omega.
  rewrite H2, H7; eauto.
  destruct (value_to_bits dummy1); simpl in *.
  unfold valid_bitlist in *; cleanup.
  omega.
  destruct (value_to_bits dummy1); simpl in *.
  unfold valid_bitlist in *; cleanup.
  omega.
  erewrite H4, H5; eauto; omega.   
Qed.      

Lemma ptsto_bits'_update_oob:
  forall l n dh a v,
    a >= length l + n ->
    ptsto_bits' dh l n ⇨⇨ ptsto_bits' (upd dh a v) l n.
Proof.
  eapply (rev_ind
    (fun l =>
       forall n dh a v,
    a >= length l + n ->
    ptsto_bits' dh l n ⇨⇨ ptsto_bits' (upd dh a v) l n));
    simpl in *; intros.
  cancel.
  rewrite app_length in *; simpl in *.
  rewrite ptsto_bits'_app_split; simpl in *.
  rewrite <- ptsto_bits'_app_merge; simpl.
  rewrite <- H; try omega.
  cancel.
  rewrite upd_ne; eauto.
  omega.
Qed.
  
 Lemma ptsto_bits'_update_apply:
   forall l n a v vs dh m F,
     a < length l + n ->
     a >= n ->
     m (S a) = Some vs ->
     (F * ptsto_bits' dh l n)%pred m ->
     (F * ptsto_bits' (upd dh a v) (updN l (a - n) 1) n)%pred (upd m (S a) (v, fst vs::snd vs)).
 Proof.
   eapply (rev_ind
    (fun l =>
       forall n a v vs dh m F,
         a < length l + n ->
         a >= n ->
         m (S a) = Some vs ->
         (F * ptsto_bits' dh l n)%pred m ->
         (F * ptsto_bits' (upd dh a v) (updN l (a - n) 1) n)%pred (upd m (S a) (v, fst vs::snd vs))));
     simpl in *; intros.
   omega.
   rewrite app_length in *; simpl in *.
   rewrite ptsto_bits'_app_split in H3; simpl in *.
   destruct (addr_dec a (length l + n)); subst.
   -
     rewrite Nat.add_sub.
     rewrite updN_app_tail; simpl.
     rewrite <- ptsto_bits'_app_merge; simpl.
     destruct_lift H3.
     eapply pimpl_apply.
     2: rewrite Nat.add_comm;
       eapply ptsto_upd;
       pred_apply; cancel.
     cancel.
     erewrite <- ptsto_bits'_update_oob.
     cancel.
     destruct x; cancel.
     destruct x; cancel.
     eauto.
     rewrite Nat.add_comm, upd_eq'; eauto.
   -
     rewrite updN_app1; try omega.
     rewrite <- ptsto_bits'_app_merge.
     simpl.
     rewrite length_updN.
     eapply pimpl_apply.
     2: {
       eapply H; eauto.
       omega.
       eassign dh;
         eassign (F
        ✶  ((exists vs : value * list value,
                 S (n + length l) |-> vs
                 ✶ match x with
                   | 0 => ⟦⟦ dh (n + length l) = None ⟧⟧
                   | 1 => ⟦⟦ dh (n + length l) = Some (fst vs) ⟧⟧
                   | S (S _) => ⟦⟦ False ⟧⟧
                   end) ✶ emp)).
       pred_apply; cancel.
     }
     rewrite upd_ne; try omega.
     cancel.
 Qed.

 Lemma ptsto_bits'_update_septract:
   forall l n a v vs dh,
     a < length l + n ->
     a >= n ->
     S a |-> vs --* ptsto_bits' dh l n =p=>
     S a |-> (v, fst vs::snd vs) --* ptsto_bits' (upd dh a v) (updN l (a - n) 1) n.
 Proof.

   
   intros.
   unfold septract, pimpl; intros.
   cleanup.

   unfold emp in *; simpl in *.
   assert (A: x (S a) = Some vs).
   eapply ptsto_valid'.
   pred_apply' H2; cancel.
   exists (upd x (S a) (v, fst vs :: snd vs)).
   intuition.
   apply mem_disjoint_comm.
   eapply mem_disjoint_upd; eauto.
   apply mem_disjoint_comm; eauto.
   eapply emp_star.
   eapply ptsto_upd'; pred_apply; cancel.
   rewrite mem_union_comm.
   rewrite mem_union_upd.
   apply emp_star.
   eapply ptsto_bits'_update_apply; eauto.

   apply mem_disjoint_comm in H1.
   eapply mem_union_addr in A; eauto.
   rewrite mem_union_comm; eauto.
   pred_apply; cancel.
   apply mem_disjoint_comm in H1; eauto.
   apply mem_disjoint_comm.
   eapply mem_disjoint_upd; eauto.
   apply mem_disjoint_comm; eauto.
 Qed.
   

 Lemma ptsto_bits'_update:
   forall l n a v vs dh,
     a < length l + n ->
     a >= n ->
      S a |-> vs --* ptsto_bits' dh l n
  ✶ S a |-> (v, fst vs :: snd vs)
  ⇨⇨ ptsto_bits' (upd dh a v)
  (updN l (a-n) 1) n.
 Proof.
   intros.
   rewrite ptsto_bits'_update_septract; eauto.
   rewrite ptsto_bits'_merge; eauto.
 Qed.
Require Eqdep.
Require Import List.

Module Type BaseSystem.
  Parameter state : Type.
  Parameter prog : Type -> Type.
  Parameter exec : forall T, state -> prog T -> state -> T -> Prop.
End BaseSystem.

Module Type ACLSystem.
  Parameter resource : Type.
  Parameter id : Type.
  Parameter id_dec : forall (i1 i2: id), {i1 = i2}+{i1 <> i2}.
  Parameter user : Type.
  Parameter permission : Type.
  Parameter can_access : user -> permission -> Prop.
  Parameter public_permission : permission.
  Axiom can_access_public : forall u, can_access u public_permission.
  Axiom can_access_unique :
    forall u u' p,
      p <> public_permission ->
      can_access u p ->
      can_access u' p ->
      u = u'.
  
  Definition resource_storage := id -> option (permission * resource).
  Parameter update : resource_storage -> id -> (permission * resource) -> resource_storage. 

  Axiom update_eq:
    forall rs i r,
      (update rs i r) i = Some r.

   Axiom update_neq:
     forall rs i i' r,
       i <> i' ->
       (update rs i r) i' = rs i'.

   Parameter remove : resource_storage -> id -> resource_storage. 

  Axiom remove_eq:
    forall rs i,
      (remove rs i) i = None.

   Axiom remove_neq:
     forall rs i i',
       i <> i' ->
       (remove rs i) i' = rs i'.

End ACLSystem.


Module L0 (System : BaseSystem) (ACL : ACLSystem).
  Export System ACL.

  (* 
     First layer language (L0)
     Can
       - Execute arbitrary non-confidential code
       - Write a new (perm, res) to a position. (e.g. write to disk)
       - Copy one (perm, res) to another position
       - Get public resources
       - Remove a resource from system
     Cannot
       - Get permitted resources
       - Change just permissions of resources
   *)
  
  Inductive prog : Type -> Type :=
  | Base : forall T, System.prog T -> prog T
  | Copy : id -> id -> prog unit
  | Put  : id -> permission -> resource -> prog unit
  | GetPublic : id -> prog resource
  | Remove : id -> prog unit
  | Transform : id -> (resource -> resource) -> prog unit
  | Ret : forall T, T -> prog T
  | Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.

  Inductive exec :
    forall T,
      user ->
      resource_storage -> state ->
      prog T ->
      resource_storage -> state -> T -> Prop :=

  | ExecBase :
      forall T u rs cs p cs' r,
        System.exec T cs p cs' r ->
        exec _ u rs cs (Base T p) rs cs' r
             
  | ExecCopy :
      forall u rs cs i i' r,
        rs i = Some r ->
        exec _ u rs cs (Copy i i') (update rs i' r) cs tt

  | ExecPut :
      forall u rs cs i p r,
        exec _ u rs cs (Put i p r) (update rs i (p,r)) cs tt
             
  | ExecGetPublic :
      forall u rs cs i r,
        rs i = Some r ->
        fst r = public_permission ->
        exec _ u rs cs (GetPublic i) rs cs (snd r)

  | ExecRemove :
      forall u rs cs i,
        exec _ u rs cs (Remove i) (remove rs i) cs tt

  | ExecTransform :
      forall u rs cs i r f,
        rs i = Some r ->
        exec _ u rs cs (Transform i f) (update rs i (fst r, f (snd r))) cs tt
             
  | ExecRet :
      forall T u rs cs (r: T),
        exec _ u rs cs (Ret _ r) rs cs r

  | ExecBind :
      forall T T' u (p1 : prog T) (p2: T -> prog T')
        rs cs rs' cs' rs'' cs'' v r,
        exec _ u rs cs p1 rs' cs' v ->
        exec _ u rs' cs' (p2 v) rs'' cs'' r ->
        exec _ u rs cs (Bind _ _ p1 p2) rs'' cs'' r.

 Ltac sigT_eq :=
  match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.
 
 Ltac invert_exec :=  
    match goal with
      [H: exec _ _ _ _ _ _ _ _ |- _ ] =>
      inversion H; subst; clear H; repeat sigT_eq
    end. 
  
  Definition same_positions (rs1 rs2: resource_storage):=
    forall i, rs1 i <> None <-> rs2 i <> None.

  Definition same_in_public (rs1 rs2: resource_storage):=
    forall i r,
      rs1 i = Some r ->
      (fst r) = public_permission ->
      rs2 i = Some r.
  
  Definition same_permissions (rs1 rs2: resource_storage):=
    forall i r1 r2,
      rs1 i = Some r1 ->
      rs2 i = Some r2 ->
      fst r1 = fst r2.
  
  Definition equivalent (u: user) (rs1 rs2: resource_storage):=
    same_positions rs1 rs2 /\
    (forall i r1 r2,
     rs1 i = Some r1 ->
     rs2 i = Some r2 ->
     can_access u (fst r1) ->
     r1 = r2).
  
  Definition data_noninterference {T} (p : prog T) :=
    forall u rs1 rs1' rs2 cs cs' r,
      exec _ u rs1 cs p rs1' cs' r ->
      same_positions rs1 rs2 ->
      same_in_public rs1 rs2 ->
      exists rs2',
        exec _ u rs2 cs p rs2' cs' r /\
        same_positions rs1' rs2' /\
        same_in_public rs1' rs2' /\
        (forall u', equivalent u' rs1 rs2 -> equivalent u' rs1' rs2').
      
  Theorem DNI_holds :
    forall T (p : prog T), data_noninterference p.
  Proof.
    unfold data_noninterference; induction p; intros; invert_exec.
    (* Base *)
    - eexists; intuition eauto.
      econstructor; eauto.
    (* Copy *)
    - specialize (H0 i) as Hx.
      destruct (rs2 i) eqn:D; intuition (try congruence).
      eexists; split; [econstructor; eauto| intuition eauto].
      unfold same_positions in *; intros; intuition.
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i1); eauto.
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i1); eauto.

      unfold same_in_public in *; intuition.
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *.
      inversion H2; subst.
      specialize (H1 i r H10 H4); congruence.
      rewrite update_neq in *; eauto.

      unfold equivalent, same_positions in *; intros; intuition.
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i1); eauto.
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i1); eauto.
      
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *.
      inversion H2; inversion H6; subst; eauto.       
      rewrite update_neq in *; eauto.
    (* Put *)
    - eexists; split; [econstructor; eauto| intuition eauto].
      unfold same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.

      unfold same_in_public in *; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; eauto.
      rewrite update_neq in *; eauto.

      unfold equivalent, same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto. 
    (* GetPublic *)
    - specialize (H1 i r0 H4 H8) as Hx.
      eexists; split; [econstructor; eauto| intuition eauto].
    (* Remove *)
    - eexists; split; [econstructor; eauto| intuition eauto].
      unfold same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; congruence.
      rewrite remove_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; congruence.
      rewrite remove_neq in *; eauto.
      destruct (H0 i0); eauto.

      unfold same_in_public in *; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; eauto.
      rewrite remove_neq in *; eauto.

      unfold equivalent, same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; congruence.
      rewrite remove_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; congruence.
      rewrite remove_neq in *; eauto.
      destruct (H0 i0); eauto.
      
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; congruence.
      rewrite remove_neq in *; eauto. 
    (* Transform *)
    - specialize (H0 i) as Hx.
      destruct (rs2 i) eqn:D; intuition (try congruence).
      eexists; split; [econstructor; eauto| intuition eauto].
      unfold same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.

      unfold same_in_public in *; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *.
      inversion H2; subst.
      simpl in *.
      specialize (H1 i0 r1 H10 H4); congruence.
      rewrite update_neq in *; eauto.

      unfold equivalent, same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; try congruence.
      inversion H2; inversion H6; subst; eauto.
      simpl in *.
      erewrite (H5 i0 r1 p); eauto.
      rewrite update_neq in *; eauto.
    (* Ret *)
    - eexists; intuition eauto.
      econstructor; eauto.
    (* Bind *)
    - edestruct IHp; eauto.
      intuition.
      edestruct H; eauto.
      intuition.
      eexists; intuition eauto.
      econstructor; eauto.
  Qed.
  
End L0.

  
(* 
   Restricted version of the first layer language (L0R)
   This language restricts the certain operations to accessible data only
*)  
Module L0R (System : BaseSystem) (ACL : ACLSystem).
  Export System ACL.

  Inductive prog : Type -> Type :=
  | Base : forall T, System.prog T -> prog T
  | Copy : id -> id -> prog unit
  | Put  : id -> permission -> resource -> prog unit
  | GetPublic : id -> prog resource
  | Remove : id -> prog unit
  | Transform : id -> (resource -> resource) -> prog unit
  | Ret : forall T, T -> prog T
  | Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.

  Inductive exec :
    forall T,
      user ->
      resource_storage -> state ->
      prog T ->
      resource_storage -> state -> T -> Prop :=

  | ExecBase :
      forall T u rs cs p cs' r,
        System.exec T cs p cs' r ->
        exec _ u rs cs (Base T p) rs cs' r
             
  | ExecCopy :
      forall u rs cs i i' r,
        rs i = Some r ->
        can_access u (fst r) ->
        exec _ u rs cs (Copy i i') (update rs i' r) cs tt

  | ExecPut :
      forall u rs cs i p r,
        p <> public_permission ->
        can_access u p ->
        exec _ u rs cs (Put i p r) (update rs i (p,r)) cs tt
             
  | ExecGetPublic :
      forall u rs cs i r,
        rs i = Some r ->
        fst r = public_permission ->
        exec _ u rs cs (GetPublic i) rs cs (snd r)

  | ExecRemove :
      forall u rs cs i r,
        rs i = Some r ->
        can_access u (fst r) ->
        exec _ u rs cs (Remove i) (remove rs i) cs tt

  | ExecTransform :
      forall u rs cs i r f,
        rs i = Some r ->
        fst r <> public_permission ->
        can_access u (fst r) ->
        exec _ u rs cs (Transform i f) (update rs i (fst r, f (snd r))) cs tt
             
  | ExecRet :
      forall T u rs cs (r: T),
        exec _ u rs cs (Ret _ r) rs cs r

  | ExecBind :
      forall T T' u (p1 : prog T) (p2: T -> prog T')
        rs cs rs' cs' rs'' cs'' v r,
        exec _ u rs cs p1 rs' cs' v ->
        exec _ u rs' cs' (p2 v) rs'' cs'' r ->
        exec _ u rs cs (Bind _ _ p1 p2) rs'' cs'' r.

 Ltac sigT_eq :=
  match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.
 
 Ltac invert_exec :=  
    match goal with
      [H: exec _ _ _ _ _ _ _ _ |- _ ] =>
      inversion H; subst; clear H; repeat sigT_eq
    end. 
  
  Definition same_positions (rs1 rs2: resource_storage):=
    forall i, rs1 i <> None <-> rs2 i <> None.

  Definition same_in_public (rs1 rs2: resource_storage):=
    forall i r,
      rs1 i = Some r ->
      (fst r) = public_permission ->
      rs2 i = Some r.
  
  Definition same_permissions (rs1 rs2: resource_storage):=
    forall i r1 r2,
      rs1 i = Some r1 ->
      rs2 i = Some r2 ->
      fst r1 = fst r2.
  
  Definition equivalent (u: user) (rs1 rs2: resource_storage):=
    same_positions rs1 rs2 /\
    (forall i r1 r2,
     rs1 i = Some r1 ->
     rs2 i = Some r2 ->
     can_access u (fst r1) ->
     r1 = r2).

  Definition state_noninterference {T} (p : prog T) :=
    forall u rs1 rs1' rs2 cs cs' r,
      exec _ u rs1 cs p rs1' cs' r ->
      same_positions rs1 rs2 ->
      same_permissions rs1 rs2 ->
      exists rs2',
        exec _ u rs2 cs p rs2' cs' r /\
        (forall u', equivalent u' rs1 rs2 -> equivalent u' rs1' rs2') /\
        same_positions rs1' rs2' /\
        same_permissions rs1' rs2'.

  FIX FROM HERE
      
  Theorem DNI_holds :
    forall T (p : prog T), state_noninterference p.
  Proof.
    unfold state_noninterference; induction p; intros; invert_exec.
    (* Base *)
    - eexists; intuition eauto.
      econstructor; eauto.
    (* Copy *)
    - specialize (H0 i) as Hx.
      destruct (rs2 i) eqn:D; intuition (try congruence).
      eexists; split; [econstructor; eauto| intuition eauto].
      unfold same_positions in *; intros; intuition.
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i1); eauto.
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i1); eauto.

      unfold same_in_public in *; intuition.
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *.
      inversion H2; subst.
      specialize (H1 i r H10 H4); congruence.
      rewrite update_neq in *; eauto.

      unfold equivalent, same_positions in *; intros; intuition.
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i1); eauto.
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i1); eauto.
      
      destruct (id_dec i0 i1); subst; try congruence.
      rewrite update_eq in *.
      inversion H2; inversion H6; subst; eauto.       
      rewrite update_neq in *; eauto.
    (* Put *)
    - eexists; split; [econstructor; eauto| intuition eauto].
      unfold same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.

      unfold same_in_public in *; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; eauto.
      rewrite update_neq in *; eauto.

      unfold equivalent, same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto. 
    (* GetPublic *)
    - specialize (H1 i r0 H4 H8) as Hx.
      eexists; split; [econstructor; eauto| intuition eauto].
    (* Remove *)
    - eexists; split; [econstructor; eauto| intuition eauto].
      unfold same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; congruence.
      rewrite remove_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; congruence.
      rewrite remove_neq in *; eauto.
      destruct (H0 i0); eauto.

      unfold same_in_public in *; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; eauto.
      rewrite remove_neq in *; eauto.

      unfold equivalent, same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; congruence.
      rewrite remove_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; congruence.
      rewrite remove_neq in *; eauto.
      destruct (H0 i0); eauto.
      
      destruct (id_dec i i0); subst; try congruence.
      rewrite remove_eq in *; congruence.
      rewrite remove_neq in *; eauto. 
    (* Transform *)
    - specialize (H0 i) as Hx.
      destruct (rs2 i) eqn:D; intuition (try congruence).
      eexists; split; [econstructor; eauto| intuition eauto].
      unfold same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.

      unfold same_in_public in *; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *.
      inversion H2; subst.
      simpl in *.
      specialize (H1 i0 r1 H10 H4); congruence.
      rewrite update_neq in *; eauto.

      unfold equivalent, same_positions in *; intros; intuition.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; congruence.
      rewrite update_neq in *; eauto.
      destruct (H0 i0); eauto.
      
      destruct (id_dec i i0); subst; try congruence.
      rewrite update_eq in *; try congruence.
      inversion H2; inversion H6; subst; eauto.
      simpl in *.
      erewrite (H5 i0 r1 p); eauto.
      rewrite update_neq in *; eauto.
    (* Ret *)
    - eexists; intuition eauto.
      econstructor; eauto.
    (* Bind *)
    - edestruct IHp; eauto.
      intuition.
      edestruct H; eauto.
      intuition.
      eexists; intuition eauto.
      econstructor; eauto.
  Qed.
  
End L0R.


Module L1 (System : BaseSystem) (ACL : ACLSystem).  
  Module L0 := L0 System ACL.
  Export L0.

  (* Second language layer (L1)
     Can
       - Run arbitrary L0 code
       - Get a permitted resource
     Cannot
       - Change just the permissions
   *)
  Inductive prog_basic : Type -> Type :=
  | L0 : forall T, L0.prog T -> prog_basic T
  | Get : id -> prog_basic resource.
  
  Inductive prog : Type -> Type :=
  | Ret : forall T, T -> prog T
  | Bind: forall T T', prog_basic T  -> (T -> prog T') -> prog T'.

  Inductive exec_basic :
    forall T,
      user ->
      resource_storage -> state ->
      prog_basic T ->
      resource_storage -> state -> T -> Prop :=
    
  | ExecL0 :
      forall T p u rs rs' cs cs' r,
        L0.exec _ u rs cs p rs' cs' r ->
        exec_basic _ u rs cs (L0 T p) rs' cs' r

  | ExecGet :
      forall u rs cs i r,
        rs i = Some r ->
        can_access u (fst r) ->
        exec_basic _ u rs cs (Get i) rs cs (snd r).
  
  Inductive exec :
    forall T,
      user ->
      resource_storage -> state ->
      prog T ->
      resource_storage -> state -> T -> Prop :=
             
  | ExecRet :
      forall T u rs cs (r: T),
        exec _ u rs cs (Ret _ r) rs cs r

  | ExecBind :
      forall T T' u (p1 : prog_basic T) (p2: T -> prog T')
        rs cs rs' cs' rs'' cs'' v r,
        exec_basic _ u rs cs p1 rs' cs' v ->
        exec _ u rs' cs' (p2 v) rs'' cs'' r ->
        exec _ u rs cs (Bind _ _ p1 p2) rs'' cs'' r.

  Definition state_noninterference {T} (p : prog T) :=
    forall u rs1 rs1' rs2 cs cs' r,
      exec _ u rs1 cs p rs1' cs' r ->
      same_positions rs1 rs2 ->
      same_permissions rs1 rs2 ->
      exists rs2' r',
        exec _ u rs2 cs p rs2' cs' r' /\
        (forall u', equivalent u' rs1 rs2 -> equivalent u' rs1' rs2') /\
        same_positions rs1' rs2' /\
        same_permissions rs1' rs2'.

  Definition state_noninterference_basic {T} (p : prog_basic T) :=
    forall u rs1 rs1' rs2 cs cs' r,
      exec_basic _ u rs1 cs p rs1' cs' r ->
      same_positions rs1 rs2 ->
      same_permissions rs1 rs2 ->
      exists rs2' r',
        exec_basic _ u rs2 cs p rs2' cs' r' /\
        (forall u', equivalent u' rs1 rs2 -> equivalent u' rs1' rs2') /\
        same_positions rs1' rs2' /\
        same_permissions rs1' rs2'.
  
  Definition data_noninterference {T} (p : prog T) :=
    forall u rs1 rs1' rs2 cs cs' r,
      exec _ u rs1 cs p rs1' cs' r ->
      equivalent u rs1 rs2 ->
      exists rs2',
        exec _ u rs2 cs p rs2' cs' r /\
        same_positions rs1' rs2' /\
        same_permissions rs1' rs2' /\
        (forall u', equivalent u' rs1 rs2 -> equivalent u' rs1' rs2').

  Ltac invert_exec :=  
    match goal with
      | [H: exec_basic _ _ _ _ _ _ _ _ |- _ ] =>
      inversion H; subst; clear H; repeat sigT_eq

      | [H: exec _ _ _ _ (Ret _ _) _ _ _ |- _ ] =>
        inversion H; subst; clear H; repeat sigT_eq
                                            
      | [H: exec _ _ _ _ (Bind _ _ _ _) _ _ _ |- _ ] =>
      inversion H; subst; clear H; repeat sigT_eq
    end.

  Theorem SNI_holds_basic:
    forall T (p: prog_basic T),
      state_noninterference_basic p.
  Proof.
    unfold state_noninterference_basic; induction p; intros;
    try invert_exec; try solve [invert_exec; eauto].
    admit.
    (* Get *)
    - specialize (H0 i) as Hx.
      destruct (rs2 i) eqn:D; intuition (try congruence).
      specialize (H1 i r0 p H4 D) as Hx.
      do 2 eexists; intuition eauto.
      econstructor; eauto.
      rewrite <- Hx; eauto.
  Admitted.

  Theorem SNI_holds:
    forall T (p: prog T),
      state_noninterference p.
  Proof.
    induction p; intros.
    unfold state_noninterference; intros; invert_exec.
    do 2 eexists; intuition eauto.
    econstructor; eauto.

    Lemma SNI_bind:
      forall T (p: prog_basic T) T' (p0 : T -> prog T'),
        state_noninterference_basic p ->
        (forall t, state_noninterference (p0 t)) ->
        state_noninterference (Bind T T' p p0).
    Proof.
      unfold state_noninterference, state_noninterference_basic; intros.
      invert_exec.
      edestruct H; eauto.
      destruct H1; intuition.
      repeat invert_exec.
      eapply L0.DNI_holds in H16; edestruct H16; eauto.
      admit.
      intuition.
      edestruct H0; eauto.
      admit.
      destruct H11; intuition.
      do 2 eexists; intuition eauto.
      econstructor; eauto.
      econstructor; eauto.

      

    
      move H0 after H14.
      invert_exec; eauto.
      specialize (IHp u rs1 rs'0 rs2 cs cs'1 v0 H11 _ _ _ H12).
      specialize (IHp u' H2).
      eapply H; eauto.
      edestruct IHp; eauto.
      admit.
      
    
  
  
  Theorem DNI_holds:
    forall T (p: prog T),
      data_noninterference p.
  Proof.
    induction p; intros.
    (* L0 *)
    - admit. (* apply DNI_L0_to_L1; apply L0.DNI_holds. *)
    (* Compute *)
    - unfold data_noninterference; intros; invert_exec.
      specialize (H0 i) as Hx.
      destruct (rs2 i) eqn:D; intuition (try congruence).
      specialize (H1 i r0 p H11 D) as Hx.
      eexists; split.
      econstructor.

      [econstructor; eauto|].
      rewrite <- Hx; eauto. *)
    (* Ret *)
    - admit. (* do 2 eexists; split; [econstructor; eauto| intuition eauto]. *)
    (* Bind *)
    - generalize dependent 
      edestruct IHexec1; eauto.
      destruct H3; intuition.
      edestruct IHexec2; eauto.
      destruct H6; intuition.
      do 2 eexists; split; [| intuition eauto].
      econstructor; eauto.
      
  
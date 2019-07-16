Require Import Memx Predx.

Module Plain.
Record ResourceSet := {
    id : Type;
    resource : Type;
    id_eq : forall (i i': id), {i=i'}+{i<>i'};
    resource_map := @mem id id_eq resource;
    prog : Type -> Type;
    exec : forall T, resource_map -> prog T -> resource_map -> T -> Prop;
}.

Record contracting_refinement (High Low : ResourceSet):= {
    refine_resource: (id High) -> (resource High) -> (resource_map Low);
    refine_prog : forall T T', (prog High T) -> (prog Low T');
    refine_ret : forall T T', (prog High T) -> T -> T';

    refine_resource_disjoint :
      forall hid1 hid2,
          hid1 <> hid2 ->
          forall hr1 hr2,
            @mem_disjoint _ (id_eq Low) _ (refine_resource hid1 hr1) (refine_resource hid2 hr2);
    
    refines_to (hm: resource_map High) (lm: resource_map Low) :=
      (forall hid hr,
          hm hid = Some hr ->
          exists m, lm = mem_union m (refine_resource hid hr));
    
    refinement_valid:
      forall T T' (p: prog High T) hm hm' r lm,
        (exec High) T hm p hm' r ->
        refines_to hm lm ->
        exists lm',
          (exec Low) T' lm (refine_prog T T' p) lm' (refine_ret T T' p r) /\
          refines_to hm' lm'
  }.
End Plain.

Module Owned.

Record OwnedResourceSet := {
    id : Type;
    resource : Type;
    id_eq : forall (i i': id), {i=i'}+{i<>i'};
    owner : Type;
    
    resource_map := @mem id id_eq resource;
    acl := owner -> id -> Prop;

    equivalent_for: owner -> resource_map -> resource_map -> Prop;
    
    prog : Type -> Type;
    exec : forall T, owner -> acl -> resource_map -> prog T -> acl -> resource_map -> T -> Prop;
}.

Record single_owner_contracting_refinement (High Low : OwnedResourceSet):=
  {
    refine_to_map: id High -> resource High -> resource_map Low;
    refine_prog : forall T T', (prog High) T -> (prog Low) T';
    refine_owner : owner High -> owner Low;
    refine_ret : forall T T', (prog High) T -> T -> T';

    refine_resource_disjoint :
      forall hid1 hid2,
          hid1 <> hid2 ->
          forall hr1 hr2,
            @mem_disjoint _ (id_eq Low) _ (refine_to_map hid1 hr1) (refine_to_map hid2 hr2);

    acl_refines_to (hacl: acl High) (lacl: acl Low):=
      forall hid ho hr lid,
        hacl ho hid ->
        (refine_to_map hid hr) lid <> None ->
        lacl (refine_owner ho) lid;
    
    map_refines_to (hm: resource_map High) (lm: resource_map Low) :=
      forall hid hr,
          hm hid = Some hr ->
          (exists m, lm = mem_union m (refine_to_map hid hr));

    refinement_preserves_equivalence:
      forall o hm1 hm2 lm1 lm2,
        equivalent_for High o hm1 hm2 ->
        map_refines_to hm1 lm1 ->
        map_refines_to hm2 lm2 ->
        equivalent_for Low (refine_owner o) lm1 lm2;
    
    refinement_valid:
      forall T T' o (p: prog High T) hm hm' hacl lacl hacl' r lm,
        (exec High) T o hacl hm p hacl' hm' r ->
        map_refines_to hm lm ->
        acl_refines_to hacl lacl ->
        exists lacl' lm',
          (exec Low) T' (refine_owner o) lacl lm (refine_prog T T' p) lacl' lm' (refine_ret T T' p r) /\
          map_refines_to hm' lm' /\
          acl_refines_to hacl' lacl'
  }.

Definition ret_noninterference {T} (layer: OwnedResourceSet) (p: (prog layer) T) :=
  forall o acl acl' rm1 rm2 rm1' r,
    (exec layer) _ o acl rm1 p acl' rm1' r ->
    equivalent_for layer o rm1 rm2 ->
    (exists rm2',
      exec layer _ o acl rm2 p acl' rm2' r /\
      equivalent_for layer o rm1' rm2').

Theorem ret_noninterference_transfer:
  forall High Low (refinement : single_owner_contracting_refinement High Low) T T' (p: prog High T),
    ret_noninterference Low ((refine_prog _ _ refinement) T T' p) ->
    (forall hm, exists lm, map_refines_to _ _ refinement hm lm) ->
    (forall hacl, exists lacl, acl_refines_to _ _ refinement hacl lacl) ->
    ret_noninterference High p.
Proof.
  unfold ret_noninterference; intros.
  destruct refinement; simpl in *.
  specialize (H0 rm1); destruct H0.
  specialize (H1 acl0); destruct H1.
  unfold map_refines_to, acl_refines_to in *; simpl in *.
  
  specialize refinement_valid0 with (1:= H2)(2:= H0)(3:= H1).
  specialize (refinement_valid0 T').
  destruct refinement_valid0.
  destruct H4.
  destruct H4.
  destruct H5.
Abort.
End Owned.
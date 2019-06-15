Record PolicyPrimitives := {
  user : Type;
  permission : Type
}.

Record Policy (P: PolicyPrimitives) := {
  can_access : user P -> permission P -> Prop
}.

Infix "'A?'" := can_access (at level 1): policy_scope.
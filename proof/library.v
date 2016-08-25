Require Import definitions.
Require Import String.
Open Scope string_scope.
Open Scope list_scope.

Fixpoint belongs A (x : A) list : Prop :=
match list with
| nil => False
| cons y list2 => y = x \/ belongs A x list2
end.

Definition true (Sigma : signature) (Gamma : context) (m : canonical_object) (sigma : canonical_family) : Prop :=
True.

Definition val (Sigma : signature) (Gamma : context) (m : canonical_object) (sigma : canonical_family) : Prop :=
match m with
| Atomic_c_o (App_a_o (Const_a_o s) _) => (s = "c_free") \/ (s = "c_lam")
| _ => False
end.

Fixpoint closed_canonical_family_under_list (sigma : canonical_family) (list : list string) : Prop :=
match sigma with
| Atomic_c_f tho => closed_atomic_family_under_list tho list
| Pi_c_f x sigma1 sigma2 => closed_canonical_family_under_list sigma1 (x :: list) /\ closed_canonical_family_under_list sigma2 (x :: list)
| Lock_c_f _ m sigma1 sigma2 => closed_canonical_family_under_list sigma1 list /\ closed_canonical_family_under_list sigma2 list
end

with closed_atomic_family_under_list (tho : atomic_family) (list : list string) : Prop :=
match tho with
| Const_family_a_f _ => True
| App_a_f tho1 m => closed_atomic_family_under_list tho1 list /\ closed_canonical_object_under_list m list
end

with closed_canonical_object_under_list (m : canonical_object) (list : list string) : Prop :=
match m with
| Atomic_c_o n => closed_atomic_object_under_list n list
| Lam_c_o x sigma m1 => closed_canonical_family_under_list sigma (x :: list) /\ closed_canonical_object_under_list m1 (x :: list)
| Lock_c_o _ m1 sigma m2 => closed_canonical_object_under_list m1 list /\ closed_canonical_family_under_list sigma list /\ closed_canonical_object_under_list m2 list
end

with closed_atomic_object_under_list (n : atomic_object) (list : list string) : Prop :=
match n with
| Const_a_o _ => True
| Var_a_o x => belongs string x list
| App_a_o n1 m => closed_atomic_object_under_list n1 list /\ closed_canonical_object_under_list m list
| Unlock_a_o _ m sigma n1 => closed_canonical_object_under_list m list /\ closed_canonical_family_under_list sigma list /\ closed_atomic_object_under_list n1 list
end.

Fixpoint doesnt_contain_canonical_family_constant (sigma : canonical_family) (c : string) : Prop :=
match sigma with
| Atomic_c_f tho => doesnt_contain_atomic_family_constant tho c
| Pi_c_f _ sigma1 sigma2 => doesnt_contain_canonical_family_constant sigma1 c /\ doesnt_contain_canonical_family_constant sigma2 c
| Lock_c_f _ m sigma1 sigma2 => doesnt_contain_canonical_object_constant m c /\ doesnt_contain_canonical_family_constant sigma1 c /\ doesnt_contain_canonical_family_constant sigma2 c
end

with doesnt_contain_atomic_family_constant (tho : atomic_family) (c : string) : Prop :=
match tho with
| Const_family_a_f _ => True
| App_a_f tho1 m => doesnt_contain_atomic_family_constant tho1 c /\ doesnt_contain_canonical_object_constant m c
end

with doesnt_contain_canonical_object_constant (m : canonical_object) (c : string) : Prop :=
match m with
| Atomic_c_o n => doesnt_contain_atomic_object_constant n c
| Lam_c_o _ sigma m1 => doesnt_contain_canonical_family_constant sigma c /\ doesnt_contain_canonical_object_constant m1 c
| Lock_c_o _ m1 sigma m2 => doesnt_contain_canonical_object_constant m1 c /\ doesnt_contain_canonical_family_constant sigma c /\ doesnt_contain_canonical_object_constant m2 c
end

with doesnt_contain_atomic_object_constant (n : atomic_object) (c : string) : Prop :=
match n with
| Const_a_o c1 => (c = c1) -> False
| Var_a_o _ => True
| App_a_o n1 m => doesnt_contain_atomic_object_constant n1 c /\ doesnt_contain_canonical_object_constant m c
| Unlock_a_o _ m sigma n1 => doesnt_contain_canonical_object_constant m c /\ doesnt_contain_canonical_family_constant sigma c /\ doesnt_contain_atomic_object_constant n1 c
end.

Definition qf (Sigma : signature) (Gamma : context) (m : canonical_object) (sigma : canonical_family) : Prop :=
sigma = Atomic_c_f (Const_family_a_f "bool") /\ closed_canonical_object_under_list m nil /\ doesnt_contain_canonical_object_constant m "c_forall".

Definition set (Sigma : signature) (Gamma : context) (m : canonical_object) (sigma : canonical_family) : Prop :=
sigma = Atomic_c_f (Const_family_a_f "args") /\
match m with
| Atomic_c_o (App_a_o (App_a_o (Const_a_o "c_assoc") (Atomic_c_o (Const_a_o c))) e) => closed_canonical_object_under_list e nil /\ doesnt_contain_canonical_object_constant e c
| _ => False
end.

Require Import String.
Require Import List.

Inductive signature_element : Set :=
	| Const_family_s_e : string -> kind -> signature_element
	| Const_s_e : string -> canonical_family -> signature_element

with context_element : Set :=
	| Var_c_e : string -> canonical_family -> context_element

with kind : Set :=
	| Type_k : kind
	| Pi_k : string -> canonical_family -> kind -> kind

with canonical_family : Set :=
	| Atomic_c_f : atomic_family -> canonical_family
	| Pi_c_f : string -> canonical_family -> canonical_family -> canonical_family
	| Lock_c_f : string -> canonical_object -> canonical_family -> canonical_family -> canonical_family
	| Prod_c_f : canonical_family -> canonical_family -> canonical_family

with atomic_family : Set :=
	| Const_family_a_f : string -> atomic_family
	| App_a_f : atomic_family -> canonical_object -> atomic_family

with canonical_object : Set :=
	| Atomic_c_o : atomic_object -> canonical_object
	| Lam_c_o : string -> canonical_family -> canonical_object -> canonical_object
	| Lock_c_o : string -> canonical_object -> canonical_family -> canonical_object -> canonical_object
	| Pair_c_o : canonical_object -> canonical_object -> canonical_object

with atomic_object : Set :=
	| Const_a_o : string -> atomic_object
	| Var_a_o : string -> atomic_object
	| App_a_o : atomic_object -> canonical_object -> atomic_object
	| Unlock_a_o : string -> canonical_object -> canonical_family -> atomic_object -> atomic_object.

Definition signature := list signature_element.

Definition context := list context_element.

Notation " s_e :: s " := (cons s_e s).

(*
Notation "( a -> k )" := (Const_family_s_e a k) (at level 50): signature_element.:
Notation "( c -> s )" := (Const_s_e c s) (at level 50): signature_element.
Notation "( x -> s )" := (Var_c_e x s) (at level 50): context_element.

Notation "'*'" := (Type_k): kind.
Notation "'Pi' x : s . k" := (Pi_k x s k) (at level 50): kind.

Notation "'at' tho" := (Atomic_c_f tho) (at level 50): canonical_family.  
Notation "'Pi' x : s1 . s2" := (Pi_c_f x s1 s2) (at level 50): canonical_family.
Notation "'Lock' m , s1 [ s2 ]" := (Lock_c_f m s1 s2) (at level 50): canonical_family.

Notation "( a )" := (Const_family_a_f a) (at level 50): atomic_family.
Notation "( tho m )" := (App_a_f tho m) (at level 50): atomic_family.

Notation "'at' n" := (Atomic_c_o n) (at level 50): canonical_object.
Notation "'Lam' x : s . m" := (Lam_c_o x s m) (at level 50): canonical_object.
Notation "'Lock' m1 , s [ m2 ]" := (Lock_c_o m1 s m2) (at level 50): canonical_object.

Notation "( 'C' c )" := (Const_a_o c) (at level 50): atomic_object.
Notation "( x )" := (Var_a_o x) (at level 50): atomic_object.
Notation "( n m )" := (App_a_o n m) (at level 50): atomic_object.
Notation "'Unlock' m , s [ n ]" := (Unlock_a_o m s n) (at level 50): atomic_object. 
*)

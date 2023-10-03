Require Export AFT.Ultimate.
Require Export Lattice.SubsetComplat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Global Notation "{set : X }" := (subtype_set X).
Global Notation "∅" := (emptysubtype _).

Open Scope type_scope.
Open Scope logic.
Open Scope subtype.

Notation "A ∩ B" := (binary_intersection A B) (at level 40, left associativity) : subtype.


(*******
** AF **
********)


Definition AF := ∑ A : Type, {set : A × A}.

Definition conflict_free (F : AF) (S : {set : pr1 F}) := 
  ∏ a b, S a -> S b -> ¬ ((pr2 F) (a,,b)).

Definition attackers (F : AF) (a : pr1 F) : {set : pr1 F} :=
  fun b => (pr2 F) (b,,a).

Definition attacked (F : AF) (S : {set : pr1 F}) :=
  fun b => ∃ a, S a ∧ (pr2 F) (a,,b).

Definition defends (F : AF) (S : {set : pr1 F}) (a : pr1 F) :=
  attackers a ⊆ attacked S.

Definition V2 (F : AF) := subset_complat (pr1 F).
  (* {set : pr1 F}. *)

Definition AF_iter (F : AF) : V2 F -> V2 F :=
  fun v a => ¬ (∃ b : (pr1 F), v b ∧ (pr2 F) (b,, a)).

Definition AF_ultimate (F : AF) := ultimate (@AF_iter F).

Lemma AF_ter_antimono (F : AF) : 
  antimono (@AF_iter F).
Proof.
  move => x y H.
  rewrite subset_lattice_le => t.
  rewrite subset_lattice_le in H.
  unfold AF_iter.
  move => H0 H1.
  unfold hneg in H0.
  apply H0; clear H0.
  unfold ishinh in H1.
  apply H1 => [[b [Hr Hl]]]; clear H1.
  move => P; apply; clear P.
  exists b; split; auto.
  apply (H b); auto.
Qed.  




(********
** ADF **
*********)

Definition par (A : Type) (L : {set : A × A}) (s : A) : {set : A} := fun r => L (r,,s).

Definition ADF := ∑ (A : Type) (L : {set : A × A}), (∏ (s : A), {set : (∑ S, S ⊆ par L s)}).
  


(**********************
** Logic Programming **
**********************)



Definition literal (A : Type) := A ⨿ A.
Definition pos (A : Type) : A -> literal A := ii1.
Definition neg (A : Type) : A -> literal A := ii2.
  

Definition rule (A : Type) := A × {set : literal A}.
Notation "a ← M" := ((a,, M) : rule _) (at level 70).

Definition positives (A : Type) : {set : literal A} -> {set : A} :=
  fun M a => M (pos a).


Definition negatives (A : Type) : {set : literal A} -> {set : A} :=
  fun M a => M (neg a).

Definition is_definite_rule (A : Type) (r : rule A) :=
  negatives (pr2 r) = ∅.

Definition program A := {set : rule A}.

Definition is_definite_program (A : Type) (P : program A) :=
  ∏ r, P r -> is_definite_rule r.

Definition definite_program A := ∑ P : program A, is_definite_program P.

Definition approximate' (A : Type) (P : program A) (XY : {set : A} × {set : A}) : {set : A} :=
  fun a => ∃ M, 
    P (a ← M) ∧ 
    (positives M ⊆ (pr1 XY)) ∧
    ( (∅ : {set : A}) = (negatives M) ∩ (pr2 XY) ).

Definition approximate (A : Type) (P : program A) (XY : {set : A} × {set : A}) : {set : A} × {set : A} :=
  approximate' P XY,, approximate' P (pr2 XY,, pr1 XY).


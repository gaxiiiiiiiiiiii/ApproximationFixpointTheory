Require Export AFT.Ultimate.
Require Export Lattice.SubsetComplat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Global Notation "{set : X }" := (subtype_set X).
Global Notation "∅" := (emptysubtype _).
Notation "L ^c" := (consistent_dcppo L) (at level 1).


Open Scope type_scope.
Open Scope logic.
Open Scope subtype.
Open Scope dcpo.

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

Definition AFintpr (F : AF) := subset_complat (pr1 F).
  (* {set : pr1 F}. *)

Definition pollok (F : AF) : AFintpr F -> AFintpr F :=
  fun v a => ¬ (∃ b : (pr1 F), v b ∧ (pr2 F) (b,, a)).

Definition dung F := @pollok F ∘ @pollok F.

Definition ultimate_pollok (F : AF) := ultimate (@pollok F).

Lemma pollok_antimono (F : AF) : 
  antimono (@pollok F).
Proof.
  move => x y H.
  rewrite subset_lattice_le => t.
  rewrite subset_lattice_le in H.
  unfold pollok.
  move => H0 H1.
  unfold hneg in H0.
  apply H0; clear H0.
  unfold ishinh in H1.
  apply H1 => [[b [Hr Hl]]]; clear H1.
  move => P; apply; clear P.
  exists b; split; auto.
  apply (H b); auto.
Qed.  

Lemma ultimate_pollok_spec (F : AF) p :
  pr1 (@ultimate_pollok F p) = pollok (pr21 p),, pollok (pr11 p).
Proof.
  move : (antimonotone_ultimate p (@pollok_antimono F)) => [H1 H2].
  rewrite <- H1, <- H2; auto.
Qed.

Definition is_AFstale F (p : AFintpr F) :=
  pollok p = p.

Definition is_AFcomplete F (p : (AFintpr F)^c) :=
  ultimate_pollok p = p.

Definition is_AFadmissible F (p : (AFintpr F)^c) :=
  pr1 p ≺k pr1 (ultimate_pollok p).

Definition is_AFpreferred F (p : (AFintpr F)^c) :=
  ∏ q, is_AFadmissible q -> pr1 q ≺k pr1 p.

Definition is_AFgrounded F (p : (AFintpr F)^c) :=
  p = pataraia (@ultimate_pollok F,, (ultimate_is_monotone (@pollok F))).




(********
** ADF **
*********)

Definition par (A : Type) (L : {set : A × A}) (s : A) : {set : A} := fun r => L (r,,s).

Definition ADF := ∑ (A : Type) 
                    (L : {set : A × A}) 
                    (C : (∏ (s : A), {set : {set : A} })), 
                    ∏ s S, In (C s) S -> S ⊆ par L s.

Definition ADFintpr (D : ADF) := subset_complat (pr1 D).

Definition strass (D : ADF) : ADFintpr D -> ADFintpr D :=
  fun v s => ∃ t, In (pr122 D s) t ∧ t ⊆ v.

Definition ultimate_strass (D : ADF) := ultimate (@strass D).

Definition is_ADFtwoValueIntrp D (p : ADFintpr D) :=
  strass p = p.

Definition is_ADFcomplete D (p : (ADFintpr D)^c) :=
  ultimate_strass p = p.

Definition is_ADFadmissible D (p : (ADFintpr D)^c) :=
  pr1 p ≺k pr1 (ultimate_strass p).

Definition is_ADFpreferred D (p : (ADFintpr D)^c) :=
  ∏ q, is_ADFadmissible q -> pr1 q ≺k pr1 p.

Definition is_ADFgrounded D (p : (ADFintpr D)^c) :=
  p = pataraia (@ultimate_strass D,, (ultimate_is_monotone (@strass D))).
  


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


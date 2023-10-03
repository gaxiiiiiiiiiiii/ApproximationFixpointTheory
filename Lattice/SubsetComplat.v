Require Export Lattice.Complat.

Notation "A ∩ B" := (binary_intersection A B) (at level 40, left associativity) : subtype.

Open Scope subtype.
Open Scope logic.

Definition subset_lattice (A : Type) : lattice {set : A}.
Proof.
  exists binary_intersection. 
  exists subtype_binaryunion.
      
  repeat use tpair.
  all : unfold iscomm, isassoc, isabsorb; intros.
  all : apply funextfun => t.
  all : unfold binary_intersection, subtype_binaryunion.
  - apply iscomm_hconj. 
  - apply iscomm_hdisj.
  - apply isassoc_hconj.
  - apply isassoc_hdisj.   
  - apply hconj_absorb_hdisj.
  - apply hdisj_absorb_hconj.   
Defined.

Lemma subset_lattice_le A (X Y : subset_lattice A) :
  X ≺ Y = (X ⊆ Y : hProp).
Proof.
  apply hPropUnivalence => H.  
  - simpl in H.
    rewrite <- H.
    move => x [H1 H2]; auto.
  - simpl.
    apply funextfun => x.
    apply hPropUnivalence.
    + intros [H1 _]; auto.
    + move => H1; split; eauto.
      apply H in H1; auto.
Qed.  

Definition subset_complat (A : Type) : complat {set : A}.
Proof.
  exists (subset_lattice A).
  exists (fun H x => ∃ B : {set : A}, H B ∧ B x).
  exists (fun H x => ∀ B : {set : A}, H B ⇒ B x).   
  repeat use tpair.
  all : intros.
  4 : intro; intros.
  all : rewrite subset_lattice_le => t Ht.
  - move => P; apply; clear P.
    exists a; split; auto.
  - unfold ishinh, ishinh_UU in Ht.
    apply Ht => [[B [H1 H2]]].
    apply X in H1.
    rewrite subset_lattice_le in H1.
    apply H1 in H2; auto.
  - apply (Ht a); auto.
  - move => B HB.
    apply X in HB.
    rewrite subset_lattice_le in HB.
    apply HB in Ht; auto .
Defined.



        
        
Require Export AFT.Lattice.Complat.

Section Interval.

Hypotheses lem : LEM.


Definition interval {T} {L : complat T} (x y : L) : {set : L} :=
  fun z => x ≺ z ∧ z ≺ y.  

Lemma isPredicate_interval {T} {L : complat T} (a b : L):
  isPredicate (λ x : L,  a ≺ x × x ≺ b).
Proof.  
  unfold isPredicate => x.
  apply isapropdirprod. 
  apply (propproperty (a ≺ x)).
  apply (propproperty (x ≺ b)).
Qed.  

Definition imeet {T} {L : complat T} (a b : L) :   
  binop (carrier_subset (interval a b)).
Proof.
  move => [x [xb xt]] [y [yb yt]].
  split with (meet x y); split; simpl in *.
  * apply meet_join in xb, yb.
    replace (meet x y) with (meet (join a x) (join a y)); first last.
    {rewrite xb yb; auto. }
    rewrite <- meetA, meetjoinK, meetjoinK; auto.
  * apply meet_join.
    replace (meet x y) with (meet (meet x b) (meet y b)); first last.
    {rewrite xt yt; auto. }
    rewrite meetA (meetC y b).
    rewrite <- (meetA b b y), meetI.
    rewrite <- (meetA x b y), (meetC x b), meetA, joinC, joinmeetK.
    auto.
Defined.

Definition ijoin {T} {L : complat T} (a b : L) : binop (carrier_subset (interval a b)).
Proof.
  move => [x [xb xt]] [y [yb yt]].
  split with (join x y); split.
  * simpl in *.
    apply meet_join in xb, yb.
    replace (join x y) with (join (join a x) (join a y)); first last.
    { rewrite xb yb; auto. }
    rewrite (joinC a x) joinA.
    rewrite <- (joinA a a y), joinI,  
    <- joinA, (joinC x a), joinA, meetjoinK; auto.
  * simpl in *.
    apply meet_join.
    replace (join x y) with (join (meet x b) (meet y b)); first last.
    { rewrite xt yt; auto. }
    rewrite joinA (joinC (meet _ _ ) b) (meetC y b) joinmeetK
      joinC meetC joinmeetK; auto.  
Defined.

Definition interval_lattice {T} {L : complat T} (a b : L) : 
  lattice (carrier_subset (interval a b)).
Proof.
  use tpair.
  { exact (@imeet _ _ a b). }
  use tpair.
  { exact (@ijoin _ _ a b). }
  
  repeat use tpair; simpl; unfold iscomm, isassoc, isabsorb; intros;
  apply subtypePath; auto; unfold imeet, ijoin => /=;
  try apply isPredicate_interval. 
  - apply meetC.
  - apply joinC.
  - apply meetA.
  - apply joinA.
  - apply meetjoinK.
  - apply joinmeetK.
Defined.




Lemma notallnot_ex T (P : T -> hProp) :
  ¬ (∀ x, hneg (P x)) -> ∃ x, P x.
Proof.
  move => H.
  apply negforall_to_existsneg in H; auto.
  unfold ishinh, ishinh_UU in H.
  apply H => [[x Hx]].
  move => Q; apply; clear Q.
  exists x;
  apply invimpl; auto.
  apply isaninv1.    
  unfold isdecprop.
  split; first last.
  { eapply propproperty. }
  move : (lem  (P x)) => Hl.
  induction Hl; [apply ii1 | apply ii2]; auto .
Qed.

Lemma notempty_has_elm {T : hSet} (X : {set : T}) (H : ¬ (X == emptysubtype _)) :
  ∃ x, x ∈ X.
Proof.
  apply notallnot_ex => F.
  apply H.
  move : (invweq (hsubtype_univalence X (emptysubtype _))) => [f Hf].
  apply f.
  unfold subtype_equal => x; split => H0.
  - induction (F x); auto.
  - induction H0.
Qed.  


  
Definition isup {T} {L : complat T} (a b : L) (H : a ≺ b): 
  {set : carrier_subset (interval a b)} -> carrier_subset (interval a b).
Proof.
  move => X.
  set Y : {set : L}:= (image_hsubtype X pr1).
  move : (lem (X == (emptysubtype _))) => HX.
  induction HX as [HX|HX].
  * exists a; split; auto.
    apply meetI.
  * exists (sup Y).
    split; first last.
    - apply is_sup => y.
      unfold Y, In => Hy.
      unfold image_hsubtype, ishinh, ishinh_UU in Hy.    
      apply Hy => [[[k [Hk1 Hk2]] [H1 H2]]].
      simpl in *.
      induction H1; auto.
    - apply notempty_has_elm in HX.
      unfold ishinh, ishinh_UU in HX.
      apply HX => [[[k [ak kb]] Hk]].
      apply transL with k; auto.        
      apply is_upb.
      unfold Y, In.
      move => P; apply; clear P.
      exists (k,, (ak,, kb)); split; auto.
Defined.


Definition iinf {T} {L : complat T} (a b : L) (H : a ≺ b): 
  {set : carrier_subset (interval a b)} -> carrier_subset (interval a b).
Proof.
  move => X.
  set Y : {set : L}:= (image_hsubtype X pr1).
  move : (lem (X == (emptysubtype _))) => HX.
  induction HX as [HX|HX].
  * exists b; split; auto.
    apply meetI.
  * exists (inf Y).
    split.
    - apply is_inf => y.
      unfold Y, In => Hy.
      unfold image_hsubtype, ishinh, ishinh_UU in Hy.    
      apply Hy => [[[k [Hk1 Hk2]] [H1 H2]]].
      simpl in *.
      induction H1; auto.
    - apply notempty_has_elm in HX.
      unfold ishinh, ishinh_UU in HX.
      apply HX => [[[k [ak kb]] Hk]].
      apply transL with k; auto.        
      apply is_lowb.
      unfold Y, In.
      move => P; apply; clear P.
      exists (k,, (ak,, kb)); split; auto.
Defined.   

  
Definition interval_complat {T} {L : complat T} (a b : L) (H : a ≺ b): 
  complat (carrier_subset (interval a b)).
Proof.
  split with (interval_lattice a b).
  use tpair.
  { apply isup; auto. }
  use tpair.
  { apply iinf; auto. }
  simpl. repeat use tpair.
  - move => X [x [ax xb]] => Hx.
    apply subtypePath => //=.
    apply isPredicate_interval.
    unfold isup.
    set H0 := (lem (X == (emptysubtype _))).
    induction H0; simpl; auto.
    * simpl in a0.
      rewrite a0 in Hx.
      induction Hx.
    * apply is_upb.
      unfold image_hsubtype, In.
      move => P; apply; clear P.
      exists (x,, ax,, xb); split; auto.
  - move => X [x [ax xb]] => Hx.
    apply subtypePath => //=.
    apply isPredicate_interval.
    unfold isup.
    set H0 := (lem (X == (emptysubtype _))).
    induction H0; simpl; auto.

    * apply is_sup.
      move => c.
      unfold image_hsubtype, In => Hc.
      unfold ishinh, ishinh_UU in Hc.
      apply Hc => [[[k [ak kb]] [H1 H2]]].
      unfold pr1 in *.
      induction H1.
      move : (Hx (k,, ak,, kb) H2) => H0.
      simpl in H0.
      apply base_paths in H0; auto.
  - move => X [x [ax xb]] => Hx.
    apply subtypePath => //=.
    apply isPredicate_interval.
    unfold iinf.
    set H0 := (lem (X == (emptysubtype _))).
    induction H0; simpl; auto.
    * simpl in a0.
      rewrite a0 in Hx.
      induction Hx.
    * apply is_lowb.
      unfold image_hsubtype, In.
      move => P; apply; clear P.
      exists (x,, ax,, xb); split; auto.
  - move => X [x [ax xb]] => Hx.
    apply subtypePath => //=.
    apply isPredicate_interval.
    unfold iinf.
    set H0 := (lem (X == (emptysubtype _))).
    induction H0; simpl; auto.
    * apply is_inf.
      move => c.
      unfold image_hsubtype, In => Hc.
      unfold ishinh, ishinh_UU in Hc.
      apply Hc => [[[k [ak kb]] [H1 H2]]].
      unfold pr1 in *.
      induction H1.
      move : (Hx (k,, ak,, kb) H2) => H0.
      simpl in H0.
      apply base_paths in H0; auto. 
Defined.

End Interval.


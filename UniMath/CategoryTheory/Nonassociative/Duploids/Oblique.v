(********************************************************************************

 The Duploid arising from an Adjunction

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition and proofs of oblique morphisms
 2. Definition of the oblique duploid
 3. Lemmas about the oblique duploid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.TwoSorted.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.EqualizingRequirement.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.
Local Open Scope oblique_mor.

Section oblique_defs.

  (** ** 2. Definition of the oblique duploid *)

  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.

  Definition oblique_ob := N ⨿ P.

  Definition oblique_negativise (a : oblique_ob) : N.
  Proof. induction a as [n | p]. exact n. exact (L p). Defined.
  Definition oblique_positivise (a : oblique_ob) : P.
  Proof. induction a as [n | p]. exact (R n). exact p. Defined.

  Local Notation "a '⁻'" := (oblique_negativise a) : duploid.
  Local Notation "a '⁺'" := (oblique_positivise a) : duploid.

  Definition oblique_mor' (a b : oblique_ob) := oblique_mor θ a⁺ b⁻.
  Arguments oblique_mor' / _ _.

  Lemma isaset_oblique_mor' (a b : oblique_ob) : isaset (oblique_mor' a b).
  Proof. apply isaset_oblique_mor. Qed.

  Definition oblique_identity (a : oblique_ob) : oblique_mor' a a.
  Proof.
    induction a.
    + apply oblique_negative_identity.
    + apply oblique_positive_identity.
  Defined.

  Definition oblique_compose {a b c : oblique_ob}
    (f : oblique_mor' a b) (g : oblique_mor' b c)
    : oblique_mor' a c.
  Proof.
    induction b.
    + exact (oblique_compose_positive θ f♯ g).
    + exact (oblique_compose_negative θ f g♭).
  Defined.

  Lemma oblique_left_id {a b : oblique_ob} (f : oblique_mor' a b) :
    oblique_compose (oblique_identity a) f = f.
  Proof.
    induction a;
      [apply oblique_mor_positive_path | apply oblique_mor_negative_path];
      apply id_left.
  Qed.

  Lemma oblique_right_id {a b : oblique_ob} (f : oblique_mor' a b) :
    oblique_compose f (oblique_identity b) = f.
  Proof.
    induction b;
      [apply oblique_mor_positive_path | apply oblique_mor_negative_path];
      apply id_right.
  Qed.

  Definition oblique_unital_premagmoid : unital_premagmoid.
  Proof.
    use make_unital_premagmoid.
    - use make_precategory_data.
      + exact (make_precategory_ob_mor oblique_ob oblique_mor').
      + exact oblique_identity.
      + intros a b c f g. exact (oblique_compose f g).
    - abstract (use make_is_unital_premagmoid;
                [ apply @oblique_left_id
                | apply @oblique_right_id ]).
  Defined.

  Definition oblique_unital_magmoid : unital_magmoid.
  Proof.
    apply (make_unital_magmoid oblique_unital_premagmoid).
    intros a b; apply isaset_oblique_mor'.
  Defined.

  Definition oblique_negative (a : N) : oblique_unital_magmoid := ii1 a.
  Definition oblique_positive (a : P) : oblique_unital_magmoid := ii2 a.

  Lemma oblique_negative_is_negative (a : N) : is_negative (oblique_negative a).
  Proof.
    intros b f c d g h.
    induction c; apply oblique_mor_positive_path, assoc.
  Qed.

  Lemma oblique_positive_is_positive (a : P) : is_positive (oblique_positive a).
  Proof.
    intros b f c d g h.
    induction c; apply oblique_mor_negative_path, assoc'.
  Qed.

  Lemma oblique_polarity_mapping : polarity_mapping oblique_unital_premagmoid.
  Proof.
    use make_polarity_mapping'.
    intro a; induction a as [n | p].
    - right; apply oblique_negative_is_negative.
    - left; apply oblique_positive_is_positive.
  Defined.

  Definition oblique_preduploid : preduploid :=
    make_preduploid oblique_unital_magmoid (polarity_mapping_to_has_polarities oblique_polarity_mapping).

  Definition oblique_upshift (a : oblique_preduploid) : oblique_preduploid.
  Proof.
    induction a as [n | p]; apply oblique_negative.
    - exact n.
    - exact (L p).
  Defined.

  Definition oblique_force (a : oblique_preduploid) : oblique_upshift a --> a.
  Proof.
    induction a as [n | p].
    + apply identity.
    + apply oblique_negative_identity.
  Defined.

  Definition oblique_delay (a : oblique_preduploid) : a --> oblique_upshift a.
  Proof.
    induction a as [n | p].
    + apply identity.
    + apply oblique_positive_identity.
  Defined.

  Definition oblique_downshift (a : oblique_preduploid) : oblique_preduploid.
  Proof.
    induction a as [n | p]; apply oblique_positive.
    + exact (R n).
    + exact p.
  Defined.

  Definition oblique_wrap (a : oblique_preduploid) : a --> oblique_downshift a.
  Proof.
    induction a as [n | p].
    + apply oblique_positive_identity.
    + apply identity.
  Defined.

  Definition oblique_unwrap (a : oblique_preduploid) : oblique_downshift a --> a.
  Proof.
    induction a as [n | p].
    + apply oblique_negative_identity.
    + apply identity.
  Defined.

  Lemma is_negative_oblique_upshift (a : oblique_preduploid)
    : is_negative (oblique_upshift a).
  Proof. induction a; apply oblique_negative_is_negative. Qed.

  Lemma is_positive_oblique_downshift (a : oblique_preduploid)
    : is_positive (oblique_downshift a).
  Proof. induction a; apply oblique_positive_is_positive. Qed.

  Lemma is_linear_oblique_force (a : oblique_preduploid)
    : is_linear (oblique_force a).
  Proof.
    induction a as [n | p].
    1: apply is_linear_identity.
    intros b c f g.
    induction b as [m | q].
    1: now rewrite (assoc'_negative _ (oblique_negative_is_negative _)).
    apply oblique_mor_positive_path; cbn.
    rewrite <- (φ_adj_inv_identity θ), <- φ_adj_inv_natural_precomp.
    now rewrite !id_right, oblique_mor_positive_transpose.
  Qed.

  Definition is_thunkable_oblique_wrap (a : oblique_preduploid)
    : is_thunkable (oblique_wrap a).
  Proof.
    induction a as [n | p].
    2: apply is_thunkable_identity.
    intros b c f g.
    induction b as [m | q].
    2: now rewrite (assoc'_positive _ (oblique_positive_is_positive _)).
    apply oblique_mor_negative_path; cbn.
    rewrite <- (φ_adj_identity θ), <- φ_adj_natural_postcomp.
    now rewrite !id_left, oblique_mor_negative_transpose.
  Qed.

  Lemma is_linear_oblique_delay (a : oblique_preduploid)
    : is_linear (oblique_delay a).
  Proof.
    induction a as [n | p].
    2: apply is_linear_of_positive, oblique_positive_is_positive.
    intros b c f g.
    induction b as [m | q].
    1: apply assoc'_negative, oblique_negative_is_negative.
    apply oblique_mor_positive_path; cbn.
    rewrite <- (φ_adj_inv_identity θ), <- φ_adj_inv_natural_precomp.
    now rewrite !id_right, oblique_mor_positive_transpose.
  Qed.

  Lemma is_thunkable_oblique_unwrap (a : oblique_preduploid)
    : is_thunkable (oblique_unwrap a).
  Proof.
    induction a as [n | p].
    1: apply is_thunkable_of_negative, oblique_negative_is_negative.
    intros b c f g.
    induction b as [m | q].
    2: apply assoc_positive, oblique_positive_is_positive.
    apply oblique_mor_negative_path; cbn.
    rewrite <- (φ_adj_identity θ), <- φ_adj_natural_postcomp.
    now rewrite !id_left, oblique_mor_negative_transpose.
  Qed.

  Definition is_inverse_in_precat_oblique_force_delay (a : oblique_preduploid)
    : is_inverse_in_precat (oblique_force a) (oblique_delay a).
  Proof.
    induction a as [n | p]; split; cbn.
    - apply oblique_mor_positive_path, id_left.
    - apply oblique_mor_positive_path, id_left.
    - apply oblique_mor_negative_path, id_right.
    - apply oblique_mor_positive_path, id_right.
  Qed.

  Definition is_inverse_in_precat_oblique_unwrap_wrap (a : oblique_preduploid)
    : is_inverse_in_precat (oblique_unwrap a) (oblique_wrap a).
  Proof.
    induction a as [n | p]; split; cbn.
    - apply oblique_mor_positive_path, id_left.
    - apply oblique_mor_negative_path, id_left.
    - apply oblique_mor_negative_path, id_right.
    - apply oblique_mor_negative_path, id_right.
  Qed.

  Definition has_linear_inverse_oblique_force (a : oblique_ob) : has_linear_inverse (oblique_force a).
  Proof.
    use make_has_linear_inverse.
    - apply (make_linear_mor (oblique_delay a)).
      apply is_linear_oblique_delay.
    - apply is_inverse_in_precat_oblique_force_delay.
  Defined.

  Definition has_thunkable_inverse_oblique_wrap (a : oblique_ob) : has_thunkable_inverse (oblique_wrap a).
  Proof.
    use make_has_thunkable_inverse.
    - apply (make_thunkable_mor (oblique_unwrap a)).
      apply is_thunkable_oblique_unwrap.
    - apply is_inverse_in_precat_oblique_unwrap_wrap.
  Defined.

  Definition oblique_negative_shift_data : negative_shift_data oblique_preduploid
    := (make_negative_shift_data oblique_upshift oblique_force).

  Definition oblique_negative_shift_axioms : negative_shift_axioms oblique_negative_shift_data.
  Proof.
    use make_negative_shift_axioms.
    - apply is_linear_oblique_force.
    - apply is_negative_oblique_upshift.
    - intro a; apply has_linear_inverse_oblique_force.
  Defined.

  Definition oblique_has_negative_shifts : has_negative_shifts oblique_preduploid
    := make_has_negative_shifts _ oblique_negative_shift_axioms.

  Definition oblique_positive_shift_data : positive_shift_data oblique_preduploid
    := (make_positive_shift_data oblique_downshift oblique_wrap).

  Definition oblique_positive_shift_axioms : positive_shift_axioms oblique_positive_shift_data.
  Proof.
    use make_positive_shift_axioms.
    - apply is_thunkable_oblique_wrap.
    - apply is_positive_oblique_downshift.
    - intro a; apply has_thunkable_inverse_oblique_wrap.
  Defined.

  Definition oblique_has_positive_shifts : has_positive_shifts oblique_preduploid
    := make_has_positive_shifts _ oblique_positive_shift_axioms.

  Definition oblique_has_polarity_shifts : has_polarity_shifts oblique_preduploid.
  Proof.
    use make_has_polarity_shifts.
    - apply oblique_has_negative_shifts.
    - apply oblique_has_positive_shifts.
  Defined.

  (** The oblique duploid is the duploid arising from an adjunction,
      where objects are objects in either category, and morphisms
      are the morphisms [N⟦L a⁺, b⁻⟧] (equivalently [P⟦a⁻, R b⁺⟧]). *)
  Definition oblique_duploid : duploid
    := make_duploid _ oblique_has_polarity_shifts.

  Lemma oblique_polarity_mapping_respects_shifts
    : polarity_mapping_respects_shifts (D:=oblique_duploid) oblique_polarity_mapping.
  Proof. split; intro a; induction a; reflexivity. Qed.

  (** Such a duploid is naturally split on which category the object is from. *)
  Definition oblique_split_duploid : split_duploid
    := make_split_duploid oblique_duploid
         oblique_polarity_mapping
         oblique_polarity_mapping_respects_shifts.

  (** ** 3. Lemmas about the oblique duploid *)

  (** The characterisation [is_linear_of_force_unwrap] can be expressed in terms of the counit *)
  Lemma is_linear_iff_oblique_counit_precompose {n : N} {a : oblique_duploid}
    (f : oblique_negative n --> a)
    : #(R ∙ L) (ε n) · f♭ = ε ((R ∙ L) n) · f♭  <->
        is_linear f.
  Proof.
    eapply logeq_trans;
      [|apply (is_linear_iff_force_unwrap (D:=oblique_duploid))].
    eapply logeq_trans;
      [|apply issymm_logeq, (weq_to_iff (oblique_mor_negative_path_weq θ _ _))].
    cbn.
    rewrite functor_id, !id_left.
    apply isrefl_logeq.
  Qed.

  Lemma is_linear_of_oblique_counit_precompose {n : N} {a : oblique_duploid}
    (f : oblique_negative n --> a)
    : #(R ∙ L) (ε n) · f♭ = ε ((R ∙ L) n) · f♭ ->
      is_linear f.
  Proof. apply is_linear_iff_oblique_counit_precompose. Qed.

  (** An object [n] is positive in the oblique duploid if [n] is a fixed point. *)
  Lemma is_positive_oblique_negative_iff_pre_fixed_point (n : N)
    : # (R ∙ L) (ε n) = ε ((R ∙ L) n)
      <-> is_positive (oblique_negative n).
  Proof.
    eapply logeq_trans;
      [|apply (is_positive_iff_linear_wrap (D:=oblique_duploid))].
    eapply logeq_trans;
      [|apply is_linear_iff_oblique_counit_precompose].
    cbn.
    rewrite !id_right.
    apply isrefl_logeq.
  Qed.

  Lemma is_positive_oblique_negative_of_fixed_point (n : N)
    : is_z_isomorphism (ε n) -> is_positive (oblique_negative n).
  Proof.
    intro H.
    apply is_positive_oblique_negative_iff_pre_fixed_point.
    refine (pre_comp_with_z_iso_is_inj'
              (_ : is_z_isomorphism (#(R ∙ L) (is_z_isomorphism_mor H)))
              _ _ _).
    1: apply functor_on_is_z_isomorphism, is_z_isomorphism_inv.
    intermediate_path (identity ((R ∙ L) n)).
    - rewrite <- functor_comp, <- functor_id.
      apply maponpaths.
      apply (is_z_isomorphism_is_inverse_in_precat H).
    - apply pathsinv0.
      refine (nat_trans_ax ε _ _ _ @ _).
      apply (is_z_isomorphism_is_inverse_in_precat H).
  Qed.

  (** The characterisation [is_thunkable_of_delay_wrap] can be expressed in terms of the counit *)
  Lemma is_thunkable_iff_oblique_unit_postcompose {a : oblique_duploid} {p : P}
    (f : a --> oblique_positive p)
    : f♯ · #(L ∙ R) (η p) = f♯ · η ((L ∙ R) p)
      <-> is_thunkable f.
  Proof.
    eapply logeq_trans;
      [|apply (is_thunkable_iff_delay_wrap (D:=oblique_duploid))].
    eapply logeq_trans;
      [|apply issymm_logeq, (weq_to_iff (oblique_mor_positive_path_weq θ _ _))].
    cbn.
    rewrite functor_id, !id_right.
    apply isrefl_logeq.
  Qed.

  (** An object [p] is negative in the oblique duploid if [p] is a fixed point. *)
  Lemma is_negative_oblique_positive_iff_pre_fixed_point (p : P)
    : # (L ∙ R) (η p) = η ((L ∙ R) p)
      <-> is_negative (oblique_positive p).
  Proof.
    eapply logeq_trans;
      [|apply (is_negative_iff_thunkable_force (D:=oblique_duploid))].
    eapply logeq_trans;
      [|apply is_thunkable_iff_oblique_unit_postcompose].
    cbn.
    rewrite !id_left.
    apply isrefl_logeq.
  Qed.

  Lemma is_negative_oblique_positive_of_fixed_point (p : P)
    : is_z_isomorphism (η p) -> is_negative (oblique_positive p).
  Proof.
    intro H.
    apply is_negative_oblique_positive_iff_pre_fixed_point.
    refine (post_comp_with_z_iso_is_inj
              (_ : is_z_isomorphism (#(L ∙ R) (is_z_isomorphism_mor H)))
              _ _ _).
    1: apply functor_on_is_z_isomorphism, is_z_isomorphism_inv.
    intermediate_path (identity ((L ∙ R) p)).
    - rewrite <- functor_comp, <- functor_id.
      apply maponpaths.
      apply (is_z_isomorphism_is_inverse_in_precat H).
    - refine (_ @ nat_trans_ax η _ _ _).
      apply pathsinv0, (is_z_isomorphism_is_inverse_in_precat H).
  Qed.

  (** The duploid is a category if and only if the adjunction is idempotent. *)

  Corollary is_precategory_iff_oblique_idempotent_counit
    : post_whisker ε (R ∙ L) = pre_whisker (R ∙ L) ε
      <-> is_assoc_premagmoid oblique_duploid.
  Proof.
    refine (logeq_trans _ any_is_positive_iff_assoc).
    split.
    - intros H a.
      induction a as [n | p].
      2: apply oblique_positive_is_positive.
      apply is_positive_oblique_negative_iff_pre_fixed_point.
      apply base_paths, eqtohomot in H.
      apply H.
    - intros H.
      apply nat_trans_eq; [apply homset_property|].
      intro n.
      apply is_positive_oblique_negative_iff_pre_fixed_point, H.
  Qed.

  Corollary is_precategory_iff_oblique_idempotent_unit
    : post_whisker η (L ∙ R) = pre_whisker (L ∙ R) η
      <-> is_assoc_premagmoid oblique_duploid.
  Proof.
    refine (logeq_trans _ any_is_negative_iff_assoc).
    split.
    - intros H a.
      induction a as [n | p].
      1: apply oblique_negative_is_negative.
      apply is_negative_oblique_positive_iff_pre_fixed_point.
      apply base_paths, eqtohomot in H.
      apply H.
    - intros H.
      apply nat_trans_eq; [apply homset_property|].
      intro p.
      apply is_negative_oblique_positive_iff_pre_fixed_point, H.
  Qed.

  Lemma neg_is_univalent_oblique_from_positive_and_negative
    (a : oblique_duploid) (Hpositive : is_positive a) (Hnegative : is_negative a)
    : ¬is_duploid_univalent oblique_duploid.
  Proof.
    intro ua.
    enough (Heq : (⇑a : oblique_duploid) = ⇓a). {
      apply nopathstruetofalse.
      apply (maponpaths coprodtobool) in Heq.
      induction a; exact Heq.
    }
    use (lt_iso_to_id ua).
    induction a as [n | p].
    - now use (lt_iso_downshift_of_positive (oblique_negative n : oblique_duploid)).
    - now use (lt_iso_upshift_of_negative (oblique_positive p : oblique_duploid)).
  Qed.

  Lemma neg_is_univalent_oblique_from_positive_pre_fixed_point
    (p : P) (H : # (L ∙ R) (η p) = η ((L ∙ R) p))
    : ¬is_duploid_univalent oblique_duploid.
  Proof.
    use neg_is_univalent_oblique_from_positive_and_negative.
    - exact (oblique_positive p).
    - apply oblique_positive_is_positive.
    - now apply is_negative_oblique_positive_iff_pre_fixed_point.
  Qed.

  Lemma neg_is_univalent_oblique_from_negative_pre_fixed_point
    (n : N) (H : # (R ∙ L) (ε n) = ε ((R ∙ L) n))
    : ¬is_duploid_univalent oblique_duploid.
  Proof.
    use neg_is_univalent_oblique_from_positive_and_negative.
    - exact (oblique_negative n).
    - now apply is_positive_oblique_negative_iff_pre_fixed_point.
    - apply oblique_negative_is_negative.
  Qed.

End oblique_defs.

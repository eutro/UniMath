(********************************************************************************

 The Duploid arising from an Adjunction

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition and proofs of oblique morphisms
 2. Definition of the oblique duploid
 3. Lemmas about the oblique duploid
 4. Univalence of the oblique duploid
 5. The Kleisli and CoKleisli categories as subcategories

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.CoKleisliCategory.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monads.KleisliCategory.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.TwoSorted.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.EqualizingRequirement.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Univalence.

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
    : is_negative_oblique_mor_linear θ f ≃ is_linear f.
  Proof.
    eapply weqcomp; [|apply (is_linear_iff_force_unwrap (D:=oblique_duploid))].
    eapply weqcomp; [|apply invweq, (oblique_mor_negative_path_weq θ _ _)].
    cbn. (* fold L R ε η. *)
    rewrite functor_id, !id_left.
    apply idweq.
  Qed.

  Lemma weq_linear_mor_oblique_linear_mor (n : N) (a : oblique_duploid)
    : oblique_linear_mor θ n a⁻ ≃ linear_mor (oblique_negative n) a.
  Proof.
    apply weqfibtototal; intro f.
    apply is_linear_iff_oblique_counit_precompose.
  Defined.

  Lemma is_linear_of_oblique_counit_precompose {n : N} {a : oblique_duploid}
    (f : oblique_negative n --> a)
    : is_negative_oblique_mor_linear θ f -> is_linear f.
  Proof. apply is_linear_iff_oblique_counit_precompose. Qed.

  (** An object [n] is positive in the oblique duploid if [n] is a fixed point. *)
  Lemma is_positive_oblique_negative_iff_pre_fixed_point (n : N)
    : is_negative_pre_fixed_point θ n ≃ is_positive (oblique_negative n).
  Proof.
    eapply weqcomp; [|apply (is_positive_iff_linear_wrap (D:=oblique_duploid))].
    eapply weqcomp; [|apply is_linear_iff_oblique_counit_precompose].
    cbn.
    rewrite !id_right.
    apply idweq.
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
    : is_positive_oblique_mor_thunkable θ f ≃ is_thunkable f.
  Proof.
    eapply weqcomp; [|apply (is_thunkable_iff_delay_wrap (D:=oblique_duploid))].
    eapply weqcomp; [|apply invweq, (oblique_mor_positive_path_weq θ _ _)].
    cbn.
    rewrite functor_id, !id_right.
    apply idweq.
  Qed.

  Lemma weq_thunkable_mor_oblique_thunkable_mor (a : oblique_duploid) (p : P)
    : oblique_thunkable_mor θ a⁺ p ≃ thunkable_mor a (oblique_positive p).
  Proof.
    apply weqfibtototal; intro f.
    apply is_thunkable_iff_oblique_unit_postcompose.
  Defined.

  (** An object [p] is negative in the oblique duploid if [p] is a fixed point. *)
  Lemma is_negative_oblique_positive_iff_pre_fixed_point (p : P)
    : is_positive_pre_fixed_point θ p ≃ is_negative (oblique_positive p).
  Proof.
    eapply weqcomp; [|apply (is_negative_iff_thunkable_force (D:=oblique_duploid))].
    eapply weqcomp; [|apply is_thunkable_iff_oblique_unit_postcompose].
    cbn.
    rewrite !id_left.
    apply idweq.
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

  (** ** Univalence of the oblique duploid *)

  Lemma neg_is_univalent_oblique_from_positive_and_negative
    (a : oblique_duploid) (Hpositive : is_positive a) (Hnegative : is_negative a)
    : ¬is_duploid_univalent oblique_duploid.
  Proof.
    now apply (neg_is_duploid_univalent_if_split oblique_split_duploid a).
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

  (** Positive inclusion *)
  Definition oblique_chosen_positive_ob_weq
    : ob P ≃ ob oblique_split_duploid⁺ᶜₜ.
  Proof.
    use weq_iso.
    - intro p.
      exists (oblique_positive p,, oblique_positive_is_positive p).
      reflexivity.
    - intros [[a Ha₀] Ha].
      induction a as [n | p].
      1: apply fromempty, nopathsfalsetotrue, Ha.
      exact p.
    - easy.
    - abstract (
          intros [[a Ha₀] Ha];
          do 2 apply carrier_eq;
          induction a as [n | p];
          [apply fromempty, nopathsfalsetotrue, Ha | reflexivity]).
  Defined.

  Lemma positive_to_oblique_duploid : P ⟶ oblique_split_duploid⁺ᶜₜ.
  Proof.
    use make_functor.
    1: use make_functor_data.
    - intro p.
      exact (oblique_chosen_positive_ob_weq p).
    - intros p q f.
      refine ((_,,tt),,tt).
      refine (weq_thunkable_mor_oblique_thunkable_mor _ _ _).
      exact (oblique_lift_positive' θ f).
    - abstract (
          apply make_is_functor;
          [intros p | intros p q r f g]; cbn;
          do 3 apply carrier_eq;
          apply oblique_mor_negative_path;
          [apply functor_id | apply functor_comp]).
  Defined.

  Lemma split_essentially_surjective_positive_to_oblique_duploid
    : split_essentially_surjective positive_to_oblique_duploid.
  Proof.
    intro a.
    exists (invweq oblique_chosen_positive_ob_weq a).
    apply idtoiso, homotweqinvweq.
  Defined.

  Lemma isweq_on_objects_positive_to_oblique_duploid
    : isweq (functor_on_objects positive_to_oblique_duploid).
  Proof. apply weqproperty. Defined.

  Lemma fully_faithful_iff_positive_equalizing_positive_to_oblique_duploid
    : is_positive_equalizing θ ≃ fully_faithful positive_to_oblique_duploid.
  Proof.
    apply invweq.
    eapply weqcomp; [|apply is_positive_equalizing_weq_isweq_oblique_lift_positive].
    apply weqonsecfibers; intro p.
    apply weqonsecfibers; intro q.
    eapply weqcomp. {
      unshelve apply (weqonsecbase (X:=oblique_thunkable_mor θ p q)).
      do 2 (eapply weqcomp; [|apply invweq, weqtotalsubtype]).
      apply (weq_thunkable_mor_oblique_thunkable_mor (oblique_positive p) q).
    }
    apply weqonsecfibers; intro f.
    apply weq_iscontrweqf.
    apply weqfibtototal; intro f'.
    do 2 (eapply weqcomp; [apply subtypeInjectivity; intro; apply isapropunit|]).
    eapply weqcomp; [apply subtypeInjectivity; intro; apply propproperty|].
    eapply weqcomp; [|apply invweq, subtypeInjectivity; intro; apply propproperty].
    exact (idweq _).
  Qed.

  Lemma adj_equiv_of_cats_iff_positive_equalizing_positive_to_oblique_duploid
    : is_positive_equalizing θ
        <-> adj_equivalence_of_cats positive_to_oblique_duploid.
  Proof.
    split; intro H.
    - apply rad_equivalence_of_cats'.
      + apply fully_faithful_iff_positive_equalizing_positive_to_oblique_duploid, H.
      + apply split_essentially_surjective_positive_to_oblique_duploid.
    - apply fully_faithful_iff_positive_equalizing_positive_to_oblique_duploid.
      apply FullyFaithful.fully_faithful_from_equivalence, H.
  Qed.

  Lemma is_catiso_positive_to_oblique_duploid
    (Heq : is_positive_equalizing θ)
    : is_catiso positive_to_oblique_duploid.
  Proof.
    split.
    - apply fully_faithful_iff_positive_equalizing_positive_to_oblique_duploid, Heq.
    - apply isweq_on_objects_positive_to_oblique_duploid.
  Defined.

  Definition positive_eq_oblique_duploid_positive_linear
    (Heq : is_positive_equalizing θ)
    : P = oblique_split_duploid ⁺ᶜₜ
    := catiso_to_category_path (_,, is_catiso_positive_to_oblique_duploid Heq).

  (** Negative inclusion *)
  Definition oblique_chosen_negative_ob_weq
    : ob N ≃ ob oblique_split_duploid⁻ᶜₗ.
  Proof.
    use weq_iso.
    - intro n.
      exists (oblique_negative n,, oblique_negative_is_negative n).
      reflexivity.
    - intros [[a Ha₀] Ha].
      induction a as [n | p].
      2: apply fromempty, nopathstruetofalse, Ha.
      exact n.
    - easy.
    - abstract (
          intros [[a Ha₀] Ha];
          do 2 apply carrier_eq;
          induction a as [n | p];
          [reflexivity | apply fromempty, nopathstruetofalse, Ha]).
  Defined.

  Lemma negative_to_oblique_duploid : N ⟶ oblique_split_duploid⁻ᶜₗ.
  Proof.
    use make_functor.
    1: use make_functor_data.
    - intro n.
      exact (oblique_chosen_negative_ob_weq n).
    - intros n m f.
      refine ((_,,tt),,tt).
      refine (weq_linear_mor_oblique_linear_mor _ _ _).
      exact (oblique_lift_negative' θ f).
    - abstract (
          apply make_is_functor;
          [intros n | intros n m r f g]; cbn;
          do 3 apply carrier_eq;
          apply oblique_mor_positive_path;
          [apply functor_id | apply functor_comp]).
  Defined.

  Lemma split_essentially_surjective_negative_to_oblique_duploid
    : split_essentially_surjective negative_to_oblique_duploid.
  Proof.
    intro a.
    exists (invweq oblique_chosen_negative_ob_weq a).
    apply idtoiso, homotweqinvweq.
  Defined.

  Lemma isweq_on_objects_negative_to_oblique_duploid
    : isweq (functor_on_objects negative_to_oblique_duploid).
  Proof. apply weqproperty. Defined.

  Lemma fully_faithful_iff_negative_equalizing_negative_to_oblique_duploid
    : is_negative_equalizing θ ≃ fully_faithful negative_to_oblique_duploid.
  Proof.
    apply invweq.
    eapply weqcomp; [|apply is_negative_equalizing_weq_isweq_oblique_lift_negative].
    apply weqonsecfibers; intro n.
    apply weqonsecfibers; intro m.
    eapply weqcomp. {
      unshelve apply (weqonsecbase (X:=oblique_linear_mor θ n m)).
      do 2 (eapply weqcomp; [|apply invweq, weqtotalsubtype]).
      apply (weq_linear_mor_oblique_linear_mor n (oblique_negative m)).
    }
    apply weqonsecfibers; intro f.
    apply weq_iscontrweqf.
    apply weqfibtototal; intro f'.
    do 2 (eapply weqcomp; [apply subtypeInjectivity; intro; apply isapropunit|]).
    eapply weqcomp; [apply subtypeInjectivity; intro; apply propproperty|].
    eapply weqcomp; [|apply invweq, subtypeInjectivity; intro; apply propproperty].
    exact (idweq _).
  Qed.

  Lemma adj_equiv_of_cats_iff_negative_equalizing_negative_to_oblique_duploid
    : is_negative_equalizing θ
        <-> adj_equivalence_of_cats negative_to_oblique_duploid.
  Proof.
    split; intro H.
    - apply rad_equivalence_of_cats'.
      + apply fully_faithful_iff_negative_equalizing_negative_to_oblique_duploid, H.
      + apply split_essentially_surjective_negative_to_oblique_duploid.
    - apply fully_faithful_iff_negative_equalizing_negative_to_oblique_duploid.
      apply FullyFaithful.fully_faithful_from_equivalence, H.
  Qed.

  Lemma is_catiso_negative_to_oblique_duploid
    (Heq : is_negative_equalizing θ)
    : is_catiso negative_to_oblique_duploid.
  Proof.
    split.
    - apply fully_faithful_iff_negative_equalizing_negative_to_oblique_duploid, Heq.
    - apply isweq_on_objects_negative_to_oblique_duploid.
  Defined.

  Definition negative_eq_oblique_duploid_negative_thunkable
    (Heq : is_negative_equalizing θ)
    : N = oblique_split_duploid ⁻ᶜₗ
    := catiso_to_category_path (_,, is_catiso_negative_to_oblique_duploid Heq).

  (** Split univalence *)
  Lemma is_univalent_split_oblique_duploid
    (Heq : is_fully_equalizing θ)
    (Hpositive : is_univalent P)
    (Hnegative : is_univalent N)
    : is_split_duploid_univalent oblique_split_duploid.
  Proof.
    split; eapply transportf_is_univalent_over_catiso.
    - exact (_,, is_catiso_positive_to_oblique_duploid Heq).
    - assumption.
    - exact (_,, is_catiso_negative_to_oblique_duploid Heq).
    - assumption.
  Qed.

  Lemma is_univalent_split_oblique_duploid_inv
    (Heq : is_fully_equalizing θ)
    (Hunivalent : is_split_duploid_univalent oblique_split_duploid)
    : is_univalent P × is_univalent N.
  Proof.
    induction Hunivalent as [Hpos Hneg].
    split; eapply transportb_is_univalent_over_catiso.
    - exact (_,, is_catiso_positive_to_oblique_duploid Heq).
    - assumption.
    - exact (_,, is_catiso_negative_to_oblique_duploid Heq).
    - assumption.
  Qed.

  (** ** The Kleisli and CoKleisli categories as subcategories *)

  (** Kleisli *)
  Definition kleisli_to_oblique_duploid_data
    : functor_data (Kleisli_cat_monad (Monad_from_adjunction θ)) oblique_split_duploid⁺ᶜ.
  Proof.
    use make_functor_data.
    - intro p.
      exists (oblique_positive p,, oblique_positive_is_positive p).
      reflexivity.
    - intros p q.
      refine (pr1weq _).
      eapply weqcomp; [|apply invweq, weqtotalsubtype].
      eapply weqcomp; [|apply weq_mor_to_positive_category].
      apply weq_oblique_mor_from_positive.
  Defined.

  Lemma is_functor_kleisli_to_oblique_duploid
    : is_functor kleisli_to_oblique_duploid_data.
  Proof.
    use make_is_functor.
    - intro p.
      do 3 apply carrier_eq.
      now apply oblique_mor_positive_path.
    - intros p q r f g.
      do 3 apply carrier_eq.
      apply oblique_mor_positive_path.
      etrans; [|apply cancel_precomposition, pathsinv0, functor_comp].
      reflexivity.
  Qed.

  Definition kleisli_to_oblique_duploid
    : functor (Kleisli_cat_monad (Monad_from_adjunction θ)) oblique_split_duploid⁺ᶜ
    := make_functor _ is_functor_kleisli_to_oblique_duploid.

  Definition fully_faithful_kleisli_to_oblique_duploid
    : fully_faithful kleisli_to_oblique_duploid.
  Proof. intros p q; apply weqproperty. Defined.

  Definition isweq_on_objects_kleisli_to_oblique_duploid
    : isweq (functor_on_objects kleisli_to_oblique_duploid).
  Proof.
    use isweq_iso.
    - intros [[a Ha₀] Ha].
      induction a as [n | p].
      1: apply fromempty, nopathsfalsetotrue, Ha.
      exact p.
    - easy.
    - abstract (
          intros [[a Ha₀] Ha];
          do 2 apply carrier_eq;
          induction a as [n | p];
          [apply fromempty, nopathsfalsetotrue, Ha | reflexivity]).
  Defined.

  Definition is_catiso_kleisli_to_oblique_duploid
    : is_catiso kleisli_to_oblique_duploid.
  Proof.
    split.
    - exact fully_faithful_kleisli_to_oblique_duploid.
    - exact isweq_on_objects_kleisli_to_oblique_duploid.
  Defined.

  Definition catiso_kleisli_to_oblique_duploid
    : catiso (Kleisli_cat_monad (Monad_from_adjunction θ)) oblique_split_duploid⁺ᶜ
    := _,, is_catiso_kleisli_to_oblique_duploid.

  (** CoKleisli *)
  Definition cokleisli_to_oblique_duploid_data
    : functor_data (Cokleisli_cat_monad (Comonad_from_adjunction θ)) oblique_split_duploid⁻ᶜ.
  Proof.
    use make_functor_data.
    - intro n.
      exists (oblique_negative n,, oblique_negative_is_negative n).
      reflexivity.
    - intros n m.
      refine (pr1weq _).
      eapply weqcomp; [|apply invweq, weqtotalsubtype].
      eapply weqcomp; [|apply weq_mor_to_negative_category].
      apply weq_oblique_mor_from_negative.
  Defined.

  Lemma is_functor_cokleisli_to_oblique_duploid
    : is_functor cokleisli_to_oblique_duploid_data.
  Proof.
    use make_is_functor.
    - intro n.
      do 3 apply carrier_eq.
      now apply oblique_mor_negative_path.
    - intros n m r f g.
      do 3 apply carrier_eq.
      apply oblique_mor_negative_path.
      etrans; [|apply cancel_postcomposition, pathsinv0, functor_comp].
      reflexivity.
  Qed.

  Definition cokleisli_to_oblique_duploid
    : functor (Cokleisli_cat_monad (Comonad_from_adjunction θ)) oblique_split_duploid⁻ᶜ
    := make_functor _ is_functor_cokleisli_to_oblique_duploid.

  Definition fully_faithful_cokleisli_to_oblique_duploid
    : fully_faithful cokleisli_to_oblique_duploid.
  Proof. intros p q; apply weqproperty. Defined.

  Definition isweq_on_objects_cokleisli_to_oblique_duploid
    : isweq (functor_on_objects cokleisli_to_oblique_duploid).
  Proof.
    use isweq_iso.
    - intros [[a Ha₀] Ha].
      induction a as [n | p].
      2: apply fromempty, nopathstruetofalse, Ha.
      exact n.
    - easy.
    - abstract (
          intros [[a Ha₀] Ha];
          do 2 apply carrier_eq;
          induction a as [n | p];
          [reflexivity | apply fromempty, nopathstruetofalse, Ha]).
  Defined.

  Definition is_catiso_cokleisli_to_oblique_duploid
    : is_catiso cokleisli_to_oblique_duploid.
  Proof.
    split.
    - exact fully_faithful_cokleisli_to_oblique_duploid.
    - exact isweq_on_objects_cokleisli_to_oblique_duploid.
  Defined.

  Definition catiso_cokleisli_to_oblique_duploid
    : catiso (Cokleisli_cat_monad (Comonad_from_adjunction θ)) oblique_split_duploid⁻ᶜ
    := _,, is_catiso_cokleisli_to_oblique_duploid.

End oblique_defs.

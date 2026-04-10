(********************************************************************************

 The Duploid from a Category

 Author: B. Szilvasy
 January 2026

 Contents:
 TODO

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.FromCategory.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.EqualizingRequirement.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Envelope.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.
Local Open Scope oblique_mor.

Section from_category_def.
  Context (C : category).

  Definition category_has_polarities : has_polarities C.
  Proof.
    intro a.
    apply hinhpr, ii1, is_negative_of_precategory.
  Qed.

  Definition category_as_preduploid : preduploid
    := make_preduploid C category_has_polarities.

  Definition category_has_polarity_shifts : has_polarity_shifts C.
  Proof.
    use make_has_polarity_shifts.
    - use make_has_negative_shifts;
        [ use make_negative_shift_data | use make_negative_shift_axioms ].
      + use idfun.
      + use identity.
      + use is_linear_identity.
      + use is_negative_of_precategory.
      + use has_linear_inverse_identity.
    - use make_has_positive_shifts;
        [ use make_positive_shift_data | use make_positive_shift_axioms ].
      + use idfun.
      + use identity.
      + use is_thunkable_identity.
      + use is_positive_of_precategory.
      + use has_thunkable_inverse_identity.
  Defined.

  Definition category_as_duploid : duploid
    := make_duploid category_as_preduploid category_has_polarity_shifts.

  Definition catiso_category_as_duploid_positive_category
    : catiso C⁺ C.
  Proof.
    simple refine (make_functor (make_functor_data _ _) (make_is_functor _ _) ,,_,,_).
    - exact weq_positive_ob_to_ob_of_category.
    - intros a b; cbn in a, b; use pr1weq.
      intermediate_weq (linear_mor (M:=C) a b).
      + use weqtotalsubtype.
      + use weq_linear_mor_to_mor_of_category.
    - easy.
    - easy.
    - intros a b; use weqproperty.
    - use weqproperty.
  Defined.

  Definition catiso_category_as_duploid_positive_thunkable_category
    : catiso C⁺ₜ C.
  Proof.
    simple refine (make_functor (make_functor_data _ _) (make_is_functor _ _) ,,_,,_).
    - exact weq_positive_ob_to_ob_of_category.
    - intros a b; cbn in a, b; use pr1weq.
      intermediate_weq (thunkable_mor (M:=C) a b).
      + use weqtotalsubtype.
      + use weq_thunkable_mor_to_mor_of_category.
    - easy.
    - easy.
    - intros a b; use weqproperty.
    - use weqproperty.
  Defined.

  Definition catiso_category_as_duploid_negative_category
    : catiso C⁻ C.
  Proof.
    simple refine (make_functor (make_functor_data _ _) (make_is_functor _ _) ,,_,,_).
    - exact weq_negative_ob_to_ob_of_category.
    - intros a b; cbn in a, b; use pr1weq.
      intermediate_weq (thunkable_mor (M:=C) a b).
      + use weqtotalsubtype.
      + use weq_thunkable_mor_to_mor_of_category.
    - easy.
    - easy.
    - intros a b; use weqproperty.
    - use weqproperty.
  Defined.

  Definition catiso_category_as_duploid_negative_linear_category
    : catiso C⁻ₗ C.
  Proof.
    simple refine (make_functor (make_functor_data _ _) (make_is_functor _ _) ,,_,,_).
    - exact weq_negative_ob_to_ob_of_category.
    - intros a b; cbn in a, b; use pr1weq.
      intermediate_weq (linear_mor (M:=C) a b).
      + use weqtotalsubtype.
      + use weq_linear_mor_to_mor_of_category.
    - easy.
    - easy.
    - intros a b; use weqproperty.
    - use weqproperty.
  Defined.

  Definition catiso_category_as_duploid_linear_thunkable_category
    : catiso C ₗₜ C.
  Proof.
    simple refine (make_functor (make_functor_data _ _) (make_is_functor _ _) ,,_,,_).
    - use idweq.
    - intros a b; cbn in a, b; use pr1weq.
      apply weqpr1; intro f.
      apply (iscontraprop1 (propproperty _)).
      use make_is_linear_and_thunkable;
        [ use is_linear_of_precategory
        | use is_thunkable_of_precategory ].
    - easy.
    - easy.
    - intros a b; use weqproperty.
    - use weqproperty.
  Defined.

  Lemma is_univalent_category_as_duploid' (H : is_univalent C)
    : is_duploid_univalent category_as_duploid.
  Proof.
    use is_duploid_univalent_from_is_univalent_linear_and_thunkable_category.
    refine (transportf _ _ H).
    apply pathsinv0, catiso_to_category_path,
      catiso_category_as_duploid_linear_thunkable_category.
  Qed.
End from_category_def.

Section envelope_duploid.
  Context {N P : category} (θ : adjunction P N).

  Definition positive_category_to_envelope_duploid
    : category_as_duploid P ⟶d envelope_duploid θ.
  Proof.
    use make_duploid_functor.
    - exact (positive_category_to_envelope_duploid θ ∙
               positive_thunkable_category_to_thunkable_category _ ∙
               thunkable_category_to_unital_magmoid _).
    - abstract (use make_preserves_linearity_and_thunkability;
                intros a b f _;
                use linear_and_thunkable_mor_is_linear_and_thunkable).
  Defined.

  Definition negative_category_to_envelope_duploid
    : category_as_duploid N ⟶d envelope_duploid θ.
  Proof.
    use make_duploid_functor.
    - exact (negative_category_to_envelope_duploid θ ∙
               negative_linear_category_to_linear_category _ ∙
               linear_category_to_unital_magmoid _).
    - abstract (use make_preserves_linearity_and_thunkability;
                intros a b f _;
                use linear_and_thunkable_mor_is_linear_and_thunkable).
  Defined.

  Lemma fully_faithful_negative_category_to_envelope_duploid_from_idempotent
    (H : ∏ (n : N), is_z_isomorphism (adjcounit θ n))
    : fully_faithful negative_category_to_envelope_duploid.
  Proof.
    intros a b.
    use isweq_iso.
    - intro f; exact (is_z_isomorphism_mor (H a) · f♭).
    - abstract (
          intro f;
          etrans; [apply assoc|];
          now apply remove_id_left; [apply is_z_isomorphism_is_inverse_in_precat|]).
    - abstract (
          intro f;
          apply oblique_mor_negative_path;
          etrans; [apply assoc|];
          now apply remove_id_left; [apply is_z_isomorphism_is_inverse_in_precat|]).
  Defined.

End envelope_duploid.

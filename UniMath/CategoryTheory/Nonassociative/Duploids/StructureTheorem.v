(********************************************************************************

 The Structure Theorem for Duploids

 Author: B. Szilvasy
 February 2026

 The first part of the structure theorem states that all duploids are equivalent
 to the envelope duploid of the [⇑ ⊣ ⇓] adjunction.

 Contents:
 1. All duploids arise from an adjunction

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.HomIsos.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Oblique.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.TwoSorted.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.ShiftFunctors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.ShiftFacts.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Envelope.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.EqualizingRequirement.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.EpisAndMonics.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.
Local Open Scope oblique_mor.

(** ** 1. All duploids arise from an adjunction *)

Section envelope_equiv.
  Context (D : duploid).
  Let θ := left_adjoint_to_adjunction (are_adjoints_upshift_downshift_negative_linear_to_positive_thunkable D).
  Let D' := envelope_duploid θ.

  Definition duploid_to_envelope_on_shifts_oblique_mor (a : ob D) : D⁻ₗ⟦⇑⇓a, ⇑a⟧.
  Proof.
    apply (#(upshift_linear_to_negative_linear D)).
    exists (unwrap a).
    apply is_linear_unwrap.
  Defined.

  Definition duploid_to_envelope_on_shifts_oblique_mor' (a : ob D) : D⁺ₜ⟦⇓a, ⇓⇑a⟧.
  Proof.
    apply (#(downshift_thunkable_to_positive_thunkable D)).
    exists (delay a).
    apply is_thunkable_delay.
  Defined.

  Lemma duploid_to_envelope_on_shifts_oblique_mor_eq (a : ob D)
    : φ_adj θ (duploid_to_envelope_on_shifts_oblique_mor a)
      = duploid_to_envelope_on_shifts_oblique_mor' a.
  Proof.
    do 2 apply carrier_eq; cbn.
    etrans; [apply assoc'_negative, (⇑_)|].
    etrans; [apply cancel_precomposition, pathsinv0, wrap_natural|].
    etrans; [apply assoc_negative, (⇑_)|].
    etrans; [apply cancel_postcomposition, pathsinv0, delay_natural|].
    etrans; [apply assoc'_thunkable, (unwrap _)|].
    reflexivity.
  Qed.

  Definition duploid_to_envelope_on_shifts_preob (a : ob D) : envelope_preob θ.
  Proof.
    apply (make_envelope_preob θ (⇓a) (⇑a)).
    use make_oblique_mor_negative.
    - exact (duploid_to_envelope_on_shifts_oblique_mor a).
    - exact (duploid_to_envelope_on_shifts_oblique_mor' a).
    - apply duploid_to_envelope_on_shifts_oblique_mor_eq.
  Defined.

  Definition envelope_on_shifts_chosen_negative_of_is_negative (a : ob D)
    (Hn : is_negative a)
    : envelope_chosen_negative θ (duploid_to_envelope_on_shifts_preob a).
  Proof.
    use make_is_z_isomorphism.
    - refine (_,,tt); cbn.
      apply (#(downshift_thunkable_to_thunkable D)).
      exists (force a).
      apply is_thunkable_force_of_negative, Hn.
    - abstract (
          use make_is_inverse_in_precat;
          first [
              do 2 apply carrier_eq; cbn;
              etrans; [apply pathsinv0, downshiftf_comp, is_thunkable_delay|];
              etrans; [|apply downshiftf_id];
              apply maponpaths, delay_force_id
            | do 2 apply carrier_eq; cbn;
              etrans; [apply pathsinv0, downshiftf_comp, is_thunkable_force_of_negative, Hn|];
              etrans; [|apply downshiftf_id];
              apply maponpaths, force_delay_id]).
  Defined.

  Definition envelope_on_shifts_chosen_positive_of_is_positive (a : ob D)
    (Hp : is_positive a)
    : envelope_chosen_positive θ (duploid_to_envelope_on_shifts_preob a).
  Proof.
    use make_is_z_isomorphism.
    - refine (_,,tt).
      apply (#(upshift_linear_to_linear D)).
      exists (wrap a).
      apply is_linear_wrap_of_positive, Hp.
    - abstract (
          use make_is_inverse_in_precat;
          first [
              do 2 apply carrier_eq; cbn;
              etrans; [apply pathsinv0, upshiftf_comp, is_linear_unwrap|];
              etrans; [|apply upshiftf_id];
              apply maponpaths, wrap_unwrap_id
            | do 2 apply carrier_eq; cbn;
              etrans; [apply pathsinv0, upshiftf_comp, is_linear_wrap_of_positive, Hp|];
              etrans; [|apply upshiftf_id];
              apply maponpaths, unwrap_wrap_id]).
  Defined.

  Definition duploid_to_envelope_on_shifts_envelope_polarization (a : ob D)
    : envelope_polarization θ (duploid_to_envelope_on_shifts_preob a).
    apply (has_polarity_rec (polarity_of D a)).
    - apply isaprop_envelope_polarization.
    - intro Hn.
      apply hinhpr, ii1.
      apply envelope_on_shifts_chosen_negative_of_is_negative, Hn.
    - intro Hp.
      apply hinhpr, ii2.
      apply envelope_on_shifts_chosen_positive_of_is_positive, Hp.
  Defined.

  Definition duploid_to_envelope_on_shifts_ob (a : ob D) : envelope_ob θ.
  Proof.
    use make_envelope_ob.
    - exact (duploid_to_envelope_on_shifts_preob a).
    - exact (duploid_to_envelope_on_shifts_envelope_polarization a).
  Defined.

  Definition duploid_to_envelope_on_shifts_envelope_mor (a b : ob D)
    (f : a --> b)
    : envelope_mor θ
        (duploid_to_envelope_on_shifts_ob a)
        (duploid_to_envelope_on_shifts_ob b).
  Proof.
    use make_oblique_mor_negative.
    - refine (_,,tt).
      apply (#(upshift_linear_to_linear D)).
      exact (positive_lift f).
    - refine (_,,tt).
      apply (#(downshift_thunkable_to_thunkable D)).
      exact (negative_lift f).
    - abstract (
          do 2 apply carrier_eq; cbn;
          etrans; [apply assoc'_negative, (⇑_)|];
          etrans; [apply cancel_precomposition, pathsinv0, wrap_natural|];
          etrans; [apply assoc_negative, (⇑_)|];
          etrans; [apply cancel_postcomposition, pathsinv0, delay_natural|];
          apply (is_epi_wrap' D D);
          etrans; [apply assoc_thunkable, (wrap _)|];
          etrans; [apply cancel_postcomposition, assoc_thunkable, (wrap _)|];
          etrans; [apply cancel_postcomposition, cancel_postcomposition, positive_lift_factors'|];
          etrans; [|apply wrap_natural];
          reflexivity).
  Defined.

  Definition duploid_to_envelope_on_shifts_data
    : functor_data D D'.
  Proof.
    use make_functor_data.
    - apply duploid_to_envelope_on_shifts_ob.
    - apply duploid_to_envelope_on_shifts_envelope_mor.
  Defined.

  Definition duploid_to_envelope_on_shifts_is_functor
    : is_functor duploid_to_envelope_on_shifts_data.
  Proof.
    use make_is_functor.
    - intro a.
      apply oblique_mor_negative_path.
      do 2 apply carrier_eq; cbn.
      apply maponpaths, magmoid_id_right.
    - intros a b c f g.
      cbn.
      unfold duploid_to_envelope_on_shifts_envelope_polarization.
      pattern (polarity_of D b).
      apply (has_polarity_rec' (polarity_of D b)).
      + intro; apply isaset_oblique_mor.
      + intro Hn.
        apply oblique_mor_positive_path.
        do 2 apply carrier_eq; cbn.
        etrans; [|apply cancel_postcomposition, downshiftf_comp, is_thunkable_negative_lift'].
        etrans; [|apply downshiftf_comp, is_thunkable_of_negative, Hn].
        apply maponpaths.
        apply pathsinv0, negative_lift_unique.
        etrans; [apply cancel_postcomposition, cancel_postcomposition, negative_lift_factors|].
        etrans; [apply assoc'_negative, Hn|].
        apply cancel_precomposition, negative_lift_factors.
      + intro Hp.
        apply oblique_mor_negative_path.
        do 2 apply carrier_eq; cbn.
        etrans; [|apply cancel_precomposition, upshiftf_comp, is_linear_positive_lift'].
        etrans; [|apply upshiftf_comp, is_linear_of_positive, Hp].
        apply maponpaths.
        apply pathsinv0, positive_lift_unique.
        etrans; [apply cancel_precomposition, cancel_precomposition, positive_lift_factors|].
        etrans; [apply assoc_positive, Hp|].
        apply cancel_postcomposition, positive_lift_factors.
  Qed.

  Definition duploid_to_envelope_on_shifts : D ⟶ D'
    := make_functor _ duploid_to_envelope_on_shifts_is_functor.

  Lemma fully_faithful_duploid_to_envelope_on_shifts
    : fully_faithful duploid_to_envelope_on_shifts.
  Proof.
    intros a b.
    use weqhomot.
    - intermediate_weq (D⁻ₗ⟦⇑⇓a, ⇑b⟧).
      2: apply invweq; exact (make_weq _ (isweq_oblique_mor_negative θ _ _)).
      intermediate_weq (D ₗ⟦⇓a, b⟧).
      1: apply invweq, (hom_weq2 (downshift_nathomweq_linear_'_left D)).
      apply (weq_from_fully_faithful (fully_faithful_from_equivalence _ _ _ (upshift_linear_to_negative_linear_is_equivalence D))
               (⇓a) b).
    - abstract (intros f; apply oblique_mor_negative_path; now do 2 apply carrier_eq).
  Defined.

  Lemma lt_essentially_surjective_duploid_to_envelope_on_shifts
    : lt_essentially_surjective duploid_to_envelope_on_shifts.
  Proof.
    intro a; cbn in a.
    apply (has_polarity_rec (polarity_of D' a)).
    - apply isapropishinh.
    - intro Hn; apply hinhpr.
      set (a' := envelope_negative_ob θ a); cbn in a'.
      exists a'.
      refine (lt_iso_compose (b:=⇑(duploid_to_envelope_on_shifts a')) _ _). {
        apply lt_iso_inv, lt_iso_upshift_of_negative.
        apply is_negative_of_envelope_chosen_negative.
        apply envelope_on_shifts_chosen_negative_of_is_negative.
        apply a'.
      }
      refine (lt_iso_compose (b:=⇑(a : D')) _ _). {
        apply envelope_lt_iso_from_negative_iso.
        cbn.
        enough (H : lt_iso (⇑(a' : D)) a'). {
          use make_z_iso.
          - refine (_,,tt).
            exists (lt_iso_mor H).
            apply lt_iso_is_linear_and_thunkable.
          - refine (_,,tt).
            exists (lt_iso_inverse H).
            apply linear_and_thunkable_mor_is_linear_and_thunkable.
          - split; do 2 apply carrier_eq; cbn.
            + exact (is_inverse_in_precat1 (lt_iso_is_inverse H)).
            + exact (is_inverse_in_precat2 (lt_iso_is_inverse H)).
        }
        apply lt_iso_upshift_of_negative, a'.
      }
      apply lt_iso_upshift_of_negative, Hn.
    - intro Hn; apply hinhpr.
      set (a' := envelope_positive_ob θ a); cbn in a'.
      exists a'.
      refine (lt_iso_compose (b:=⇓(duploid_to_envelope_on_shifts a')) _ _). {
        apply lt_iso_downshift_of_positive.
        apply is_positive_of_envelope_chosen_positive.
        apply envelope_on_shifts_chosen_positive_of_is_positive, a'.
      }
      refine (lt_iso_compose (b:=⇓(a : D')) _ _). {
        apply envelope_lt_iso_from_positive_iso.
        cbn.
        enough (H : lt_iso (⇓(a' : D)) a'). {
          use make_z_iso.
          - refine (_,,tt).
            exists (lt_iso_mor H).
            apply lt_iso_is_linear_and_thunkable.
          - refine (_,,tt).
            exists (lt_iso_inverse H).
            apply linear_and_thunkable_mor_is_linear_and_thunkable.
          - split; do 2 apply carrier_eq; cbn.
            + exact (is_inverse_in_precat1 (lt_iso_is_inverse H)).
            + exact (is_inverse_in_precat2 (lt_iso_is_inverse H)).
        }
        apply lt_iso_inv, lt_iso_downshift_of_positive, a'.
      }
      apply lt_iso_inv, lt_iso_downshift_of_positive, Hn.
  Qed.

  Lemma is_weak_dupoid_equivalence_duploid_to_envelope_on_shifts
    : is_weak_duploid_equivalence duploid_to_envelope_on_shifts.
  Proof.
    use make_is_weak_duploid_equivalence.
    - exact fully_faithful_duploid_to_envelope_on_shifts.
    - exact lt_essentially_surjective_duploid_to_envelope_on_shifts.
  Defined.

  Theorem weak_dupoid_equivalence_duploid_to_envelope_on_shifts
    : weak_duploid_equivalence D D'.
  Proof.
    exact (make_weak_duploid_equivalence _
             is_weak_dupoid_equivalence_duploid_to_envelope_on_shifts).
  Defined.

End envelope_equiv.

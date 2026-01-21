(********************************************************************************

 The Duploid arising from an Adjunction

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition of oblique duploid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.TwoSorted.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

(** ** 1. Definition of oblique duploid *)

Section oblique_defs.

  Context {C₁ C₂ : category} (θ : adjunction C₂ C₁).
  Let F : C₂ ⟶ C₁ := left_functor θ.
  Let G : C₁ ⟶ C₂ := right_functor θ.
  Let H : are_adjoints F G := θ.
  Let η : functor_identity C₂ ⟹ F ∙ G := unit_from_are_adjoints H.
  Let ε : G ∙ F ⟹ functor_identity C₁ := counit_from_are_adjoints H.

  Definition oblique_ob := C₁ ⨿ C₂.

  Definition oblique_negativise (a : oblique_ob) : C₁.
  Proof. induction a as [n | p]. exact n. exact (F p). Defined.
  Definition oblique_positivise (a : oblique_ob) : C₂.
  Proof. induction a as [n | p]. exact (G n). exact p. Defined.

  Notation "a '⁻'" := (oblique_negativise a) : duploid.
  Notation "a '⁺'" := (oblique_positivise a) : duploid.

  Definition oblique_mor (a b : oblique_ob) := C₁⟦F (a⁺), b⁻⟧.

  Lemma isaset_oblique_mor (a b : oblique_ob) : isaset (oblique_mor a b).
  Proof. apply C₁. Qed.

  Definition oblique_identity (a : oblique_ob) : oblique_mor a a.
  Proof.
    induction a.
    + apply (φ_adj_inv H), identity.
    + apply identity.
  Defined.

  Definition oblique_compose {a b c : oblique_ob}
    (f : oblique_mor a b) (g : oblique_mor b c)
    : oblique_mor a c.
  Proof.
    induction b.
    + exact (φ_adj_inv H (φ_adj H f · φ_adj H g)).
    + exact (f · g).
  Defined.

  Lemma oblique_left_id {a b : oblique_ob} (f : oblique_mor a b) :
    oblique_compose (oblique_identity a) f = f.
  Proof.
    induction a; simpl.
    + rewrite φ_adj_after_φ_adj_inv, id_left.
      apply φ_adj_inv_after_φ_adj.
    + apply id_left.
  Qed.

  Lemma oblique_right_id {a b : oblique_ob} (f : oblique_mor a b) :
    oblique_compose f (oblique_identity b) = f.
  Proof.
    induction b; simpl.
    + rewrite φ_adj_after_φ_adj_inv, id_right.
      apply φ_adj_inv_after_φ_adj.
    + apply id_right.
  Qed.

  Definition oblique_unital_premagmoid : unital_premagmoid.
  Proof.
    use make_unital_premagmoid.
    - use make_precategory_data.
      + exact (make_precategory_ob_mor oblique_ob oblique_mor).
      + exact oblique_identity.
      + intros a b c f g. exact (oblique_compose f g).
    - abstract (use make_is_unital_premagmoid;
                [apply @oblique_left_id
                |apply @oblique_right_id]).
  Defined.

  Definition oblique_unital_magmoid : unital_magmoid.
  Proof.
    apply (make_unital_magmoid oblique_unital_premagmoid).
    intros a b; apply homset_property.
  Defined.

  Definition oblique_negative (a : C₁) : oblique_unital_magmoid := ii1 a.
  Definition oblique_positive (a : C₂) : oblique_unital_magmoid := ii2 a.

  Lemma oblique_negative_is_negative (a : C₁) : is_negative (oblique_negative a).
  Proof.
    intros b f c d g h.
    induction c as [m | q]; unfold compose; simpl.
    + do 2 rewrite φ_adj_after_φ_adj_inv.
      now rewrite assoc.
    + rewrite φ_adj_natural_postcomp, assoc.
      now rewrite φ_adj_inv_natural_postcomp.
  Qed.

  Lemma oblique_positive_is_positive (a : C₂) : is_positive (oblique_positive a).
  Proof.
    intros b f c d g h.
    induction c as [m | q]; unfold compose; simpl.
    + rewrite φ_adj_natural_postcomp, assoc.
      now rewrite φ_adj_inv_natural_postcomp.
    + apply assoc'.
  Qed.

  Lemma oblique_polarity_mapping : polarity_mapping oblique_unital_premagmoid.
  Proof.
    use make_polarity_mapping'.
    intro a; induction a as [n | p].
    - right; apply oblique_negative_is_negative.
    - left; apply oblique_positive_is_positive.
  Qed.

  Definition oblique_preduploid : preduploid :=
    make_preduploid oblique_unital_magmoid (polarity_mapping_to_has_polarities oblique_polarity_mapping).

  Definition oblique_upshift (a : oblique_preduploid) : oblique_preduploid.
  Proof.
    induction a as [n | p]; apply oblique_negative.
    - exact n.
    - exact (F p).
  Defined.

  Definition oblique_force (a : oblique_preduploid) : oblique_upshift a --> a.
  Proof.
    induction a as [n | p].
    + apply identity.
    + apply (φ_adj_inv H), identity.
  Defined.

  Definition oblique_delay (a : oblique_preduploid) : a --> oblique_upshift a.
  Proof.
    induction a as [n | p].
    + apply identity.
    + apply (identity (F p)).
  Defined.

  Definition oblique_downshift (a : oblique_preduploid) : oblique_preduploid.
  Proof.
    induction a as [n | p]; apply oblique_positive.
    + exact (G n).
    + exact p.
  Defined.

  Definition oblique_wrap (a : oblique_preduploid) : a --> oblique_downshift a.
  Proof.
    induction a as [n | p].
    + apply (identity (F (G n))).
    + apply identity.
  Defined.

  Definition oblique_unwrap (a : oblique_preduploid) : oblique_downshift a --> a.
  Proof.
    induction a as [n | p].
    + apply (φ_adj_inv H), identity.
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
    unfold compose; simpl.
    rewrite φ_adj_after_φ_adj_inv.
    now do 2 rewrite id_right, φ_adj_inv_after_φ_adj.
  Qed.

  Definition is_thunkable_oblique_wrap (a : oblique_preduploid)
    : is_thunkable (oblique_wrap a).
  Proof.
    induction a as [n | p].
    2: apply is_thunkable_identity.
    intros b c f g.
    induction b as [m | q].
    2: now rewrite (assoc'_positive _ (oblique_positive_is_positive _)).
    unfold compose; simpl.
    now do 2 rewrite id_left.
  Qed.

  Lemma is_linear_oblique_delay (a : oblique_preduploid)
    : is_linear (oblique_delay a).
  Proof.
    induction a as [n | p].
    2: apply is_linear_of_positive, oblique_positive_is_positive.
    intros b c f g.
    induction b as [m | q].
    1: apply assoc'_negative, oblique_negative_is_negative.
    cbn.
    rewrite φ_adj_natural_postcomp.
    rewrite φ_adj_after_φ_adj_inv.
    do 2 rewrite id_right.
    rewrite φ_adj_inv_natural_postcomp.
    now do 2 rewrite φ_adj_inv_after_φ_adj.
  Qed.

  Lemma is_thunkable_oblique_unwrap (a : oblique_preduploid)
    : is_thunkable (oblique_unwrap a).
  Proof.
    induction a as [n | p].
    1: apply is_thunkable_of_negative, oblique_negative_is_negative.
    intros b c f g.
    induction b as [m | q].
    2: apply assoc_positive, oblique_positive_is_positive.
    cbn.
    now do 2 rewrite id_left.
  Qed.

  Definition is_inverse_in_precat_oblique_force_delay (a : oblique_preduploid)
    : is_inverse_in_precat (oblique_force a) (oblique_delay a).
  Proof.
    induction a as [n | p]; simpl; split; unfold identity, compose; simpl;
      fold (identity (C:=C₂)); fold (identity (C:=C₁)).
    - now rewrite φ_adj_after_φ_adj_inv, id_left.
    - now rewrite φ_adj_after_φ_adj_inv, id_left.
    - now rewrite id_right.
    - now rewrite φ_adj_after_φ_adj_inv, id_right, φ_adj_inv_after_φ_adj.
  Qed.

  Definition is_inverse_in_precat_oblique_wrap_unwrap (a : oblique_preduploid)
    : is_inverse_in_precat (oblique_wrap a) (oblique_unwrap a).
  Proof.
    induction a as [n | p]; simpl; split; unfold identity, compose; simpl;
      fold (identity (C:=C₂)); fold (identity (C:=C₁)).
    - now rewrite id_left.
    - now rewrite φ_adj_after_φ_adj_inv, id_left, φ_adj_inv_after_φ_adj.
    - apply id_left.
    - apply id_left.
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
    - apply is_inverse_in_precat_oblique_wrap_unwrap.
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

  (* The oblique duploid is the duploid arising from an adjunction,
   where objects are objects in either category, and morphisms
   are the morphisms C₁⟦F a⁺, b⁻⟧ (equivalently C₂⟦a⁻, G b⁺⟧). *)
  Definition oblique_duploid : duploid
    := make_duploid _ oblique_has_polarity_shifts.

  Definition oblique_split_duploid : split_duploid
    := make_split_duploid oblique_duploid oblique_polarity_mapping.

  Lemma is_linear_of_oblique_counit_precompose {n : C₁} {a : oblique_duploid}
    (f : oblique_negative n --> a)
    : #(G ∙ F) (ε n) · f = ε ((G ∙ F) n) · f ->
      is_linear f.
  Proof.
    intro Hf.
    apply (is_linear_of_force_unwrap (C:=oblique_duploid)).
    cbn.
    rewrite φ_adj_natural_postcomp, φ_adj_inv_natural_precomp.
    do 2 rewrite φ_adj_after_φ_adj_inv, id_left, φ_adj_inv_after_φ_adj.
    unfold φ_adj_inv; fold ε.
    do 2 rewrite functor_id, id_left.
    exact Hf.
  Qed.

  Lemma is_thunkable_of_oblique_unit_postcompose {a : oblique_duploid} {p : C₂}
    (f : a --> oblique_positive p)
    : φ_adj H f · #(F ∙ G) (η p) = φ_adj H f · η ((F ∙ G) p) ->
      is_thunkable f.
  Proof.
    intro Hf.
    apply (is_thunkable_of_delay_wrap (C:=oblique_duploid)).
    eenough (H' : φ_adj_inv H (φ_adj H _) = φ_adj_inv H (φ_adj H _)). {
      do 2 rewrite φ_adj_inv_after_φ_adj in H'.
      exact H'.
    }
    apply maponpaths.
    cbn.
    do 2 rewrite φ_adj_natural_postcomp, φ_adj_inv_natural_precomp.
    rewrite φ_adj_inv_after_φ_adj, functor_id.
    do 2 rewrite id_right.
    rewrite functor_comp, functor_id, φ_adj_natural_precomp.
    do 2 rewrite φ_adj_identity. fold η.
    exact Hf.
  Qed.

  Corollary is_precategory_of_oblique_idempotent_adjunction
    (H1 : post_whisker ε (G ∙ F) = pre_whisker (G ∙ F) ε)
    : is_assoc_premagmoid oblique_duploid.
  Proof.
    use make_is_one_assoc_premagmoid.
    intros a b c d f g h.
    apply assoc_linear.
    induction c as [n | p].
    2: apply is_linear_of_positive, oblique_positive_is_positive.
    apply is_linear_of_oblique_counit_precompose.
    intermediate_path (post_whisker ε (G ∙ F) n · h).
    apply idpath.
    now rewrite H1.
  Qed.

End oblique_defs.

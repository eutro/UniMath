(********************************************************************************

 The Single-Sorted Duploid arising from an Adjunction

 Author: B. Szilvasy
 January 2026

 This file defines the envelope duploid and some proofs about it.  The main
 result is its univalence [is_univalent_envelope_duploid] when arising from a
 fully equalizing adjunction between univalent categories.

 The "structure theorem" about the envelope duploid -- that all duploids are
 equivalent to an envelope duploid -- can be found in [StructureTheorem.v].

 Contents:
 1. Definition of the envelope duploid
 2. Weak equivalence with the oblique duploid
 3. Lemmas about the envelope duploid
 4. Univalence of the envelope duploid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.RXGraph.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Oblique.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.ShiftFunctors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.ShiftFacts.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.EqualizingRequirement.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.
Local Open Scope oblique_mor.

Section envelope_defs.
  (** ** 1. Definition of the envelope duploid *)

  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.

  (** A pre-object of the envelope. *)
  Definition envelope_preob := ∑ (pn : P × N), oblique_mor θ (pr1 pn) (pr2 pn).
  Definition make_envelope_preob
    (p : P) (n : N) (cross : oblique_mor θ p n)
    : envelope_preob := (p,,n),,cross.

  Definition envelope_negative_ob (a : envelope_preob) : N := pr21 a.
  Definition envelope_positive_ob (a : envelope_preob) : P := pr11 a.

  Local Notation "a '⁻'" := (envelope_negative_ob a) (at level 1) : duploid.
  Local Notation "a '⁺'" := (envelope_positive_ob a) (at level 1) : duploid.

  Definition envelope_mor (a b : envelope_preob) : UU := oblique_mor θ a⁺ b⁻.
  Definition envelope_cross_mor (a : envelope_preob) : envelope_mor a a := pr2 a.
  Local Notation "a '►'" := (envelope_cross_mor a) : duploid.
  (* type in Emacs with agda-input using \t *)

  Arguments envelope_mor / _ _.

  Definition envelope_chosen_negative (a : envelope_preob) : UU := oblique_is_positive_iso _ a►.
  Identity Coercion Id_envelope_chosen_negative : envelope_chosen_negative >-> oblique_is_positive_iso.
  Definition envelope_chosen_positive (a : envelope_preob) : UU := oblique_is_negative_iso _ a►.
  Identity Coercion Id_envelope_chosen_positive : envelope_chosen_positive >-> oblique_is_negative_iso.
  Definition envelope_polarization_choice (a : envelope_preob) : UU
    := envelope_chosen_negative a ⨿ envelope_chosen_positive a.

  Arguments envelope_chosen_negative / _.
  Arguments envelope_chosen_positive / _.

  Lemma isaprop_envelope_chosen_negative (a : envelope_preob)
    : isaprop (envelope_chosen_negative a).
  Proof. apply isaprop_oblique_is_positive_iso. Qed.
  Lemma isaprop_envelope_chosen_positive (a : envelope_preob)
    : isaprop (envelope_chosen_positive a).
  Proof. apply isaprop_oblique_is_negative_iso. Qed.

  Definition envelope_mor_factor_chosen_negative {a b : envelope_preob}
    (f : envelope_mor a b) (negative : envelope_chosen_negative b)
    : a⁺ --> b⁺ := f♯ · is_z_isomorphism_mor negative.
  Definition envelope_mor_factor_chosen_positive {a b : envelope_preob}
    (f : envelope_mor a b) (positive : envelope_chosen_positive a)
    : a⁻ --> b⁻ := is_z_isomorphism_mor positive · f♭.

  Local Notation "f '#⊖'" := (envelope_mor_factor_chosen_negative f).
  Local Notation "f '#⊕'" := (envelope_mor_factor_chosen_positive f).

  Arguments envelope_mor_factor_chosen_negative {_ _} / _.
  Arguments envelope_mor_factor_chosen_positive {_ _} / _.

  Lemma envelope_mor_factor_chosen_negative_eq {a b : envelope_preob}
    (f : envelope_mor a b) (negative : envelope_chosen_negative b)
    : f#⊖negative · b►♯ = f♯.
  Proof.
    refine (assoc' _ _ _ @ _ @ id_right _).
    apply cancel_precomposition, (is_inverse_in_precat2 negative).
  Qed.

  Lemma envelope_mor_factor_chosen_positive_eq {a b : envelope_preob}
    (f : envelope_mor a b) (positive : envelope_chosen_positive a)
    : a►♭ · f#⊕positive = f♭.
  Proof.
    refine (assoc _ _ _ @ _ @ id_left _).
    apply cancel_postcomposition, (is_inverse_in_precat1 positive).
  Qed.

  (** To compose two morphisms, we need a choice of polarization for the middle object. *)
  Definition envelope_compose' {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (choice : envelope_polarization_choice b)
    : envelope_mor a c.
  Proof.
    unfold envelope_mor in *.
    induction choice as [Hn | Hp].
    - exact (oblique_compose_positive θ (f#⊖Hn) g).
    - exact (oblique_compose_negative θ f (g#⊕Hp)).
  Defined.

  Local Lemma isInjective_φ_adj {a b} : isInjective (φ_adj (A:=a) (B:=b) θ).
  Proof. apply isweqonpathsincl, isinclweq, adjunction_hom_weq. Qed.
  Local Lemma isInjective_φ_adj_inv {a b} : isInjective (φ_adj_inv (A:=a) (B:=b) θ).
  Proof. apply isweqonpathsincl, isinclweq, (invweq (adjunction_hom_weq _ _ _)). Qed.

  Ltac cancel_φ_adj := apply (Injectivity (φ_adj θ) isInjective_φ_adj).
  Ltac cancel_φ_adj_inv := apply (Injectivity (φ_adj_inv θ) isInjective_φ_adj_inv).

  Definition envelope_compose_id_left {a b : envelope_preob}
    (f : envelope_mor a b)
    (choice : envelope_polarization_choice a)
    : envelope_compose' (a►) f choice = f.
  Proof.
    induction choice as [Hn | Hp]; cbn.
    - apply oblique_mor_positive_path; cbn.
      etrans; [apply cancel_postcomposition, (is_inverse_in_precat1 Hn)|].
      apply id_left.
    - apply oblique_mor_negative_path; cbn.
      apply envelope_mor_factor_chosen_positive_eq.
  Qed.

  Definition envelope_compose_id_right {a b : envelope_preob}
    (f : envelope_mor a b)
    (choice : envelope_polarization_choice b)
    : envelope_compose' f (b►) choice = f.
  Proof.
    induction choice as [Hn | Hp]; cbn.
    - apply oblique_mor_positive_path; cbn.
      apply envelope_mor_factor_chosen_negative_eq.
    - apply oblique_mor_negative_path; cbn.
      etrans; [apply cancel_precomposition, (is_inverse_in_precat2 Hp)|].
      apply id_right.
  Qed.

  (** However, if both choices exist, then it does not matter which we choose. *)
  Lemma envelope_chosen_negative_and_positive_eq (a : envelope_preob)
    (negative : envelope_chosen_negative a)
    (positive : envelope_chosen_positive a)
    : # R (is_z_isomorphism_mor positive) = φ_adj θ (# L (is_z_isomorphism_mor negative)).
  Proof.
    apply (pre_comp_with_z_iso_is_inj' negative).
    cancel_φ_adj_inv.
    intermediate_path (identity (L a ⁺)).
    - rewrite φ_adj_inv_natural_postcomp.
      etrans; [apply cancel_postcomposition, oblique_mor_positive_transpose|].
      apply (is_inverse_in_precat1 positive).
    - rewrite <- φ_adj_natural_precomp, <- functor_comp, φ_adj_inv_after_φ_adj.
      rewrite <- functor_id; apply maponpaths, pathsinv0.
      apply (is_inverse_in_precat1 negative).
  Qed.

  Theorem envelope_compose_irrel {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (negative : envelope_chosen_negative b)
    (positive : envelope_chosen_positive b)
    : envelope_compose' f g (ii2 positive) = envelope_compose' f g (ii1 negative).
  Proof.
    apply oblique_mor_negative_path; cbn.
    rewrite assoc.
    apply cancel_postcomposition.
    cancel_φ_adj.
    rewrite functor_comp, φ_adj_natural_precomp, φ_adj_natural_postcomp.
    rewrite oblique_mor_negative_transpose.
    apply cancel_precomposition.
    apply envelope_chosen_negative_and_positive_eq.
  Qed.

  Corollary envelope_compose_irrel' {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (choice1 choice2 : envelope_polarization_choice b)
    : envelope_compose' f g choice1 = envelope_compose' f g choice2.
  Proof.
    induction choice1, choice2.
    1, 4: apply maponpaths, maponpaths, proofirrelevance, isaprop_is_z_isomorphism.
    - apply pathsinv0, envelope_compose_irrel.
    - apply envelope_compose_irrel.
  Qed.

  (** This justifies truncating the polarization choice to a property *)
  Definition envelope_polarization (a : envelope_preob) : hProp
    := ∥envelope_polarization_choice a∥.

  Lemma isaprop_envelope_polarization (a : envelope_preob) : isaprop (envelope_polarization a).
  Proof. apply propproperty. Qed.

  Definition envelope_compose {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (polarization : envelope_polarization b)
    : envelope_mor a c.
  Proof.
    refine (squash_to_set _ (envelope_compose' f g) _ polarization).
    - abstract (apply isaset_oblique_mor).
    - apply envelope_compose_irrel'.
  Defined.

  Lemma envelope_polarization_rec {a : envelope_preob}
    (T : envelope_polarization a -> hProp)
    (Hnegative : ∏ (negative : envelope_chosen_negative a), T (hinhpr (ii1 negative)))
    (Hpositive : ∏ (positive : envelope_chosen_positive a), T (hinhpr (ii2 positive)))
    : ∏ (polarization : envelope_polarization a), T polarization.
  Proof.
    intro polarization; apply squash_rec; intro H.
    induction H as [Hn | Hp].
    - apply Hnegative.
    - apply Hpositive.
  Defined.

  Lemma envelope_polarization_rec' {a : envelope_preob}
    (T : envelope_polarization a -> UU)
    (Hprop : isPredicate T)
    (Hnegative : ∏ (negative : envelope_chosen_negative a), T (hinhpr (ii1 negative)))
    (Hpositive : ∏ (positive : envelope_chosen_positive a), T (hinhpr (ii2 positive)))
    : ∏ (polarization : envelope_polarization a), T polarization.
  Proof.
    apply (envelope_polarization_rec (λ H, make_hProp (T H) (Hprop H))); assumption.
  Defined.

  Lemma envelope_compose_rec {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (T : envelope_mor a c -> hProp)
    (Hnegative : ∏ negative, T (envelope_compose' f g (ii1 negative)))
    (Hpositive : ∏ positive, T (envelope_compose' f g (ii2 positive)))
    : ∏ (polarization : envelope_polarization b), T (envelope_compose f g polarization).
  Proof.
    intro polarization.
    apply (envelope_polarization_rec (λ H, T (envelope_compose f g H))).
    - apply Hnegative.
    - apply Hpositive.
  Defined.

  Lemma envelope_compose_rec' {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (T : envelope_mor a c -> UU)
    (Hprop : isPredicate T)
    (Hnegative : ∏ negative, T (envelope_compose' f g (ii1 negative)))
    (Hpositive : ∏ positive, T (envelope_compose' f g (ii2 positive)))
    : ∏ (polarization : envelope_polarization b), T (envelope_compose f g polarization).
  Proof.
    apply (envelope_compose_rec _ _ (λ H, make_hProp (T H) (Hprop H))); assumption.
  Defined.

  Lemma envelope_compose_known {a b c : envelope_preob}
    (Hchoice : envelope_polarization_choice b)
    (Hpolarization : envelope_polarization b)
    (f : envelope_mor a b) (g : envelope_mor b c)
    : envelope_compose f g Hpolarization = envelope_compose' f g Hchoice.
  Proof.
    apply envelope_compose_rec'.
    1: intro; apply isaset_oblique_mor.
    all: intro; apply envelope_compose_irrel'.
  Qed.

  Definition envelope_ob := ∑ (a : envelope_preob), envelope_polarization a.
  Definition make_envelope_ob (a : envelope_preob)
    (H : envelope_polarization a) : envelope_ob
    := a,,H.

  Coercion envelope_ob_to_envelope_preob (a : envelope_ob) : envelope_preob := pr1 a.
  Coercion envelope_ob_to_envelope_polarization (a : envelope_ob) : envelope_polarization a := pr2 a.

  Definition envelope_preob_of_positive (p : P) : envelope_preob.
  Proof.
    use make_envelope_preob.
    - exact p.
    - exact (L p).
    - exact (oblique_positive_identity θ p).
  Defined.

  Definition envelope_preob_of_negative (n : N) : envelope_preob.
  Proof.
    use make_envelope_preob.
    - exact (R n).
    - exact n.
    - exact (oblique_negative_identity θ n).
  Defined.

  Lemma envelope_chosen_positive_of_positive (p : P)
    : envelope_chosen_positive (envelope_preob_of_positive p).
  Proof. apply oblique_positive_identity_is_negative_iso. Defined.

  Lemma envelope_chosen_negative_of_negative (n : N)
    : envelope_chosen_negative (envelope_preob_of_negative n).
  Proof. apply oblique_negative_identity_is_positive_iso. Defined.

  Definition envelope_ob_of_positive (p : P) : envelope_ob.
  Proof.
    use (make_envelope_ob (envelope_preob_of_positive p)).
    apply hinhpr; constructor; apply envelope_chosen_positive_of_positive.
  Defined.

  Definition envelope_ob_of_negative (n : N) : envelope_ob.
  Proof.
    use (make_envelope_ob (envelope_preob_of_negative n)).
    apply hinhpr; constructor; apply envelope_chosen_negative_of_negative.
  Defined.

  Definition envelope_ob_mor : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact envelope_ob.
    - intros a b; exact (envelope_mor a b).
  Defined.

  Definition envelope_unital_premagmoid_data : unital_premagmoid_data.
  Proof.
    use (make_precategory_data envelope_ob_mor).
    - cbn; intro a; exact (a►).
    - cbn; intros a b c f g; exact (envelope_compose f g b).
  Defined.

  Definition envelope_is_unital_premagmoid : is_unital_premagmoid envelope_unital_premagmoid_data.
  Proof.
    split; intros a b f; cbn;
      (apply envelope_compose_rec'; [intro; apply isaset_oblique_mor | |]).
    1, 2: intro; apply envelope_compose_id_left.
    1, 2: intro; apply envelope_compose_id_right.
  Qed.

  Definition envelope_unital_premagmoid : unital_premagmoid
    := make_unital_premagmoid _ envelope_is_unital_premagmoid.

  Definition envelope_unital_magmoid : unital_magmoid.
  Proof.
    use (make_unital_magmoid envelope_unital_premagmoid).
    abstract (intros a b; apply isaset_oblique_mor).
  Defined.

  Ltac envelope_induction' a
    := let a' := uconstr:(a : envelope_ob) in
       generalize (a' : envelope_polarization a');
       apply (envelope_polarization_rec' (a:=a')).

  Lemma is_positive_of_envelope_chosen_positive (a : envelope_unital_magmoid)
    (H : envelope_chosen_positive (a : envelope_ob)) : is_positive a.
  Proof.
    intros b f c d g h; cbn in c, f, g, h |- *.
    rewrite !(envelope_compose_known (ii2 H)).
    envelope_induction' c.
    - intro; apply isaset_oblique_mor.
    - intro Hn; cbn.
      apply oblique_mor_positive_path; cbn.
      now rewrite !assoc.
    - intro Hp.
      apply oblique_mor_negative_path; cbn.
      now rewrite !assoc.
  Qed.

  Corollary is_positive_envelope_ob_of_positive (p : P)
    : is_positive (M:=envelope_unital_magmoid) (envelope_ob_of_positive p).
  Proof.
    apply is_positive_of_envelope_chosen_positive, envelope_chosen_positive_of_positive.
  Qed.

  Lemma is_negative_of_envelope_chosen_negative (a : envelope_unital_magmoid)
    (H : envelope_chosen_negative (a : envelope_ob)) : is_negative a.
  Proof.
    intros b f c d g h; cbn in c, f, g, h |- *.
    rewrite !(envelope_compose_known (ii1 H)).
    envelope_induction' c.
    - intro; apply isaset_oblique_mor.
    - intro Hn; cbn.
      apply oblique_mor_positive_path; cbn.
      now rewrite !assoc.
    - intro Hp.
      apply oblique_mor_negative_path; cbn.
      now rewrite !assoc.
  Qed.

  Corollary is_negative_envelope_ob_of_negative (n : N)
    : is_negative (M:=envelope_unital_magmoid) (envelope_ob_of_negative n).
  Proof.
    apply is_negative_of_envelope_chosen_negative, envelope_chosen_negative_of_negative.
  Qed.

  Lemma envelope_has_polarities : has_polarities envelope_unital_magmoid.
  Proof.
    intro a; cbn in a.
    envelope_induction' a.
    - intro; apply isaprop_has_polarity.
    - intro H.
      apply make_has_polarity_negative, is_negative_of_envelope_chosen_negative, H.
    - intro H.
      apply make_has_polarity_positive, is_positive_of_envelope_chosen_positive, H.
  Qed.

  Definition envelope_preduploid : preduploid :=
    make_preduploid envelope_unital_magmoid envelope_has_polarities.

  Definition envelope_downshift (a : envelope_preob) : envelope_ob
    := envelope_ob_of_positive (a⁺).
  Definition envelope_upshift (a : envelope_preob)
    : envelope_ob := envelope_ob_of_negative (a⁻).

  Definition envelope_force
    (a : envelope_preob) : envelope_mor (envelope_upshift a) a.
  Proof. exact (oblique_negative_identity θ (a⁻)). Defined.
  Definition envelope_delay
    (a : envelope_preob) : envelope_mor a (envelope_upshift a).
  Proof. exact (a►). Defined.

  Definition envelope_wrap
    (a : envelope_preob) : envelope_mor a (envelope_downshift a).
  Proof. exact (oblique_positive_identity θ (a⁺)). Defined.
  Definition envelope_unwrap
    (a : envelope_preob) : envelope_mor (envelope_downshift a) a.
  Proof. exact (a►). Defined.

  Lemma is_linear_envelope_force (a : envelope_ob)
    : is_linear (M:=envelope_preduploid) (envelope_force a).
  Proof.
    intros b c g h; cbn in b.
    envelope_induction' b.
    1: intro; apply unital_magmoid_has_homsets.
    1: intro H; apply assoc'_negative, is_negative_of_envelope_chosen_negative, H.
    intro Hp; cbn.
    rewrite !(envelope_compose_known (ii2 Hp)); cbn.
    apply oblique_mor_positive_path; cbn.
    rewrite <- (φ_adj_inv_identity θ), <- φ_adj_inv_natural_precomp, !id_right.
    now rewrite oblique_mor_positive_transpose.
  Qed.

  Lemma is_linear_envelope_delay (a : envelope_ob)
    : is_linear (M:=envelope_preduploid) (envelope_delay a).
  Proof.
    cbn in a; envelope_induction' a.
    1: intro; apply isaprop_is_linear.
    2: intro H; apply is_linear_of_positive, is_positive_of_envelope_chosen_positive, H.
    intros Hn b c g h.
    cbn in b; envelope_induction' b.
    1: intro; apply unital_magmoid_has_homsets.
    1: intro H; apply assoc'_negative, is_negative_of_envelope_chosen_negative, H.
    intro Hp; cbn.
    rewrite !(envelope_compose_known (ii2 Hp)),
      !(envelope_compose_known (ii1 Hn)); cbn.
    unfold envelope_delay; cbn.
    apply oblique_mor_positive_path; cbn.
    rewrite <- (oblique_mor_positive_transpose θ (a►)), <- φ_adj_inv_natural_precomp.
    now rewrite !assoc', !(is_inverse_in_precat2 Hn), !id_right,
      oblique_mor_positive_transpose.
  Qed.

  Lemma is_inverse_in_precat_envelope_force_delay (a : envelope_ob)
    : is_inverse_in_precat (C:=envelope_preduploid) (envelope_force a) (envelope_delay a).
  Proof.
    split; cbn.
    - envelope_induction' a.
      1: intro; apply isaset_oblique_mor.
      + intro Hn; cbn.
        unfold envelope_delay, envelope_force; cbn.
        apply oblique_mor_positive_path; cbn.
        rewrite id_left.
        apply (is_inverse_in_precat2 Hn).
      + intro Hp; cbn.
        unfold envelope_delay; cbn.
        apply oblique_mor_positive_path; cbn.
        now rewrite (is_inverse_in_precat2 Hp), functor_id, id_right.
    - unfold envelope_delay, envelope_force; cbn.
      apply oblique_mor_positive_path; cbn.
      now rewrite !id_right.
  Qed.

  Definition has_linear_inverse_envelope_force (a : envelope_ob)
    : has_linear_inverse (M:=envelope_preduploid) (envelope_force a).
  Proof.
    use make_has_linear_inverse.
    - exact (make_linear_mor _ (is_linear_envelope_delay a)).
    - apply is_inverse_in_precat_envelope_force_delay.
  Defined.

  Definition envelope_negative_shift_data : negative_shift_data envelope_preduploid.
  Proof.
    use make_negative_shift_data.
    - intro a; exact (envelope_upshift (a : envelope_ob)).
    - intro a; apply (envelope_force (a : envelope_ob)).
  Defined.

  Definition envelope_negative_shift_axioms : negative_shift_axioms envelope_negative_shift_data.
  Proof.
    use make_negative_shift_axioms.
    - apply is_linear_envelope_force.
    - intro a; apply is_negative_envelope_ob_of_negative.
    - intro a; apply has_linear_inverse_envelope_force.
  Defined.

  Definition envelope_has_negative_shifts : has_negative_shifts envelope_preduploid
    := make_has_negative_shifts _ envelope_negative_shift_axioms.

  Lemma is_thunkable_envelope_wrap (a : envelope_ob)
    : is_thunkable (M:=envelope_preduploid) (envelope_wrap a).
  Proof.
    intros b c g h; cbn in b.
    envelope_induction' b.
    1: intro; apply unital_magmoid_has_homsets.
    2: intro H; apply assoc_positive, is_positive_of_envelope_chosen_positive, H.
    intro Hn; cbn.
    rewrite !(envelope_compose_known (ii1 Hn)); cbn.
    unfold envelope_wrap; cbn.
    apply oblique_mor_negative_path; cbn.
    rewrite <- (φ_adj_identity θ), <- φ_adj_natural_postcomp, !id_left.
    now rewrite oblique_mor_negative_transpose.
  Qed.

  Lemma is_thunkable_envelope_unwrap (a : envelope_ob)
    : is_thunkable (M:=envelope_preduploid) (envelope_unwrap a).
  Proof.
    cbn in a; envelope_induction' a.
    1: intro; apply isaprop_is_thunkable.
    1: intro H; apply is_thunkable_of_negative, is_negative_of_envelope_chosen_negative, H.
    intros Hp b c g h.
    cbn in b; envelope_induction' b.
    1: intro; apply unital_magmoid_has_homsets.
    2: intro H; apply assoc_positive, is_positive_of_envelope_chosen_positive, H.
    intro Hn; cbn.
    rewrite !(envelope_compose_known (ii1 Hn)),
      !(envelope_compose_known (ii2 Hp)); cbn.
    unfold envelope_unwrap; cbn.
    apply oblique_mor_negative_path; cbn.
    rewrite <- (oblique_mor_negative_transpose θ (a►)), <- φ_adj_natural_postcomp.
    now rewrite !assoc, !(is_inverse_in_precat1 Hp), !id_left,
      oblique_mor_negative_transpose.
  Qed.

  Lemma is_inverse_in_precat_envelope_unwrap_wrap (a : envelope_ob)
    : is_inverse_in_precat (C:=envelope_preduploid) (envelope_unwrap a) (envelope_wrap a).
  Proof.
    split; cbn.
    - envelope_induction' a.
      1: intro; apply isaset_oblique_mor.
      + intro Hn; cbn.
        unfold envelope_unwrap, envelope_wrap; cbn.
        apply oblique_mor_negative_path; cbn.
        now rewrite (is_inverse_in_precat1 Hn), functor_id, id_left.
      + intro Hp; cbn.
        unfold envelope_unwrap, envelope_wrap; cbn.
        apply oblique_mor_negative_path; cbn.
        rewrite id_right.
        apply (is_inverse_in_precat1 Hp).
    - unfold envelope_wrap, envelope_unwrap; cbn.
      apply oblique_mor_negative_path; cbn.
      now rewrite !id_left.
  Qed.

  Definition has_thunkable_inverse_envelope_wrap (a : envelope_ob)
    : has_thunkable_inverse (M:=envelope_preduploid) (envelope_wrap a).
  Proof.
    use make_has_thunkable_inverse.
    - exact (make_thunkable_mor _ (is_thunkable_envelope_unwrap a)).
    - apply is_inverse_in_precat_envelope_unwrap_wrap.
  Defined.

  Definition envelope_positive_shift_data : positive_shift_data envelope_preduploid.
  Proof.
    use make_positive_shift_data.
    - intro a; exact (envelope_downshift (a : envelope_ob)).
    - intro a; apply (envelope_wrap (a : envelope_ob)).
  Defined.

  Definition envelope_positive_shift_axioms : positive_shift_axioms envelope_positive_shift_data.
  Proof.
    use make_positive_shift_axioms.
    - apply is_thunkable_envelope_wrap.
    - intro a; apply is_positive_envelope_ob_of_positive.
    - intro a; apply has_thunkable_inverse_envelope_wrap.
  Defined.

  Definition envelope_has_positive_shifts : has_positive_shifts envelope_preduploid
    := make_has_positive_shifts _ envelope_positive_shift_axioms.

  Definition envelope_has_polarity_shifts : has_polarity_shifts envelope_preduploid.
  Proof.
    use make_has_polarity_shifts.
    - apply envelope_has_negative_shifts.
    - apply envelope_has_positive_shifts.
  Defined.

  Definition envelope_duploid : duploid
    := make_duploid _ envelope_has_polarity_shifts.

  (** ** 2. Weak equivalence with the oblique duploid *)

  Definition oblique_to_envelope_ob (a : oblique_duploid θ) : envelope_preduploid.
  Proof.
    induction a as [n | p].
    - apply envelope_ob_of_negative, n.
    - apply envelope_ob_of_positive, p.
  Defined.

  Definition oblique_to_envelope_mor {a b : oblique_duploid θ} (f : a --> b)
    : oblique_to_envelope_ob a --> oblique_to_envelope_ob b.
  Proof.
    induction a, b; exact f.
  Defined.

  Definition oblique_to_envelope_data : functor_data (oblique_duploid θ) envelope_duploid.
  Proof.
    use make_functor_data.
    - exact oblique_to_envelope_ob.
    - exact @oblique_to_envelope_mor.
  Defined.

  Definition is_functor_oblique_to_envelope : is_functor oblique_to_envelope_data.
  Proof.
    use make_is_functor.
    - intro a; induction a;
        [ apply oblique_mor_positive_path
        | apply oblique_mor_negative_path ]; easy.
    - intros a b c g f.
      induction a as [n | p], b as [m | q], c as [o | r]; cbn;
        first [rewrite id_right | rewrite id_left];
        easy.
  Qed.

  Definition oblique_to_envelope : functor (oblique_duploid θ) envelope_duploid
    := make_functor _ is_functor_oblique_to_envelope.

  Lemma fully_faithful_oblique_to_envelope : fully_faithful oblique_to_envelope.
  Proof.
    intros a b; induction a, b; apply idisweq.
  Defined.

  (* This is a nice sanity check; it is not load-bearing. *)
  Lemma oblique_to_envelope_preserves_downshift (a : oblique_duploid θ)
    : (⇓oblique_to_envelope a : ob _) = oblique_to_envelope (⇓a).
  Proof. now induction a as [n | p]. Defined.
  Lemma oblique_to_envelope_preserves_upshift (a : oblique_duploid θ)
    : (⇑oblique_to_envelope a : ob _) = oblique_to_envelope (⇑a).
  Proof. now induction a as [n | p]. Defined.

  Lemma oblique_to_envelope_inverse_of_chosen_negative
    (b : envelope_duploid) (Hn : envelope_chosen_negative (b : envelope_ob))
    : ∑ (a : oblique_duploid θ), lt_iso (oblique_to_envelope a) b.
  Proof.
    exists (oblique_negative θ ((b : envelope_ob) ⁻)).
    apply (lt_iso_upshift_of_negative b).
    abstract (apply is_negative_of_envelope_chosen_negative, Hn).
  Defined.

  Lemma oblique_to_envelope_inverse_of_chosen_positive
    (b : envelope_duploid) (Hn : envelope_chosen_positive (b : envelope_ob))
    : ∑ (a : oblique_duploid θ), lt_iso (oblique_to_envelope a) b.
  Proof.
    exists (oblique_positive θ ((b : envelope_ob) ⁺)).
    apply lt_iso_inv, (lt_iso_downshift_of_positive b).
    abstract (apply is_positive_of_envelope_chosen_positive, Hn).
  Defined.

  Lemma lt_essentially_surjective_oblique_to_envelope : lt_essentially_surjective oblique_to_envelope.
  Proof.
    intro a; envelope_induction' a.
    1: intro; apply isapropishinh.
    - intro Hn; apply hinhpr, oblique_to_envelope_inverse_of_chosen_negative, Hn.
    - intro Hp; apply hinhpr, oblique_to_envelope_inverse_of_chosen_positive, Hp.
  Qed.

  Lemma split_lt_essentially_surjective_oblique_to_envelope_from_LEM
    : LEM -> split_lt_essentially_surjective oblique_to_envelope.
  Proof.
    intros lem a.
    set (Hlemn := lem (make_hProp (envelope_chosen_negative (a : envelope_ob)) (isaprop_is_z_isomorphism _))).
    induction Hlemn as [Hn | Hnotn].
    - apply oblique_to_envelope_inverse_of_chosen_negative, Hn.
    - assert (Hp : envelope_chosen_positive (a : envelope_ob)). {
        envelope_induction' a; intro.
        apply isaprop_is_z_isomorphism.
        all: easy.
      }
      apply oblique_to_envelope_inverse_of_chosen_positive, Hp.
  Qed.

  Lemma preserves_linearity_and_thunkability_oblique_to_envelope
    : preserves_linearity_and_thunkability oblique_to_envelope.
  Proof.
    apply full_and_lt_essentially_surjective_preserves_linearity_and_thunkability.
    - apply fully_faithful_implies_full_and_faithful, fully_faithful_oblique_to_envelope.
    - apply lt_essentially_surjective_oblique_to_envelope.
  Qed.

  Definition oblique_to_envelope_duploid : oblique_duploid θ ⟶d envelope_duploid
    := make_duploid_functor _ preserves_linearity_and_thunkability_oblique_to_envelope.

  Definition weak_equiv_oblique_to_envelope_duploid
    : weak_duploid_equivalence (oblique_duploid θ) envelope_duploid.
  Proof.
    use (make_weak_duploid_equivalence oblique_to_envelope_duploid).
    use make_is_weak_duploid_equivalence.
    - exact fully_faithful_oblique_to_envelope.
    - exact lt_essentially_surjective_oblique_to_envelope.
  Defined.

  Definition equiv_oblique_to_envelope_duploid_from_LEM
    : LEM -> duploid_equivalence (oblique_duploid θ) envelope_duploid.
  Proof.
    intro lem.
    use (make_duploid_equivalence oblique_to_envelope_duploid).
    use make_is_duploid_equivalence.
    - exact fully_faithful_oblique_to_envelope.
    - exact (split_lt_essentially_surjective_oblique_to_envelope_from_LEM lem).
  Defined.

  (** ** 3. Lemmas about the envelope duploid *)
  Lemma envelope_positive_lift {a b : envelope_ob}
    (f : envelope_duploid⟦a, b⟧)
    : (positive_lift f : envelope_duploid⟦_, _⟧) = f.
  Proof.
    envelope_induction' a.
    - intro; apply isaset_oblique_mor.
    - intro Hn.
      etrans; [apply (envelope_compose_known (ii1 Hn) _ (envelope_unwrap a) f)|].
      apply oblique_mor_positive_path; cbn.
      etrans; [apply cancel_postcomposition, (is_inverse_in_precat1 Hn)|].
      apply id_left.
    - intro Hp.
      etrans; [apply (envelope_compose_known (ii2 Hp) _ (envelope_unwrap a) f)|].
      apply oblique_mor_negative_path; cbn.
      etrans; [apply assoc|].
      etrans; [apply cancel_postcomposition, (is_inverse_in_precat1 Hp)|].
      apply id_left.
  Qed.

  Lemma is_linear_from_upshift_iff_envelope_counit_precompose {a : N} {b : envelope_ob}
    (f : envelope_duploid⟦envelope_ob_of_negative a, b⟧)
    : #(R ∙ L) (ε a) · f♭ = ε ((R ∙ L) a) · f♭ <->
        is_linear f.
  Proof.
    eapply logeq_trans;
      [|apply (is_linear_iff_force_unwrap (D:=envelope_duploid))].
    eapply logeq_trans;
      [|apply issymm_logeq, (weq_to_iff (oblique_mor_negative_path_weq θ _ _))].
    cbn.
    now rewrite !id_left, !functor_id, !id_left, !id_right.
  Qed.

  Lemma is_positive_envelope_upshift_iff_pre_fixed_point (a : N)
    : # (R ∙ L) (ε a) = ε ((R ∙ L) a)
      <-> is_positive (M:=envelope_duploid) (envelope_ob_of_negative a).
  Proof.
    eapply logeq_trans;
      [|apply (is_positive_iff_linear_wrap (D:=envelope_duploid))].
    eapply logeq_trans;
      [|apply is_linear_from_upshift_iff_envelope_counit_precompose].
    cbn.
    now rewrite !id_right.
  Qed.

  Lemma envelope_negative_lift {a b : envelope_ob}
    (f : envelope_duploid⟦a, b⟧)
    : (negative_lift f : envelope_duploid⟦_, _⟧) = f.
  Proof.
    envelope_induction' b.
    - intro; apply isaset_oblique_mor.
    - intro Hn.
      etrans; [apply (envelope_compose_known (ii1 Hn) _ f (envelope_delay b))|].
      apply oblique_mor_positive_path; cbn.
      etrans; [apply assoc'|].
      etrans; [apply cancel_precomposition, (is_inverse_in_precat2 Hn)|].
      apply id_right.
    - intro Hp.
      etrans; [apply (envelope_compose_known (ii2 Hp) _ f (envelope_delay b))|].
      apply oblique_mor_negative_path; cbn.
      etrans; [apply cancel_precomposition, (is_inverse_in_precat2 Hp)|].
      apply id_right.
  Qed.

  Lemma is_thunkable_from_downshift_iff_envelope_unit_postcompose {a : envelope_ob} {b : P}
    (f : envelope_duploid⟦a, envelope_ob_of_positive b⟧)
    : f♯ · #(L ∙ R) (η b) = f♯ · η ((L ∙ R) b) <->
        is_thunkable f.
  Proof.
    eapply logeq_trans;
      [|apply (is_thunkable_iff_delay_wrap (D:=envelope_duploid))].
    eapply logeq_trans;
      [|apply issymm_logeq, (weq_to_iff (oblique_mor_positive_path_weq θ _ _))].
    cbn.
    now rewrite !id_right, !functor_id, !id_right, !id_left.
  Qed.

  Lemma is_negative_envelope_downshift_iff_pre_fixed_point (a : P)
    : # (L ∙ R) (η a) = η ((L ∙ R) a)
      <-> is_negative (M:=envelope_duploid) (envelope_ob_of_positive a).
  Proof.
    eapply logeq_trans;
      [|apply (is_negative_iff_thunkable_force (D:=envelope_duploid))].
    eapply logeq_trans;
      [|apply is_thunkable_from_downshift_iff_envelope_unit_postcompose].
    cbn.
    now rewrite !id_left.
  Qed.

  Lemma envelope_mor_from_negative_mor {a b : N}
    (f : a --> b)
    : linear_and_thunkable_mor (M:=envelope_duploid)
        (envelope_ob_of_negative a)
        (envelope_ob_of_negative b).
  Proof.
    transparent assert (f' :
        (envelope_duploid⟦
             envelope_ob_of_negative a,
             envelope_ob_of_negative b⟧)). {
      use make_oblique_mor_positive.
      + exact (ε a · f).
      + exact (#R f).
      + abstract (
            rewrite <- (id_left (#R f)), φ_adj_inv_natural_postcomp;
            now rewrite φ_adj_inv_identity).
    }
    exists f'.
    apply make_is_linear_and_thunkable.
    - abstract (apply is_linear_of_force_unwrap;
                apply oblique_mor_positive_path; cbn;
                rewrite !id_left, functor_id, id_left, !id_right;
                apply pathsinv0, functor_comp).
    - abstract (apply is_thunkable_of_delay_wrap;
                apply oblique_mor_positive_path; cbn;
                now rewrite !id_left, !id_right).
  Defined.

  Lemma envelope_mor_from_positive_mor {a b : P}
    (f : a --> b)
    : linear_and_thunkable_mor (M:=envelope_duploid)
        (envelope_ob_of_positive a)
        (envelope_ob_of_positive b).
  Proof.
    transparent assert (f' :
        (envelope_duploid⟦
             envelope_ob_of_positive a,
             envelope_ob_of_positive b⟧)). {
      use make_oblique_mor_negative.
      + exact (#L f).
      + exact (f · η b).
      + abstract (
            rewrite <- (id_right (#L f)), φ_adj_natural_precomp;
            now rewrite φ_adj_identity).
    }
    exists f'.
    apply make_is_linear_and_thunkable.
    - abstract (apply is_linear_of_force_unwrap;
                apply oblique_mor_negative_path; cbn;
                now rewrite !id_right, !id_left).
    - abstract (apply is_thunkable_of_delay_wrap;
                apply oblique_mor_negative_path; cbn;
                rewrite !id_right, functor_id, id_left, !id_right;
                apply pathsinv0, functor_comp).
  Defined.

  Definition negative_category_to_envelope_duploid_data
    : functor_data N envelope_duploid⁻ₗ.
  Proof.
    use make_functor_data.
    - intro n.
      exists (envelope_ob_of_negative n).
      apply is_negative_envelope_ob_of_negative.
    - intros a b f.
      refine (_,,tt).
      exists (envelope_mor_from_negative_mor f).
      apply linear_and_thunkable_mor_is_linear_and_thunkable.
  Defined.

  Lemma negative_category_to_envelope_duploid_is_functor
    : is_functor negative_category_to_envelope_duploid_data.
  Proof.
    use make_is_functor; red; intros;
      do 2 apply carrier_eq;
      apply oblique_mor_positive_path; cbn.
    - apply functor_id.
    - etrans; [apply functor_comp|].
      apply cancel_postcomposition, pathsinv0, id_right.
  Qed.

  Definition negative_category_to_envelope_duploid : N ⟶ envelope_duploid⁻ₗ
    := make_functor _ negative_category_to_envelope_duploid_is_functor.

  Definition positive_category_to_envelope_duploid_data
    : functor_data P envelope_duploid⁺ₜ.
  Proof.
    use make_functor_data.
    - intro p.
      exists (envelope_ob_of_positive p).
      apply is_positive_envelope_ob_of_positive.
    - intros a b f.
      refine (_,,tt).
      exists (envelope_mor_from_positive_mor f).
      apply linear_and_thunkable_mor_is_linear_and_thunkable.
  Defined.

  Lemma positive_category_to_envelope_duploid_is_functor
    : is_functor positive_category_to_envelope_duploid_data.
  Proof.
    use make_is_functor; red; intros;
      do 2 apply carrier_eq;
      apply oblique_mor_negative_path; cbn.
    - apply functor_id.
    - etrans; [apply functor_comp|].
      apply cancel_precomposition, pathsinv0, id_left.
  Qed.

  Definition positive_category_to_envelope_duploid : P ⟶ envelope_duploid⁺ₜ
    := make_functor _ positive_category_to_envelope_duploid_is_functor.

  Lemma envelope_lt_iso_from_negative_iso {a b : N}
    (f : z_iso a b)
    : lt_iso (M:=envelope_duploid)
        (envelope_ob_of_negative a)
        (envelope_ob_of_negative b).
  Proof.
    use make_lt_iso'.
    - apply envelope_mor_from_negative_mor, (z_iso_mor f).
    - apply envelope_mor_from_negative_mor, (inv_from_z_iso f).
    - split.
      + apply oblique_mor_positive_path; cbn.
        rewrite id_right, <- functor_comp, <- functor_id.
        apply maponpaths, (is_inverse_in_precat1 f).
      + apply oblique_mor_positive_path; cbn.
        rewrite id_right, <- functor_comp, <- functor_id.
        apply maponpaths, (is_inverse_in_precat2 f).
  Defined.

  Lemma envelope_lt_iso_from_positive_iso {a b : P}
    (f : z_iso a b)
    : lt_iso (M:=envelope_duploid)
        (envelope_ob_of_positive a)
        (envelope_ob_of_positive b).
  Proof.
    use make_lt_iso'.
    - apply envelope_mor_from_positive_mor, (z_iso_mor f).
    - apply envelope_mor_from_positive_mor, (inv_from_z_iso f).
    - split.
      + apply oblique_mor_negative_path; cbn.
        rewrite id_left, <- functor_comp, <- functor_id.
        apply maponpaths, (is_inverse_in_precat1 f).
      + apply oblique_mor_negative_path; cbn.
        rewrite id_left, <- functor_comp, <- functor_id.
        apply maponpaths, (is_inverse_in_precat2 f).
  Defined.

End envelope_defs.

(** ** 4. Structure theorem *)

Section equalized.
  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.

  Definition fully_faithful_negative_category_to_envelope_duploid_iff
    : is_negative_equalizing θ <-> fully_faithful (negative_category_to_envelope_duploid θ).
  Proof.
    assert (Hweq : ∏ n m (f : negative_category_to_envelope_duploid θ n --> negative_category_to_envelope_duploid θ m),
             hfiber # (negative_category_to_envelope_duploid θ) f ≃ (∑ f' : N ⟦ n, m ⟧, ε n · f' = (pr11 f) ♭)). {
      intros n m f.
      apply (weqtotal2 (idweq _)); intro f'.
      eapply weqcomp (* paths over ∑ _, tt *).
      1: apply (weqonpathsincl pr1), isinclpr1; intro; apply isapropifcontr, iscontrunit.
      eapply weqcomp (* paths over ∑ f, ish_linear f *).
      1: apply (weqonpathsincl pr1), isinclpr1; intro; apply propproperty.
      (* paths over oblique_mor θ n m *)
      apply (weqonpathsincl (λ f, f♭)), isinclweq; intro; apply isweq_oblique_mor_negative.
    }
    split.
    - intros Hnegative_eq n m f.
      apply (iscontrweqb (Hweq n m f)).
      apply Hnegative_eq.
      induction f as [f Hf0], f as [f Hf]; cbn; clear Hf0.
      apply (is_linear_from_upshift_iff_envelope_counit_precompose θ f).
      exact Hf.
    - intros Hff n m f Hf.
      apply (is_linear_from_upshift_iff_envelope_counit_precompose θ
               (a:=n)
               (b:=envelope_ob_of_negative _ m)
               (oblique_mor_from_negative θ f))
        in Hf.
      apply (iscontrweqf (Hweq n m (((oblique_mor_from_negative θ f),,Hf),,tt))).
      apply Hff.
  Defined.

  Lemma split_essentially_surjective_negative_category_to_envelope_duploid
    : split_essentially_surjective (negative_category_to_envelope_duploid θ).
  Proof.
    intro a; cbn in a.
    exists (envelope_negative_ob θ (pr1 a : envelope_ob θ)).
    set (α := lt_iso_upshift_of_negative (D:=envelope_duploid θ) (pr1 a) (pr2 a)).
    use make_z_iso.
    - exact (make_linear_mor (lt_iso_mor α) (lt_iso_is_linear_and_thunkable α),,tt).
    - exact (make_linear_mor (lt_iso_inverse α) (lt_iso_inverse α),,tt).
    - split; do 2 apply carrier_eq; apply lt_iso_is_inverse.
  Defined.

  Lemma adj_equivalence_negative_category_to_envelope_duploid_iff
    : is_negative_equalizing θ
      <-> adj_equivalence_of_cats (negative_category_to_envelope_duploid θ).
  Proof.
    split.
    - intro H.
      apply rad_equivalence_of_cats'.
      + apply fully_faithful_negative_category_to_envelope_duploid_iff, H.
      + exact split_essentially_surjective_negative_category_to_envelope_duploid.
    - intro H.
      apply fully_faithful_negative_category_to_envelope_duploid_iff.
      apply fully_faithful_from_equivalence, H.
  Defined.

  Definition fully_faithful_positive_category_to_envelope_duploid_iff
    : is_positive_equalizing θ <-> fully_faithful (positive_category_to_envelope_duploid θ).
  Proof.
    assert (Hweq : ∏ p q (f : positive_category_to_envelope_duploid θ p --> positive_category_to_envelope_duploid θ q),
             hfiber # (positive_category_to_envelope_duploid θ) f ≃ (∑ f' : P ⟦ p, q ⟧, f' · η q = (pr11 f) ♯)). {
      intros p q f.
      apply (weqtotal2 (idweq _)); intro f'.
      eapply weqcomp (* paths over ∑ _, tt *).
      1: apply (weqonpathsincl pr1), isinclpr1; intro; apply isapropifcontr, iscontrunit.
      eapply weqcomp (* paths over ∑ f, ish_thunkable f *).
      1: apply (weqonpathsincl pr1), isinclpr1; intro; apply propproperty.
      (* paths over oblique_mor θ p q *)
      apply (weqonpathsincl (λ f, f♯)), isinclweq; intro; apply isweq_oblique_mor_positive.
    }
    split.
    - intros Hpositive_eq p q f.
      apply (iscontrweqb (Hweq p q f)).
      apply Hpositive_eq.
      induction f as [f Hf0], f as [f Hf]; cbn; clear Hf0.
      apply (is_thunkable_from_downshift_iff_envelope_unit_postcompose θ f).
      exact Hf.
    - intros Hff p q f Hf.
      apply (is_thunkable_from_downshift_iff_envelope_unit_postcompose θ
               (b:=q)
               (a:=envelope_ob_of_positive _ p)
               (oblique_mor_from_positive θ f))
        in Hf.
      apply (iscontrweqf (Hweq p q (((oblique_mor_from_positive θ f),,Hf),,tt))).
      apply Hff.
  Defined.

  Lemma split_essentially_surjective_positive_category_to_envelope_duploid
    : split_essentially_surjective (positive_category_to_envelope_duploid θ).
  Proof.
    intro a; cbn in a.
    exists (envelope_positive_ob θ (pr1 a : envelope_ob θ)).
    set (α := lt_iso_downshift_of_positive (D:=envelope_duploid θ) (pr1 a) (pr2 a)).
    use make_z_iso.
    - exact (make_thunkable_mor (lt_iso_inverse α) (lt_iso_inverse α),,tt).
    - exact (make_thunkable_mor (lt_iso_mor α) (lt_iso_is_linear_and_thunkable α),,tt).
    - split; do 2 apply carrier_eq; apply lt_iso_is_inverse.
  Defined.

  Lemma adj_equivalence_positive_category_to_envelope_duploid_iff
    : is_positive_equalizing θ
      <-> adj_equivalence_of_cats (positive_category_to_envelope_duploid θ).
  Proof.
    split.
    - intro H.
      apply rad_equivalence_of_cats'.
      + apply fully_faithful_positive_category_to_envelope_duploid_iff, H.
      + exact split_essentially_surjective_positive_category_to_envelope_duploid.
    - intro H.
      apply fully_faithful_positive_category_to_envelope_duploid_iff.
      apply fully_faithful_from_equivalence, H.
  Defined.

  (** Univalence *)

  Hypothesis (Hnegative_univalent : is_univalent N).
  Hypothesis (Hpositive_univalent : is_univalent P).
  Hypothesis (Hnegative_eq : is_negative_equalizing θ).
  Hypothesis (Hpositive_eq : is_positive_equalizing θ).

  Definition envelope_preob_rxgraph0 : rxgraph.
  Proof.
    use total_rxgraph. {
      refine (_ × _)%rxgraph_spec.
      - exact (make_univalent_rxgraph (category_to_rxgraph P) Hpositive_univalent).
      - exact (make_univalent_rxgraph (category_to_rxgraph N) Hnegative_univalent).
    }
    use make_disp_rxgraph'.
    - intros [p n]; exact (oblique_mor θ p n).
    - intros [p n] [q m] [Hpq Hmn] f g.
      cbn in Hpq, Hmn.
      exact (oblique_compose_negative θ f Hmn =
               oblique_compose_positive θ Hpq g).
    - intros [p n] f.
      abstract (apply oblique_mor_negative_path; cbn;
                now rewrite functor_id, id_left, id_right).
  Defined.

  Lemma is_univalent_envelope_preob_rxgraph0
    : is_rxgraph_univalent envelope_preob_rxgraph0.
  Proof.
    apply is_univalent_total_rxgraph.
    1: apply rxgraph_univalence.
    intros [p n].
    apply is_rxgraph_univalent_from_isaprop_edges_from.
    intro f. cbn in f.
    apply (isofhlevelweqb 1 (Y:=paths_from f)).
    2: apply isapropifcontr, iscontr_paths_from.
    use weqbandf; [apply idweq|]; cbn.
    intro g.
    apply weqiff; [split | |].
    - intro H.
      refine (_ @ H @ _).
      + apply oblique_mor_negative_path, pathsinv0, id_right.
      + apply oblique_mor_positive_path, id_left.
    - intro H.
      refine (_ @ H @ _).
      + apply oblique_mor_negative_path, id_right.
      + apply oblique_mor_positive_path, pathsinv0, id_left.
    - apply isaset_oblique_mor.
    - apply isaset_oblique_mor.
  Qed.

  Definition envelope_preob_iso (a b : envelope_preob θ) : UU
    := ∑ eq : (z_iso (envelope_positive_ob _ a) (envelope_positive_ob _ b))
                × (z_iso (envelope_negative_ob _ a) (envelope_negative_ob _ b)),
        oblique_compose_negative θ (envelope_cross_mor _ a) (pr2 eq) =
          oblique_compose_positive θ (pr1 eq) (envelope_cross_mor _ b).

  Definition make_envelope_preob_iso {a b : envelope_preob θ}
    (f : z_iso (envelope_positive_ob _ a) (envelope_positive_ob _ b))
    (g : z_iso (envelope_negative_ob _ a) (envelope_negative_ob _ b))
    (H : oblique_compose_negative θ (envelope_cross_mor _ a) g =
           oblique_compose_positive θ f (envelope_cross_mor _ b))
    : envelope_preob_iso a b
    := (f,,g),,H.

  Definition envelope_preob_iso_identity (a : envelope_preob θ)
    : envelope_preob_iso a a.
  Proof.
    exists (identity_z_iso _,,identity_z_iso _).
    intermediate_path (envelope_cross_mor θ a).
    - apply oblique_mor_negative_path, id_right.
    - apply oblique_mor_positive_path, pathsinv0, id_left.
  Defined.

  Definition envelope_preob_rxgraph : univalent_rxgraph.
  Proof.
    use make_univalent_rxgraph; [use make_rxgraph'|].
    - exact (envelope_preob θ).
    - intros a b; exact (envelope_preob_iso a b).
    - intros a; exact (envelope_preob_iso_identity a).
    - use (rxgraph_univalent_from_iso_f
             envelope_preob_rxgraph0 is_univalent_envelope_preob_rxgraph0).
      abstract (use make_rxgraph_iso;
                [ apply (make_pregraph_iso (idweq _) (λ a b, idweq _))
                | intros a;
                  apply subtypePath'; [|apply isaset_oblique_mor];
                  reflexivity ]).
  Defined.

  Definition envelope_ob_rxgraph : univalent_rxgraph.
  Proof.
    exact ({ a : envelope_preob_rxgraph ∇ envelope_polarization θ a })%rxgraph_spec.
  Defined.

  Definition lt_iso_of_positive_to_positive_iso (a b : envelope_duploid θ)
    (H : lt_iso a b)
    (Ha : is_positive a)
    : z_iso
        (envelope_positive_ob _ (a : envelope_ob _))
        (envelope_positive_ob _ (b : envelope_ob _)).
  Proof.
    apply (iso_from_fully_faithful_reflection
             (pr1 fully_faithful_positive_category_to_envelope_duploid_iff Hpositive_eq)).
    refine (weq_z_iso_lt_iso_positive _ _ (_ : lt_iso (⇓a) (⇓b))).
    refine (lt_iso_compose _ (lt_iso_compose H _)).
    - apply lt_iso_inv, lt_iso_downshift_of_positive, Ha.
    - apply lt_iso_downshift_of_positive, (is_positive_of_lt_iso H), Ha.
  Defined.

  Definition lt_iso_of_negative_to_negative_iso (a b : envelope_duploid θ)
    (H : lt_iso a b)
    (Ha : is_negative a)
    : z_iso
        (envelope_negative_ob _ (a : envelope_ob _))
        (envelope_negative_ob _ (b : envelope_ob _)).
  Proof.
    apply (iso_from_fully_faithful_reflection
             (pr1 fully_faithful_negative_category_to_envelope_duploid_iff Hnegative_eq)).
    refine (weq_z_iso_lt_iso_negative _ _ (_ : lt_iso (⇑a) (⇑b))).
    refine (lt_iso_compose _ (lt_iso_compose H _)).
    - apply lt_iso_upshift_of_negative, Ha.
    - apply lt_iso_inv, lt_iso_upshift_of_negative, (is_negative_of_lt_iso H), Ha.
  Defined.

  Lemma envelope_chosen_negative_of_positive_iff_is_negative (p : P)
    : is_negative (M:=envelope_duploid θ) (envelope_ob_of_positive θ p)
        <-> envelope_chosen_negative θ (envelope_ob_of_positive θ p).
  Proof.
    eapply logeq_trans;
      [apply issymm_logeq, (is_negative_envelope_downshift_iff_pre_fixed_point θ p)|].
    eapply logeq_trans;
      [|apply weq_to_iff, invweq,
        (is_positive_fixed_point_weq_pre_fixed_point θ Hpositive_eq)].
    apply isrefl_logeq.
  Qed.

  Lemma envelope_chosen_positive_of_negative_iff_is_positive (n : N)
    : is_positive (M:=envelope_duploid θ) (envelope_ob_of_negative θ n)
        <-> envelope_chosen_positive θ (envelope_ob_of_negative θ n).
  Proof.
    eapply logeq_trans;
      [apply issymm_logeq, (is_positive_envelope_upshift_iff_pre_fixed_point θ n)|].
    eapply logeq_trans;
      [|apply weq_to_iff, invweq,
        (is_negative_fixed_point_weq_pre_fixed_point θ Hnegative_eq)].
    apply isrefl_logeq.
  Qed.

  (** Positive category is univalent *)

  Lemma envelope_chosen_positive_of_is_positive (a : envelope_duploid θ)
    (Hp : is_positive a) : envelope_chosen_positive θ (a : envelope_ob θ).
  Proof.
    set (a' := a : envelope_ob _).
    generalize (a' : envelope_polarization θ a').
    apply (envelope_polarization_rec' θ (a:=a')).
    1: intro; apply isaprop_is_z_isomorphism.
    2: easy.
    intro Hn.
    eassert (Hupshift : envelope_chosen_positive θ (envelope_upshift θ a')). {
      apply (pr1 (envelope_chosen_positive_of_negative_iff_is_positive (envelope_negative_ob _ a'))).
      refine (is_positive_of_lt_iso _ Hp).
      apply lt_iso_inv, (lt_iso_upshift_of_negative a).
      apply is_negative_of_envelope_chosen_negative, Hn.
    }
    change (is_z_isomorphism (envelope_cross_mor θ a')♭).
    rewrite <- oblique_mor_positive_transpose; unfold φ_adj_inv.
    apply is_z_isomorphism_comp.
    - apply functor_on_is_z_isomorphism, Hn.
    - apply Hupshift.
  Qed.

  Lemma envelope_chosen_positive_weq_is_positive (a : envelope_duploid θ)
    : is_positive a ≃ envelope_chosen_positive θ (a : envelope_ob θ).
  Proof.
    apply weqiff; [split | |].
    - apply envelope_chosen_positive_of_is_positive.
    - apply is_positive_of_envelope_chosen_positive.
    - apply isaprop_is_positive.
    - apply isaprop_envelope_chosen_positive.
  Qed.

  Lemma envelope_ob_eq_positive' (a : envelope_ob θ)
    (Ha : envelope_chosen_positive _ a)
    : a = envelope_downshift _ a.
  Proof.
    apply (edge_to_id envelope_ob_rxgraph).
    use make_envelope_preob_iso; cbn.
    - apply identity_z_iso.
    - apply z_iso_inv, (make_z_iso' _ Ha).
    - intermediate_path (oblique_positive_identity θ (envelope_positive_ob θ a)).
      + apply oblique_mor_negative_path; cbn.
        exact (is_inverse_in_precat1 Ha).
      + apply oblique_mor_positive_path.
        apply pathsinv0, id_left.
  Defined.

  Lemma envelope_ob_eq_positive (a : envelope_ob θ)
    (Ha : is_positive (M:=envelope_duploid θ) a)
    : a = envelope_ob_of_positive _ (envelope_positive_ob _ a).
  Proof.
    apply envelope_chosen_positive_of_is_positive in Ha.
    apply envelope_ob_eq_positive', Ha.
  Defined.

  Lemma envelope_positive_ob_eq_positive
    (a : (envelope_duploid θ)⁺)
    : a = envelope_ob_of_positive θ (envelope_positive_ob θ (pr1 a : envelope_ob _)),,is_positive_envelope_ob_of_positive θ _.
  Proof.
    induction a as [a Ha].
    apply carrier_eq; cbn.
    apply envelope_ob_eq_positive, Ha.
  Defined.

  Lemma isweq_on_objects_positive_category_to_envelope_duploid
    : isweq (functor_on_objects (positive_category_to_envelope_duploid θ)).
  Proof.
    use isweq_iso.
    - intro a; cbn in a.
      exact (envelope_positive_ob θ (pr1 a : envelope_ob θ)).
    - easy.
    - intro a; cbn in a |- *.
      apply pathsinv0, (envelope_positive_ob_eq_positive a).
  Defined.

  Lemma is_catiso_positive_category_to_envelope_duploid
    : is_catiso (positive_category_to_envelope_duploid θ).
  Proof.
    use make_dirprod.
    - apply fully_faithful_positive_category_to_envelope_duploid_iff,
        Hpositive_eq.
    - apply isweq_on_objects_positive_category_to_envelope_duploid.
  Qed.

  Lemma eq_positive_category_envelope_duploid_positive_thunkable
    : P = (envelope_duploid θ)⁺ₜ.
  Proof.
    apply catiso_to_category_path.
    exact (_,,is_catiso_positive_category_to_envelope_duploid).
  Defined.

  Lemma is_univalent_envelope_positive_thunkable_category
    : is_univalent (envelope_duploid θ)⁺ₜ.
  Proof.
    exact (transportf _
             eq_positive_category_envelope_duploid_positive_thunkable
             Hpositive_univalent).
  Qed.

  (** Negative category is univalent *)

  Lemma envelope_chosen_negative_of_is_negative (a : envelope_duploid θ)
    (Hn : is_negative a) : envelope_chosen_negative θ (a : envelope_ob θ).
  Proof.
    set (a' := a : envelope_ob _).
    generalize (a' : envelope_polarization θ a').
    apply (envelope_polarization_rec' θ (a:=a')).
    1: intro; apply isaprop_is_z_isomorphism.
    1: easy.
    intro Hp.
    eassert (Hdownshift : envelope_chosen_negative θ (envelope_downshift θ a')). {
      apply (pr1 (envelope_chosen_negative_of_positive_iff_is_negative (envelope_positive_ob _ a'))).
      refine (is_negative_of_lt_iso _ Hn).
      apply (lt_iso_downshift_of_positive a).
      apply is_positive_of_envelope_chosen_positive, Hp.
    }
    change (is_z_isomorphism (envelope_cross_mor θ a')♯).
    rewrite <- oblique_mor_negative_transpose; unfold φ_adj.
    apply is_z_isomorphism_comp.
    - apply Hdownshift.
    - cbn.
      apply functor_on_is_z_isomorphism, Hp.
  Qed.

  Lemma envelope_chosen_negative_weq_is_negative (a : envelope_duploid θ)
    : is_negative a ≃ envelope_chosen_negative θ (a : envelope_ob θ).
  Proof.
    apply weqiff; [split | |].
    - apply envelope_chosen_negative_of_is_negative.
    - apply is_negative_of_envelope_chosen_negative.
    - apply isaprop_is_negative.
    - apply isaprop_envelope_chosen_negative.
  Qed.

  Lemma envelope_ob_eq_negative' (a : envelope_ob θ)
    (Ha : envelope_chosen_negative _ a)
    : a = envelope_upshift _ a.
  Proof.
    apply (edge_to_id envelope_ob_rxgraph).
    use make_envelope_preob_iso; cbn.
    - apply (make_z_iso' _ Ha).
    - apply identity_z_iso.
    - intermediate_path (envelope_cross_mor θ a).
      + apply oblique_mor_negative_path; cbn.
        apply id_right.
      + apply oblique_mor_positive_path.
        apply pathsinv0, id_right.
  Defined.

  Lemma envelope_ob_eq_negative (a : envelope_ob θ)
    (Ha : is_negative (M:=envelope_duploid θ) a)
    : a = envelope_ob_of_negative _ (envelope_negative_ob _ a).
  Proof.
    apply envelope_chosen_negative_of_is_negative in Ha.
    apply envelope_ob_eq_negative', Ha.
  Defined.

  Lemma envelope_negative_ob_eq_negative
    (a : (envelope_duploid θ)⁻)
    : a = envelope_ob_of_negative θ (envelope_negative_ob θ (pr1 a : envelope_ob _)),,is_negative_envelope_ob_of_negative θ _.
  Proof.
    induction a as [a Ha].
    apply carrier_eq; cbn.
    apply envelope_ob_eq_negative, Ha.
  Defined.

  Lemma isweq_on_objects_negative_category_to_envelope_duploid
    : isweq (functor_on_objects (negative_category_to_envelope_duploid θ)).
  Proof.
    use isweq_iso.
    - intro a; cbn in a.
      exact (envelope_negative_ob θ (pr1 a : envelope_ob θ)).
    - easy.
    - intro a; cbn in a |- *.
      apply pathsinv0, (envelope_negative_ob_eq_negative a).
  Defined.

  Lemma is_catiso_negative_category_to_envelope_duploid
    : is_catiso (negative_category_to_envelope_duploid θ).
  Proof.
    use make_dirprod.
    - apply fully_faithful_negative_category_to_envelope_duploid_iff,
        Hnegative_eq.
    - apply isweq_on_objects_negative_category_to_envelope_duploid.
  Qed.

  Lemma eq_negative_category_envelope_duploid_negative_linear
    : N = (envelope_duploid θ)⁻ₗ.
  Proof.
    apply catiso_to_category_path.
    exact (_,,is_catiso_negative_category_to_envelope_duploid).
  Defined.

  Lemma is_univalent_envelope_negative_linear_category
    : is_univalent (envelope_duploid θ)⁻ₗ.
  Proof.
    exact (transportf _
             eq_negative_category_envelope_duploid_negative_linear
             Hnegative_univalent).
  Qed.

  Theorem is_univalent_envelope_duploid'
    : is_duploid_univalent (envelope_duploid θ).
  Proof.
    apply is_duploid_univalent_from_positive_thunkable_and_negative_linear_categories.
    - apply is_univalent_envelope_positive_thunkable_category.
    - apply is_univalent_envelope_negative_linear_category.
  Qed.
End equalized.

(** Restatement with more bundling *)
Theorem is_univalent_envelope_duploid
  {N P : univalent_category}
  (θ : adjunction P N)
  (Hθ : is_fully_equalizing θ)
  : is_duploid_univalent (envelope_duploid θ).
Proof.
  apply is_univalent_envelope_duploid'.
  - exact (univalent_category_is_univalent N).
  - exact (univalent_category_is_univalent P).
  - exact Hθ.
  - exact Hθ.
Qed.

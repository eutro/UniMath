(********************************************************************************

 The Single-Sorted Duploid arising from an Adjunction

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition of the envelope duploid
 2. Weak equivalence with the oblique duploid
 3. Lemmas about the envelope duploid
 4. Structure theorem

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

Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Oblique.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.TwoSorted.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.ShiftFunctors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.ShiftFacts.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

Declare Scope cross_mor.
Delimit Scope cross_mor with cross_mor.
Local Open Scope cross_mor.

Section cross_mor_defs.
  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.

  Definition cross_mor (p : P) (n : N) : UU
    := ∑ (f : N⟦L p, n⟧) (g : P⟦p, R n⟧), φ_adj θ f = g.
  Definition cross_mor_negative {p : P} {n : N} (f : cross_mor p n) : N⟦L p, n⟧
    := pr1 f.
  Definition cross_mor_positive {p : P} {n : N} (f : cross_mor p n) : P⟦p, R n⟧
    := pr12 f.
  Local Notation "f '♭'" := (cross_mor_negative f) : cross_mor.
  Local Notation "f '♯'" := (cross_mor_positive f) : cross_mor.

  Definition cross_mor_eq_negative {p : P} {n : N} (f : cross_mor p n)
    : φ_adj θ f♭ = f♯ := pr22 f.
  Definition cross_mor_eq_positive {p : P} {n : N} (f : cross_mor p n)
    : φ_adj_inv θ f♯ = f♭.
  Proof.
    intermediate_path (φ_adj_inv θ (φ_adj θ f♭)).
    - apply maponpaths, pathsinv0, cross_mor_eq_negative.
    - apply φ_adj_inv_after_φ_adj.
  Qed.

  Definition make_cross_mor_negative {p : P} {n : N}
    (f : N⟦L p, n⟧) (g : P⟦p, R n⟧) (H : φ_adj θ f = g)
    : cross_mor p n := f,,g,,H.
  Definition make_cross_mor_positive {p : P} {n : N}
    (f : N⟦L p, n⟧) (g : P⟦p, R n⟧) (H : f = φ_adj_inv θ g)
    : cross_mor p n.
  Proof.
    apply (make_cross_mor_negative f g).
    abstract (apply (maponpaths (φ_adj θ)) in H;
              refine (H @ _);
              apply φ_adj_after_φ_adj_inv).
  Defined.

  Definition make_cross_mor_negative' {p : P} {n : N}
    (f : N⟦L p, n⟧) : cross_mor p n
    := make_cross_mor_negative f _ (idpath _).
  Definition make_cross_mor_positive' {p : P} {n : N}
    (g : P⟦p, R n⟧) : cross_mor p n
    := make_cross_mor_positive _ g (idpath _).

  Definition cross_mor_negative_path {p : P} {n : N}
    (f g : cross_mor p n) (H : f♭ = g♭) : f = g.
  Proof.
    induction f as [fb fs], g as [gb gs],
          fs as [fs Hf], gs as [gs Hg].
    cbn in H; induction H.
    set (Hfg := !Hf @ Hg).
    induction Hfg.
    assert (Hfgeq : Hf = Hg); [apply proofirrelevance, homset_property|].
    induction Hfgeq.
    reflexivity.
  Qed.

  Definition cross_mor_negative_path_iff {p : P} {n : N}
    (f g : cross_mor p n) : f♭ = g♭ <-> f = g.
  Proof.
    split.
    - apply cross_mor_negative_path.
    - intro H; now induction H.
  Qed.

  Definition cross_mor_positive_path {p : P} {n : N}
    (f g : cross_mor p n) (H : f♯ = g♯) : f = g.
  Proof.
    set (Hf := cross_mor_eq_positive f).
    set (Hg := cross_mor_eq_positive g).
    induction f as [fb fs], g as [gb gs],
          fs as [fs Hf'], gs as [gs Hg'].
    cbn in H; induction H.
    cbn in Hf, Hg.
    set (Hfg := !Hf @ Hg).
    induction Hfg.
    assert (Hfgeq : Hf' = Hg'); [apply proofirrelevance, homset_property|].
    induction Hfgeq.
    reflexivity.
  Qed.

  Definition cross_mor_positive_path_iff {p : P} {n : N}
    (f g : cross_mor p n) : f♯ = g♯ <-> f = g.
  Proof.
    split.
    - apply cross_mor_positive_path.
    - intro H; now induction H.
  Qed.

  Lemma isaset_cross_mor {p n} : isaset (cross_mor p n).
  Proof.
    apply isaset_total2.
    1: apply homset_property.
    intro f.
    apply isaset_total2.
    1: apply homset_property.
    intro g.
    apply isasetaprop, homset_property.
  Qed.

  Lemma isweq_cross_mor_negative (p : P) (n : N) : isweq (@cross_mor_negative p n).
  Proof.
    use isweq_iso.
    - exact make_cross_mor_negative'.
    - intro f; now apply cross_mor_negative_path.
    - easy.
  Defined.

  Lemma isweq_cross_mor_positive (p : P) (n : N) : isweq (@cross_mor_positive p n).
  Proof.
    use isweq_iso.
    - exact make_cross_mor_positive'.
    - intro f; now apply cross_mor_positive_path.
    - easy.
  Defined.
End cross_mor_defs.

Notation "f '♭'" := (cross_mor_negative _ f) : cross_mor.
Notation "f '♯'" := (cross_mor_positive _ f) : cross_mor.

Section envelope_defs.
  (** ** 1. Definition of the envelope duploid *)

  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.

  (** A pre-object of the envelope. *)
  Definition envelope_preob := ∑ (pn : P × N), cross_mor θ (pr1 pn) (pr2 pn).
  Definition make_envelope_preob
    (p : P) (n : N) (cross : cross_mor θ p n)
    : envelope_preob := (p,,n),,cross.

  Definition envelope_negative_ob (a : envelope_preob) : N := pr21 a.
  Definition envelope_positive_ob (a : envelope_preob) : P := pr11 a.

  Local Notation "a '⁻'" := (envelope_negative_ob a) (at level 1) : duploid.
  Local Notation "a '⁺'" := (envelope_positive_ob a) (at level 1) : duploid.

  Definition envelope_mor (a b : envelope_preob) : UU := cross_mor θ a⁺ b⁻.
  Definition envelope_cross_mor (a : envelope_preob) : envelope_mor a a := pr2 a.
  Local Notation "a '►'" := (envelope_cross_mor a) : duploid.
  (* type in Emacs with agda-input using \t *)

  Arguments envelope_mor / _ _.

  Definition envelope_chosen_negative (a : envelope_preob) : UU := is_z_isomorphism a►♯.
  Identity Coercion Id_envelope_chosen_negative : envelope_chosen_negative >-> is_z_isomorphism.
  Definition envelope_chosen_positive (a : envelope_preob) : UU := is_z_isomorphism a►♭.
  Identity Coercion Id_envelope_chosen_positive : envelope_chosen_positive >-> is_z_isomorphism.
  Definition envelope_polarization_choice (a : envelope_preob) : UU
    := envelope_chosen_negative a ⨿ envelope_chosen_positive a.

  Arguments envelope_chosen_negative / _.
  Arguments envelope_chosen_positive / _.

  Definition envelope_mor_factor_chosen_negative {a b : envelope_preob}
    (f : envelope_mor a b) (negative : envelope_chosen_negative b)
    : a⁺ --> b⁺ := (f♯ · is_z_isomorphism_mor negative).
  Definition envelope_mor_factor_chosen_positive {a b : envelope_preob}
    (f : envelope_mor a b) (positive : envelope_chosen_positive a)
    : a⁻ --> b⁻ := (is_z_isomorphism_mor positive · f♭).

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
    - apply make_cross_mor_positive'.
      exact (f#⊖Hn · g♯).
    - apply make_cross_mor_negative'.
      exact (f♭ · g#⊕Hp).
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
    - apply cross_mor_positive_path; cbn.
      etrans; [apply cancel_postcomposition, (is_inverse_in_precat1 Hn)|].
      apply id_left.
    - apply cross_mor_negative_path; cbn.
      apply envelope_mor_factor_chosen_positive_eq.
  Qed.

  Definition envelope_compose_id_right {a b : envelope_preob}
    (f : envelope_mor a b)
    (choice : envelope_polarization_choice b)
    : envelope_compose' f (b►) choice = f.
  Proof.
    induction choice as [Hn | Hp]; cbn.
    - apply cross_mor_positive_path; cbn.
      apply envelope_mor_factor_chosen_negative_eq.
    - apply cross_mor_negative_path; cbn.
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
      etrans; [apply cancel_postcomposition, cross_mor_eq_positive|].
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
    apply cross_mor_negative_path; cbn.
    rewrite φ_adj_inv_natural_precomp, cross_mor_eq_positive, assoc.
    apply cancel_postcomposition.
    cancel_φ_adj.
    rewrite functor_comp, φ_adj_natural_precomp, φ_adj_natural_postcomp.
    rewrite cross_mor_eq_negative.
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
  Definition envelope_polarization (a : envelope_preob) : UU
    := ∥envelope_polarization_choice a∥.

  Lemma isaprop_envelope_polarization (a : envelope_preob) : isaprop (envelope_polarization a).
  Proof. apply isapropishinh. Qed.

  Definition envelope_compose {a b c : envelope_preob}
    (f : envelope_mor a b) (g : envelope_mor b c)
    (polarization : envelope_polarization b)
    : envelope_mor a c.
  Proof.
    refine (squash_to_set _ (envelope_compose' f g) _ polarization).
    - abstract (apply isaset_cross_mor).
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
    1: intro; apply isaset_cross_mor.
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
    - use make_cross_mor_negative.
      + exact (identity (L p)).
      + exact (η p).
      + apply φ_adj_identity.
  Defined.

  Lemma φ_adj_inv_identity (n : N)
    : φ_adj_inv θ (identity (R n)) = ε n.
  Proof.
    unfold φ_adj_inv.
    etrans; [apply cancel_postcomposition, functor_id|].
    apply id_left.
  Qed.

  Definition envelope_preob_of_negative (n : N) : envelope_preob.
  Proof.
    use make_envelope_preob.
    - exact (R n).
    - exact n.
    - use make_cross_mor_positive.
      + exact (ε n).
      + exact (identity (R n)).
      + apply pathsinv0, φ_adj_inv_identity.
  Defined.

  Lemma envelope_chosen_positive_of_positive (p : P)
    : envelope_chosen_positive (envelope_preob_of_positive p).
  Proof.
    exists (identity _).
    abstract (apply is_z_isomorphism_identity).
  Defined.

  Lemma envelope_chosen_negative_of_negative (n : N)
    : envelope_chosen_negative (envelope_preob_of_negative n).
  Proof.
    exists (identity _).
    abstract (apply is_z_isomorphism_identity).
  Defined.

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
      (apply envelope_compose_rec'; [intro; apply isaset_cross_mor | |]).
    1, 2: intro; apply envelope_compose_id_left.
    1, 2: intro; apply envelope_compose_id_right.
  Qed.

  Definition envelope_unital_premagmoid : unital_premagmoid
    := make_unital_premagmoid _ envelope_is_unital_premagmoid.

  Definition envelope_unital_magmoid : unital_magmoid.
  Proof.
    use (make_unital_magmoid envelope_unital_premagmoid).
    abstract (intros a b; apply isaset_cross_mor).
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
    - intro; apply isaset_cross_mor.
    - intro Hn.
      apply cross_mor_positive_path.
      cbn -[envelope_mor_factor_chosen_negative envelope_mor_factor_chosen_positive].
      rewrite <- φ_adj_natural_precomp, assoc.
      rewrite φ_adj_inv_natural_precomp.
      now rewrite cross_mor_eq_positive.
    - intro Hp; cbn.
      apply cross_mor_negative_path; cbn.
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
    - intro; apply isaset_cross_mor.
    - intro Hn; cbn.
      apply cross_mor_positive_path.
      now rewrite !assoc.
    - intro Hp.
      apply cross_mor_negative_path.
      cbn -[envelope_mor_factor_chosen_negative envelope_mor_factor_chosen_positive].
      rewrite <- φ_adj_inv_natural_postcomp, assoc'.
      rewrite φ_adj_natural_postcomp.
      now rewrite cross_mor_eq_negative.
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
  Proof.
    apply make_cross_mor_positive'.
    exact (identity (R a⁻)).
  Defined.
  Definition envelope_delay
    (a : envelope_preob) : envelope_mor a (envelope_upshift a).
  Proof. exact (a►). Defined.

  Definition envelope_wrap
    (a : envelope_preob) : envelope_mor a (envelope_downshift a).
  Proof.
    apply make_cross_mor_negative'.
    exact (identity (L a⁺)).
  Defined.
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
    apply cross_mor_positive_path; cbn.
    now rewrite !id_right, cross_mor_eq_positive.
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
    apply cross_mor_positive_path; cbn.
    now rewrite !assoc', !(is_inverse_in_precat2 Hn), !id_right, cross_mor_eq_positive.
  Qed.

  Lemma is_inverse_in_precat_envelope_force_delay (a : envelope_ob)
    : is_inverse_in_precat (C:=envelope_preduploid) (envelope_force a) (envelope_delay a).
  Proof.
    split; cbn.
    - envelope_induction' a.
      1: intro; apply isaset_cross_mor.
      + intro Hn; cbn.
        unfold envelope_delay, envelope_force; cbn.
        apply cross_mor_positive_path; cbn.
        rewrite id_left.
        apply (is_inverse_in_precat2 Hn).
      + intro Hp; cbn.
        unfold envelope_delay; cbn.
        apply cross_mor_positive_path; cbn.
        rewrite (is_inverse_in_precat2 Hp), id_right.
        now rewrite φ_adj_after_φ_adj_inv.
    - unfold envelope_delay, envelope_force; cbn.
      rewrite !id_right.
      now apply cross_mor_positive_path.
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
    apply cross_mor_negative_path; cbn.
    now rewrite !id_left, cross_mor_eq_negative.
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
    apply cross_mor_negative_path; cbn.
    now rewrite !assoc, !(is_inverse_in_precat1 Hp), !id_left, cross_mor_eq_negative.
  Qed.

  Lemma is_inverse_in_precat_envelope_unwrap_wrap (a : envelope_ob)
    : is_inverse_in_precat (C:=envelope_preduploid) (envelope_unwrap a) (envelope_wrap a).
  Proof.
    split; cbn.
    - envelope_induction' a.
      1: intro; apply isaset_cross_mor.
      + intro Hn; cbn.
        unfold envelope_unwrap, envelope_wrap; cbn.
        apply cross_mor_negative_path; cbn.
        rewrite (is_inverse_in_precat1 Hn), id_left.
        apply φ_adj_inv_after_φ_adj.
      + intro Hp; cbn.
        unfold envelope_unwrap, envelope_wrap; cbn.
        apply cross_mor_negative_path; cbn.
        rewrite id_right.
        apply (is_inverse_in_precat1 Hp).
    - unfold envelope_wrap, envelope_unwrap; cbn.
      rewrite !id_left.
      now apply cross_mor_negative_path.
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
    apply make_cross_mor_negative'.
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
    - intro a; induction a; [apply cross_mor_positive_path|apply cross_mor_negative_path]; cbn.
      + apply φ_adj_after_φ_adj_inv.
      + reflexivity.
    - intros a b c g f.
      induction a as [n | p], b as [m | q], c as [o | r]; cbn;
        first [rewrite id_right | rewrite id_left];
        apply cross_mor_positive_path; cbn;
        first [reflexivity|apply φ_adj_after_φ_adj_inv].
  Qed.

  Definition oblique_to_envelope : functor (oblique_duploid θ) envelope_duploid
    := make_functor _ is_functor_oblique_to_envelope.

  Lemma fully_faithful_oblique_to_envelope : fully_faithful oblique_to_envelope.
  Proof.
    intros a b; induction a, b;
      apply (invweq (make_weq _ (isweq_cross_mor_negative _ _ _))).
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
    - intro; apply isaset_cross_mor.
    - intro Hn.
      etrans; [apply (envelope_compose_known (ii1 Hn) _ (envelope_unwrap a) f)|].
      apply cross_mor_positive_path; cbn.
      etrans; [apply cancel_postcomposition, (is_inverse_in_precat1 Hn)|].
      apply id_left.
    - intro Hp.
      etrans; [apply (envelope_compose_known (ii2 Hp) _ (envelope_unwrap a) f)|].
      apply cross_mor_negative_path; cbn.
      etrans; [apply assoc|].
      etrans; [apply cancel_postcomposition, (is_inverse_in_precat1 Hp)|].
      apply id_left.
  Qed.

  Lemma is_linear_from_upshift_iff_envelope_counit_precompose {a b : envelope_ob}
    (f : envelope_duploid⟦envelope_upshift a, b⟧)
    : #(R ∙ L) (ε a⁻) · f♭ = ε ((R ∙ L) a⁻) · f♭ <->
        is_linear f.
  Proof.
    eapply logeq_trans;
      [|apply (is_linear_iff_force_unwrap (D:=envelope_duploid))].
    eapply logeq_trans; [|apply cross_mor_negative_path_iff].
    cbn.
    rewrite φ_adj_natural_postcomp, φ_adj_inv_natural_precomp.
    rewrite φ_adj_after_φ_adj_inv, !id_left, !id_right.
    rewrite !cross_mor_eq_positive.
    rewrite φ_adj_inv_identity.
    apply isrefl_logeq.
  Qed.

  Lemma is_positive_envelope_upshift_iff_pre_fixed_point (a : envelope_ob)
    : # (R ∙ L) (ε a⁻) = ε ((R ∙ L) a⁻)
      <-> is_positive (M:=envelope_duploid) (envelope_upshift a).
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
    - intro; apply isaset_cross_mor.
    - intro Hn.
      etrans; [apply (envelope_compose_known (ii1 Hn) _ f (envelope_delay b))|].
      apply cross_mor_positive_path; cbn.
      etrans; [apply assoc'|].
      etrans; [apply cancel_precomposition, (is_inverse_in_precat2 Hn)|].
      apply id_right.
    - intro Hp.
      etrans; [apply (envelope_compose_known (ii2 Hp) _ f (envelope_delay b))|].
      apply cross_mor_negative_path; cbn.
      etrans; [apply cancel_precomposition, (is_inverse_in_precat2 Hp)|].
      apply id_right.
  Qed.

  Lemma is_thunkable_from_downshift_iff_envelope_unit_postcompose {a b : envelope_ob}
    (f : envelope_duploid⟦a, envelope_downshift b⟧)
    : f♯ · #(L ∙ R) (η b⁺) = f♯ · η ((L ∙ R) b⁺) <->
        is_thunkable f.
  Proof.
    eapply logeq_trans;
      [|apply (is_thunkable_iff_delay_wrap (D:=envelope_duploid))].
    eapply logeq_trans; [|apply cross_mor_positive_path_iff].
    cbn.
    rewrite !φ_adj_natural_postcomp, !φ_adj_inv_natural_precomp.
    rewrite φ_adj_inv_after_φ_adj, !id_left, functor_id, !id_right.
    rewrite !cross_mor_eq_negative.
    rewrite φ_adj_identity.
    apply isrefl_logeq.
  Qed.

  Lemma is_negative_envelope_downshift_iff_pre_fixed_point (a : envelope_ob)
    : # (L ∙ R) (η a⁺) = η ((L ∙ R) a⁺)
      <-> is_negative (M:=envelope_duploid) (envelope_downshift a).
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
      use make_cross_mor_positive.
      + exact (ε a · f).
      + exact (#R f).
      + abstract (
            rewrite <- (id_left (#R f)), φ_adj_inv_natural_postcomp;
            now rewrite φ_adj_inv_identity).
    }
    exists f'.
    apply make_is_linear_and_thunkable.
    - abstract (apply is_linear_of_force_unwrap;
                apply cross_mor_positive_path; cbn;
                rewrite !id_left, !id_right;
                rewrite <- !φ_adj_natural_postcomp, assoc';
                cbn;
                apply maponpaths, cancel_precomposition;
                change (f'♭ = φ_adj_inv θ f'♯);
                apply pathsinv0, cross_mor_eq_positive).
    - abstract (apply is_thunkable_of_delay_wrap;
                apply cross_mor_positive_path; cbn;
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
      use make_cross_mor_negative.
      + exact (#L f).
      + exact (f · η b).
      + abstract (
            rewrite <- (id_right (#L f)), φ_adj_natural_precomp;
            now rewrite φ_adj_identity).
    }
    exists f'.
    apply make_is_linear_and_thunkable.
    - abstract (apply is_linear_of_force_unwrap;
                apply cross_mor_negative_path; cbn;
                now rewrite !id_right, !id_left).
    - abstract (apply is_thunkable_of_delay_wrap;
                apply cross_mor_negative_path; cbn;
                rewrite !id_right, !id_left;
                rewrite <- !φ_adj_inv_natural_precomp, assoc;
                cbn;
                apply maponpaths, cancel_postcomposition;
                change (f'♯ = φ_adj θ f'♭);
                apply pathsinv0, cross_mor_eq_negative).
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
      apply cross_mor_positive_path; cbn.
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
      apply cross_mor_negative_path; cbn.
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
      + apply cross_mor_positive_path; cbn.
        rewrite id_right, <- functor_comp, <- functor_id.
        apply maponpaths, (is_inverse_in_precat1 f).
      + apply cross_mor_positive_path; cbn.
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
      + apply cross_mor_negative_path; cbn.
        rewrite id_left, <- functor_comp, <- functor_id.
        apply maponpaths, (is_inverse_in_precat1 f).
      + apply cross_mor_negative_path; cbn.
        rewrite id_left, <- functor_comp, <- functor_id.
        apply maponpaths, (is_inverse_in_precat2 f).
  Defined.

End envelope_defs.

(** ** 4. Structure theorem *)

Section structure_theorem.
  Context (D : duploid).
  Let θ := left_adjoint_to_adjunction (are_adjoints_nat_hom_weq_upshift_downshift_negative_linear_to_positive_thunkable D).
  Let D' := envelope_duploid θ.

  Definition duploid_to_envelope_on_shifts_cross_mor (a : ob D) : D⁻ₗ⟦⇑⇓a, ⇑a⟧.
  Proof.
    apply (#(upshift_linear_to_negative_linear D)).
    exists (unwrap a).
    apply is_linear_unwrap.
  Defined.

  Definition duploid_to_envelope_on_shifts_cross_mor' (a : ob D) : D⁺ₜ⟦⇓a, ⇓⇑a⟧.
  Proof.
    apply (#(downshift_thunkable_to_positive_thunkable D)).
    exists (delay a).
    apply is_thunkable_delay.
  Defined.

  Lemma duploid_to_envelope_on_shifts_cross_mor_eq (a : ob D)
    : φ_adj θ (duploid_to_envelope_on_shifts_cross_mor a)
      = duploid_to_envelope_on_shifts_cross_mor' a.
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
    use make_cross_mor_negative.
    - exact (duploid_to_envelope_on_shifts_cross_mor a).
    - exact (duploid_to_envelope_on_shifts_cross_mor' a).
    - apply duploid_to_envelope_on_shifts_cross_mor_eq.
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
    use make_cross_mor_negative.
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
      apply cross_mor_negative_path.
      do 2 apply carrier_eq; cbn.
      apply maponpaths, magmoid_id_right.
    - intros a b c f g.
      cbn.
      unfold duploid_to_envelope_on_shifts_envelope_polarization.
      pattern (polarity_of D b).
      apply (has_polarity_rec' (polarity_of D b)).
      + intro; apply isaset_cross_mor.
      + intro Hn.
        apply cross_mor_positive_path.
        do 2 apply carrier_eq; cbn.
        etrans; [|apply cancel_postcomposition, downshiftf_comp, is_thunkable_negative_lift'].
        etrans; [|apply downshiftf_comp, is_thunkable_of_negative, Hn].
        apply maponpaths.
        apply pathsinv0, negative_lift_unique.
        etrans; [apply cancel_postcomposition, cancel_postcomposition, negative_lift_factors|].
        etrans; [apply assoc'_negative, Hn|].
        apply cancel_precomposition, negative_lift_factors.
      + intro Hp.
        apply cross_mor_negative_path.
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
      2: apply invweq; exact (make_weq _ (isweq_cross_mor_negative θ _ _)).
      intermediate_weq (D ₗ⟦⇓a, b⟧).
      1: apply invweq, (hom_weq2 (downshift_nathomweq_linear_'_left D)).
      apply (weq_from_fully_faithful (fully_faithful_from_equivalence _ _ _ (upshift_linear_to_negative_linear_is_equivalence D))
               (⇓a) b).
    - abstract (intros f; apply cross_mor_negative_path; now do 2 apply carrier_eq).
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

End structure_theorem.

Section equalized.
  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let HFG : are_adjoints L R := θ.
  Let η : functor_identity P ⟹ L ∙ R := unit_from_are_adjoints HFG.
  Let ε : R ∙ L ⟹ functor_identity N := counit_from_are_adjoints HFG.

  Definition is_negative_equalizing : UU
    := ∏ (n m : N) (f : (R ∙ L) n --> m) (H : #(R ∙ L) (ε n) · f = ε ((R ∙ L) n) · f),
      ∃! (f' : n --> m), ε n · f' = f.

  Lemma isaprop_is_negative_equalizing : isaprop is_negative_equalizing.
  Proof.
    do 4 (apply impred; intro).
    apply isapropiscontr.
  Qed.

  Definition is_positive_equalizing : UU
    := ∏ (p q : P) (f : p --> (L ∙ R) q) (H : f · #(L ∙ R) (η q) = f · η ((L ∙ R) q)),
       ∃! (f' : p --> q), f' · η q = f.

  Lemma isaprop_is_positive_equalizing : isaprop is_positive_equalizing.
  Proof.
    do 4 (apply impred; intro).
    apply isapropiscontr.
  Qed.

  Definition fully_faithful_negative_category_to_envelope_duploid_iff
    : is_negative_equalizing <-> fully_faithful (negative_category_to_envelope_duploid θ).
  Proof.
    assert (Hweq : ∏ n m (f : negative_category_to_envelope_duploid θ n --> negative_category_to_envelope_duploid θ m),
             hfiber # (negative_category_to_envelope_duploid θ) f ≃ (∑ f' : N ⟦ n, m ⟧, ε n · f' = (pr11 f) ♭)). {
      intros n m f.
      apply (weqtotal2 (idweq _)); intro f'.
      eapply weqcomp (* paths over ∑ _, tt *).
      1: apply (weqonpathsincl pr1), isinclpr1; intro; apply isapropifcontr, iscontrunit.
      eapply weqcomp (* paths over ∑ f, ish_linear f *).
      1: apply (weqonpathsincl pr1), isinclpr1; intro; apply propproperty.
      (* paths over cross_mor θ n m *)
      apply (weqonpathsincl (λ f, f♭)), isinclweq; intro; apply isweq_cross_mor_negative.
    }
    split.
    - intros Hnegative_eq n m f.
      apply (iscontrweqb (Hweq n m f)).
      apply Hnegative_eq.
      induction f as [f Hf0], f as [f Hf]; cbn; clear Hf0.
      apply (is_linear_from_upshift_iff_envelope_counit_precompose θ
               (a:=(envelope_upshift θ (envelope_ob_of_negative _ n)))
               f).
      exact Hf.
    - intros Hff n m f Hf.
      apply (is_linear_from_upshift_iff_envelope_counit_precompose θ
               (a:=(envelope_upshift θ (envelope_ob_of_negative _ n)))
               (b:=envelope_ob_of_negative _ m)
               (make_cross_mor_negative' θ f))
        in Hf.
      apply (iscontrweqf (Hweq n m (((make_cross_mor_negative' θ f),,Hf),,tt))).
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
    : is_negative_equalizing
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
    : is_positive_equalizing <-> fully_faithful (positive_category_to_envelope_duploid θ).
  Proof.
    assert (Hweq : ∏ p q (f : positive_category_to_envelope_duploid θ p --> positive_category_to_envelope_duploid θ q),
             hfiber # (positive_category_to_envelope_duploid θ) f ≃ (∑ f' : P ⟦ p, q ⟧, f' · η q = (pr11 f) ♯)). {
      intros p q f.
      apply (weqtotal2 (idweq _)); intro f'.
      eapply weqcomp (* paths over ∑ _, tt *).
      1: apply (weqonpathsincl pr1), isinclpr1; intro; apply isapropifcontr, iscontrunit.
      eapply weqcomp (* paths over ∑ f, ish_thunkable f *).
      1: apply (weqonpathsincl pr1), isinclpr1; intro; apply propproperty.
      (* paths over cross_mor θ p q *)
      apply (weqonpathsincl (λ f, f♯)), isinclweq; intro; apply isweq_cross_mor_positive.
    }
    split.
    - intros Hpositive_eq p q f.
      apply (iscontrweqb (Hweq p q f)).
      apply Hpositive_eq.
      induction f as [f Hf0], f as [f Hf]; cbn; clear Hf0.
      apply (is_thunkable_from_downshift_iff_envelope_unit_postcompose θ
               (b:=(envelope_downshift θ (envelope_ob_of_positive _ q)))
               f).
      exact Hf.
    - intros Hff p q f Hf.
      apply (is_thunkable_from_downshift_iff_envelope_unit_postcompose θ
               (b:=(envelope_downshift θ (envelope_ob_of_positive _ q)))
               (a:=envelope_ob_of_positive _ p)
               (make_cross_mor_positive' θ f))
        in Hf.
      apply (iscontrweqf (Hweq p q (((make_cross_mor_positive' θ f),,Hf),,tt))).
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
    : is_positive_equalizing
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

  Hypothesis (Hnegative_eq : is_negative_equalizing).
  Hypothesis (Hnegative_univalent : is_univalent N).
  Hypothesis (Hpositive_eq : is_positive_equalizing).
  Hypothesis (Hpositive_univalent : is_univalent P).

  Definition lt_iso_of_positive_to_positive_iso (a b : envelope_duploid θ)
    (H : lt_iso a b)
    (Ha : is_positive a)
    : z_iso
        (envelope_positive_ob _ (a : envelope_ob _))
        (envelope_positive_ob _ (b : envelope_ob _)).
  Proof.
    eapply make_z_iso.
    unshelve apply (fully_faithful_reflects_iso_proof _ _ _
                      (pr1 fully_faithful_positive_category_to_envelope_duploid_iff Hpositive_eq)).
    enough (α : lt_iso (⇓a) (⇓b)). {
      use make_z_iso.
      - exact (make_thunkable_mor (lt_iso_mor α) (lt_iso_is_linear_and_thunkable α),,tt).
      - exact (make_thunkable_mor (lt_iso_inverse α) (lt_iso_inverse α),,tt).
      - split; do 2 apply carrier_eq; apply lt_iso_is_inverse.
    }
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
    eapply make_z_iso.
    unshelve apply (fully_faithful_reflects_iso_proof _ _ _
                      (pr1 fully_faithful_negative_category_to_envelope_duploid_iff Hnegative_eq)).
    enough (α : lt_iso (⇑a) (⇑b)). {
      use make_z_iso.
      - exact (make_linear_mor (lt_iso_mor α) (lt_iso_is_linear_and_thunkable α),,tt).
      - exact (make_linear_mor (lt_iso_inverse α) (lt_iso_inverse α),,tt).
      - split; do 2 apply carrier_eq; apply lt_iso_is_inverse.
    }
    refine (lt_iso_compose _ (lt_iso_compose H _)).
    - apply lt_iso_upshift_of_negative, Ha.
    - apply lt_iso_inv, lt_iso_upshift_of_negative, (is_negative_of_lt_iso H), Ha.
  Defined.

  Lemma envelope_chosen_positive_of_is_positive (a : envelope_duploid θ)
    (Hp : is_positive a) : envelope_chosen_positive θ (a : envelope_ob θ).
  Proof.
    set (a' := a : envelope_ob _).
    generalize (a' : envelope_polarization θ a').
    apply (envelope_polarization_rec' θ (a:=a')).
    1: intro; apply isaprop_is_z_isomorphism.
    2: easy.
    intro Hn.
    assert (Hε : #(R ∙ L) (ε (envelope_negative_ob _ a'))
                 = (ε ((R ∙ L) (envelope_negative_ob _ a')))). {
      apply (is_positive_envelope_upshift_iff_pre_fixed_point θ a').
      refine (is_positive_of_lt_iso _ Hp).
      apply lt_iso_inv, (lt_iso_upshift_of_negative a).
      apply is_negative_of_envelope_chosen_negative, Hn.
    }
    set (Hε' := Hnegative_eq (envelope_negative_ob _ a') _ (identity _)
                  (maponpaths (λ f, f · identity _) Hε)).
    exists (pr1 (iscontrpr1 Hε') · #L (is_z_isomorphism_mor Hn)).
    split; cbn.
    - use (cancel_z_iso _ _ (make_z_iso' (#L (envelope_cross_mor _ a')♯) _) _).
      1: apply functor_on_is_z_isomorphism, Hn.
      cbn; rewrite id_left, !assoc'.
      rewrite <- functor_comp, (is_inverse_in_precat2 Hn).
      rewrite functor_id, id_right.
      rewrite <- (id_right (#L _)).
      apply (Injectivity _ (isInjective_φ_adj θ)).
      rewrite φ_adj_natural_precomp, φ_adj_natural_postcomp.
      rewrite cross_mor_eq_negative, φ_adj_identity.
      apply cancel_precomposition.
      admit.
    - rewrite <- cross_mor_eq_positive.
      etrans; [apply cancel_precomposition, maponpaths, pathsinv0, id_right|].
      cbn; rewrite φ_adj_inv_natural_precomp.
      etrans; [
          rewrite assoc; apply cancel_postcomposition;
          rewrite assoc'; apply cancel_precomposition;
          rewrite <- functor_comp, (is_inverse_in_precat2 Hn);
          apply functor_id|].
      rewrite id_right.
      admit.
  Abort.

End equalized.

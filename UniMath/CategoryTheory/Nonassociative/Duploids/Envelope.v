(********************************************************************************

 The Single-Sorted Duploid arising from an Adjunction

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition of the envelope duploid
 2. Weak equivalence with the oblique duploid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Oblique.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.TwoSorted.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

Section envelope_defs.

  (** ** 1. Definition of the envelope duploid *)

  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let HFG : are_adjoints L R := θ.
  Let η : functor_identity P ⟹ L ∙ R := unit_from_are_adjoints HFG.
  Let ε : R ∙ L ⟹ functor_identity N := counit_from_are_adjoints HFG.

  (** A pre-object of the envelope. *)
  Definition envelope_preob := ∑ (p : P) (n : N), N⟦L p, n⟧.
  Definition make_envelope_preob
    (p : P) (n : N) (cross : N⟦L p, n⟧)
    : envelope_preob := p,,n,,cross.

  Definition envelope_negative_ob (a : envelope_preob) : N := pr12 a.
  Definition envelope_positive_ob (a : envelope_preob) : P := pr1 a.

  Local Notation "a '⁻'" := (envelope_negative_ob a) : duploid.
  Local Notation "a '⁺'" := (envelope_positive_ob a) : duploid.

  Definition envelope_mor (a b : envelope_preob) : UU := N⟦L a⁺, b⁻⟧.
  Definition envelope_mor' (a b : envelope_preob) : UU := P⟦a⁺, R b⁻⟧.
  Definition envelope_cross_mor (a : envelope_preob) : envelope_mor a a := pr22 a.
  Local Notation "a '►'" := (envelope_cross_mor a) : duploid.
    (* type in Emacs with agda-input using \t *)

  Definition envelope_mor_to_' {a b : envelope_preob} (f : envelope_mor a b)
    : envelope_mor' a b := φ_adj HFG f.
  Local Notation "a '♯'" := (envelope_mor_to_' a) : duploid.

  Definition envelope_mor_from_' {a b : envelope_preob} (f : envelope_mor' a b)
    : envelope_mor a b := φ_adj_inv HFG f.
  Local Notation "a '♭'" := (envelope_mor_from_' a) : duploid.

  Definition envelope_cross_mor' (a : envelope_preob) : envelope_mor' a a := a►♯.
  Local Notation "a '▻'" := (envelope_cross_mor' a) : duploid.
    (* type in Emacs with agda-input using \t *)

  Arguments envelope_mor / _ _.
  Arguments envelope_mor' / _ _.
  Arguments envelope_mor_to_' / _.
  Arguments envelope_mor_from_' / _.
  (* Arguments envelope_cross_mor / _.
     Arguments envelope_cross_mor' / _. *)

  (** Setting the arguments as above makes them unfold immediately *)
  Goal ∏ {a b : envelope_preob} (f : envelope_mor a b), f♯♭ = f.
    intros; cbn.
    apply φ_adj_inv_after_φ_adj.
  Qed.

  Definition envelope_chosen_negative (a : envelope_preob) : UU := is_z_isomorphism a▻.
  Identity Coercion Id_envelope_chosen_negative : envelope_chosen_negative >-> is_z_isomorphism.
  Definition envelope_chosen_positive (a : envelope_preob) : UU := is_z_isomorphism a►.
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
    : a⁻ --> b⁻ := (is_z_isomorphism_mor positive · f).

  Local Notation "f '#⊖'" := (envelope_mor_factor_chosen_negative f).
  Local Notation "f '#⊕'" := (envelope_mor_factor_chosen_positive f).

  Lemma envelope_mor_factor_chosen_negative_eq {a b : envelope_preob}
    (f : envelope_mor a b) (negative : envelope_chosen_negative b)
    : f#⊖negative · b▻ = f♯.
  Proof.
    refine (assoc' _ _ _ @ _ @ id_right _).
    apply cancel_precomposition, (is_inverse_in_precat2 negative).
  Qed.

  Lemma envelope_mor_factor_chosen_positive_eq {a b : envelope_preob}
    (f : envelope_mor a b) (positive : envelope_chosen_positive a)
    : a► · f#⊕positive = f.
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
    - exact (f#⊖Hn · g♯)♭.
    - exact (f · g#⊕Hp).
  Defined.

  Local Lemma isInjective_φ_adj {a b} : isInjective (φ_adj (A:=a) (B:=b) HFG).
  Proof. apply isweqonpathsincl, isinclweq, adjunction_hom_weq. Qed.
  Local Lemma isInjective_φ_adj_inv {a b} : isInjective (φ_adj_inv (A:=a) (B:=b) HFG).
  Proof. apply isweqonpathsincl, isinclweq, (invweq (adjunction_hom_weq _ _ _)). Qed.

  Ltac cancel_φ_adj := apply (Injectivity (φ_adj HFG) isInjective_φ_adj).
  Ltac cancel_φ_adj_inv := apply (Injectivity (φ_adj_inv HFG) isInjective_φ_adj_inv).

  Definition envelope_compose_id_left {a b : envelope_preob}
    (f : envelope_mor a b)
    (choice : envelope_polarization_choice a)
    : envelope_compose' (a►) f choice = f.
  Proof.
    induction choice as [Hn | Hp]; cbn.
    - cancel_φ_adj; rewrite φ_adj_after_φ_adj_inv.
      etrans; [apply cancel_postcomposition, (is_inverse_in_precat1 Hn)|].
      apply id_left.
    - apply envelope_mor_factor_chosen_positive_eq.
  Qed.

  Definition envelope_compose_id_right {a b : envelope_preob}
    (f : envelope_mor a b)
    (choice : envelope_polarization_choice b)
    : envelope_compose' f (b►) choice = f.
  Proof.
    induction choice as [Hn | Hp]; cbn.
    - cancel_φ_adj; rewrite φ_adj_after_φ_adj_inv.
      apply envelope_mor_factor_chosen_negative_eq.
    - etrans; [apply cancel_precomposition, (is_inverse_in_precat2 Hp)|].
      apply id_right.
  Qed.

  (** However, if both choices exist, then it does not matter which we choose. *)
  Lemma envelope_chosen_negative_and_positive_eq (a : envelope_preob)
    (negative : envelope_chosen_negative a)
    (positive : envelope_chosen_positive a)
    : # R (is_z_isomorphism_mor positive) = φ_adj HFG (# L (is_z_isomorphism_mor negative)).
  Proof.
    apply (pre_comp_with_z_iso_is_inj' negative).
    cancel_φ_adj_inv.
    intermediate_path (identity (L a ⁺)).
    - rewrite φ_adj_inv_natural_postcomp.
      etrans; [apply cancel_postcomposition, φ_adj_inv_after_φ_adj|].
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
    cbn.
    unfold envelope_mor_factor_chosen_negative, envelope_mor_factor_chosen_positive.
    rewrite φ_adj_inv_natural_precomp, φ_adj_inv_after_φ_adj, assoc.
    apply cancel_postcomposition.
    cancel_φ_adj.
    rewrite functor_comp, φ_adj_natural_precomp, φ_adj_natural_postcomp.
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
    - abstract (apply homset_property).
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
    1: intro; apply homset_property.
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
    - exact (identity (L p)).
  Defined.

  Definition envelope_preob_of_negative (n : N) : envelope_preob.
  Proof.
    use make_envelope_preob.
    - exact (R n).
    - exact n.
    - exact (φ_adj_inv HFG (identity (R n))).
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
    abstract (
        cbn; unfold envelope_cross_mor'; cbn;
        rewrite φ_adj_after_φ_adj_inv; apply is_z_isomorphism_identity).
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
      (apply envelope_compose_rec'; [intro; apply homset_property | |]).
    1, 2: intro; apply envelope_compose_id_left.
    1, 2: intro; apply envelope_compose_id_right.
  Qed.

  Definition envelope_unital_premagmoid : unital_premagmoid
    := make_unital_premagmoid _ envelope_is_unital_premagmoid.

  Definition envelope_unital_magmoid : unital_magmoid.
  Proof.
    use (make_unital_magmoid envelope_unital_premagmoid).
    abstract (intros a b; apply homset_property).
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
    - intro; apply homset_property.
    - intro Hn; cbn; cancel_φ_adj.
      rewrite !φ_adj_natural_postcomp, !φ_adj_after_φ_adj_inv.
      now rewrite assoc.
    - intro Hp; cbn.
      unfold envelope_mor_factor_chosen_negative,
        envelope_mor_factor_chosen_positive.
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
    - intro; apply homset_property.
    - intro Hn; cbn.
      unfold envelope_mor_factor_chosen_negative,
        envelope_mor_factor_chosen_positive; cbn.
      do 2 rewrite φ_adj_after_φ_adj_inv.
      now rewrite !assoc.
    - intro Hp; cbn.
      rewrite φ_adj_natural_postcomp, assoc.
      now rewrite φ_adj_inv_natural_postcomp.
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

  Definition oblique_to_envelope_ob (a : oblique_duploid θ) : envelope_preduploid.
  Proof.
    induction a as [n | p].
    - apply envelope_ob_of_negative, n.
    - apply envelope_ob_of_positive, p.
  Defined.

  Definition oblique_to_envelope_mor {a b : oblique_duploid θ} (f : a --> b)
    : oblique_to_envelope_ob a --> oblique_to_envelope_ob b.
  Proof. induction a, b; exact f. Defined.

  Definition envelope_downshift (a : envelope_preob) : envelope_ob
    := envelope_ob_of_positive (a⁺).
  Definition envelope_upshift (a : envelope_preob)
    : envelope_ob := envelope_ob_of_negative (a⁻).

  Definition envelope_force
    (a : envelope_preob) : envelope_mor (envelope_upshift a) a.
  Proof. exact (φ_adj_inv HFG (identity (R a⁻))). Defined.
  Definition envelope_delay
    (a : envelope_preob) : envelope_mor a (envelope_upshift a).
  Proof. exact (a►). Defined.

  Definition envelope_wrap
    (a : envelope_preob) : envelope_mor a (envelope_downshift a).
  Proof. exact (identity (L a⁺)). Defined.
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
    unfold envelope_mor_factor_chosen_negative, envelope_mor_factor_chosen_positive, envelope_force; cbn.
    rewrite !φ_adj_after_φ_adj_inv, !id_right.
    now rewrite !φ_adj_inv_after_φ_adj.
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
    unfold envelope_mor_factor_chosen_negative, envelope_mor_factor_chosen_positive, envelope_delay; cbn.
    change (φ_adj HFG a►) with a▻.
    rewrite !assoc', !(is_inverse_in_precat2 Hn), !id_right.
    now rewrite !φ_adj_inv_after_φ_adj.
  Qed.

  Lemma is_inverse_in_precat_envelope_force_delay (a : envelope_ob)
    : is_inverse_in_precat (C:=envelope_preduploid) (envelope_force a) (envelope_delay a).
  Proof.
    split; cbn.
    - envelope_induction' a.
      1: intro; apply homset_property.
      + intro Hn; cbn.
        unfold envelope_mor_factor_chosen_negative, envelope_mor_factor_chosen_positive,
          envelope_delay, envelope_force; cbn.
        cancel_φ_adj; rewrite !φ_adj_after_φ_adj_inv, !id_left.
        apply (is_inverse_in_precat2 Hn).
      + intro Hp; cbn.
        unfold envelope_mor_factor_chosen_positive,envelope_delay; cbn.
        now rewrite (is_inverse_in_precat2 Hp), id_right.
    - unfold envelope_mor_factor_chosen_positive,envelope_delay; cbn.
      unfold envelope_mor_factor_chosen_negative, envelope_force; cbn.
      cancel_φ_adj; rewrite !φ_adj_after_φ_adj_inv.
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
    unfold envelope_mor_factor_chosen_positive, envelope_mor_factor_chosen_negative, envelope_wrap; cbn.
    now rewrite !id_left.
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
    unfold envelope_mor_factor_chosen_positive, envelope_mor_factor_chosen_negative, envelope_unwrap; cbn.
    now rewrite !assoc, !(is_inverse_in_precat1 Hp), !id_left.
  Qed.

  Lemma is_inverse_in_precat_envelope_unwrap_wrap (a : envelope_ob)
    : is_inverse_in_precat (C:=envelope_preduploid) (envelope_wrap a) (envelope_unwrap a).
  Proof.
    split; cbn.
    - unfold envelope_mor_factor_chosen_negative, envelope_unwrap; cbn.
      unfold envelope_mor_factor_chosen_positive, envelope_wrap; cbn.
      now rewrite !id_left.
    - envelope_induction' a.
      1: intro; apply homset_property.
      + intro Hn; cbn.
        unfold envelope_mor_factor_chosen_positive, envelope_mor_factor_chosen_negative,
          envelope_unwrap, envelope_wrap; cbn.
        change (φ_adj HFG a►) with a▻.
        rewrite (is_inverse_in_precat1 Hn), id_left.
        apply φ_adj_inv_after_φ_adj.
      + intro Hp; cbn.
        unfold envelope_mor_factor_chosen_negative, envelope_unwrap; cbn.
        unfold envelope_mor_factor_chosen_positive, envelope_wrap; cbn.
        now rewrite id_right, (is_inverse_in_precat1 Hp).
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

  Definition oblique_to_envelope_data : functor_data (oblique_duploid θ) envelope_duploid.
  Proof.
    use make_functor_data.
    - exact oblique_to_envelope_ob.
    - exact @oblique_to_envelope_mor.
  Defined.

  Definition is_functor_oblique_to_envelope : is_functor oblique_to_envelope_data.
  Proof.
    use make_is_functor.
    - intro a; now induction a.
    - intros a b c g f.
      induction a as [n | p], b as [m | q], c as [o | r]; cbn;
        unfold envelope_mor_factor_chosen_negative,
        envelope_mor_factor_chosen_positive; cbn;
        first [rewrite id_right | rewrite id_left];
        reflexivity.
  Qed.

  Definition oblique_to_envelope : functor (oblique_duploid θ) envelope_duploid
    := make_functor _ is_functor_oblique_to_envelope.

  Lemma fully_faithful_oblique_to_envelope : fully_faithful oblique_to_envelope.
  Proof.
    intros a b.
    use isweq_iso.
    1: intro f; induction a, b; exact f.
    all: abstract (intro f; now induction a, b).
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
    exists (force b).
    refine (is_lt_iso_delay_of_negative b _).
    abstract (apply is_negative_of_envelope_chosen_negative, Hn).
  Defined.

  Lemma oblique_to_envelope_inverse_of_chosen_positive
    (b : envelope_duploid) (Hn : envelope_chosen_positive (b : envelope_ob))
    : ∑ (a : oblique_duploid θ), lt_iso (oblique_to_envelope a) b.
  Proof.
    exists (oblique_positive θ ((b : envelope_ob) ⁺)).
    apply lt_iso_inv.
    exists (wrap b).
    refine (is_lt_iso_unwrap_of_positive b _).
    abstract (apply is_positive_of_envelope_chosen_positive, Hn).
  Defined.

  Lemma lt_essentially_surjective_oblique_to_envelope : lt_essentially_surjective oblique_to_envelope.
  Proof.
    intro a; envelope_induction' a.
    1: intro; apply isapropishinh.
    - intro Hn; apply hinhpr, oblique_to_envelope_inverse_of_chosen_negative, Hn.
    - intro Hp; apply hinhpr, oblique_to_envelope_inverse_of_chosen_positive, Hp.
  Qed.

  Lemma lt_split_essentially_surjective_oblique_to_envelope_from_LEM
    : LEM -> lt_essentially_surjective oblique_to_envelope.
  Proof.
    intros lem a.
    set (Hlemn := lem (make_hProp (envelope_chosen_negative (a : envelope_ob)) (isaprop_is_z_isomorphism _))).
    induction Hlemn as [Hn | Hnotn].
    - apply hinhpr, oblique_to_envelope_inverse_of_chosen_negative, Hn.
    - assert (Hp : envelope_chosen_positive (a : envelope_ob)). {
        envelope_induction' a; intro.
        apply isaprop_is_z_isomorphism.
        all: easy.
      }
      apply hinhpr, oblique_to_envelope_inverse_of_chosen_positive, Hp.
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

End envelope_defs.

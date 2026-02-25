(********************************************************************************

 The Equalizing Requirement for an Adjunction

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition and proofs of oblique morphisms
 2. Definition of the equalizing requirement
 3. The shift adjunction of a duploid is fully equalizing

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.RXGraph.

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
Require Import UniMath.CategoryTheory.SplitMonicsAndEpis.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.EpisAndMonics.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.ShiftFunctors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.ShiftFacts.

Local Open Scope cat.
Local Open Scope unital_magmoid.

Declare Scope oblique_mor.
Delimit Scope oblique_mor with oblique_mor.
Local Open Scope oblique_mor.

(** ** 1. Definition and proofs of oblique morphisms

 Given an adjunction [θ : L ⊣ R] between [L : P ⟶ N] and [R : N ⟶ P], the
 oblique morphisms [f : oblique_mor θ (p : P) (n : N)] are pairs of morphisms
 [f♭ : N⟦L p, n⟧] and [f♯ : P⟦p, R n⟧] such that [f♯] is the transpose of [f♭]
 (via [φ_adj θ]).

 *)

Section oblique_mor_defs.
  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.

  (** Definition of the oblique morphism *)
  Definition oblique_mor (p : P) (n : N) : UU
    := ∑ (f : N⟦L p, n⟧) (g : P⟦p, R n⟧), φ_adj θ f = g.

  Definition oblique_mor_negative {p : P} {n : N} (f : oblique_mor p n) : N⟦L p, n⟧
    := pr1 f.
  Definition oblique_mor_positive {p : P} {n : N} (f : oblique_mor p n) : P⟦p, R n⟧
    := pr12 f.

  Local Notation "f '♭'" := (oblique_mor_negative f) : oblique_mor.
  Local Notation "f '♯'" := (oblique_mor_positive f) : oblique_mor.

  Definition oblique_mor_negative_transpose {p : P} {n : N} (f : oblique_mor p n)
    : φ_adj θ f♭ = f♯ := pr22 f.
  Definition oblique_mor_positive_transpose {p : P} {n : N} (f : oblique_mor p n)
    : φ_adj_inv θ f♯ = f♭.
  Proof.
    intermediate_path (φ_adj_inv θ (φ_adj θ f♭)).
    - apply maponpaths, pathsinv0, oblique_mor_negative_transpose.
    - apply φ_adj_inv_after_φ_adj.
  Qed.

  Definition make_oblique_mor_negative {p : P} {n : N}
    (f : N⟦L p, n⟧) (g : P⟦p, R n⟧) (H : φ_adj θ f = g)
    : oblique_mor p n := f,,g,,H.
  Definition make_oblique_mor_positive {p : P} {n : N}
    (f : N⟦L p, n⟧) (g : P⟦p, R n⟧) (H : φ_adj_inv θ g = f)
    : oblique_mor p n.
  Proof.
    apply (make_oblique_mor_negative f g).
    abstract (apply (maponpaths (φ_adj θ)) in H;
              refine (!H @ _);
              apply φ_adj_after_φ_adj_inv).
  Defined.

  Definition oblique_mor_from_negative {p : P} {n : N}
    (f : N⟦L p, n⟧) : oblique_mor p n
    := make_oblique_mor_negative f _ (idpath _).
  Definition oblique_mor_from_positive {p : P} {n : N}
    (g : P⟦p, R n⟧) : oblique_mor p n
    := make_oblique_mor_positive _ g (idpath _).

  Lemma isaset_oblique_mor {p n} : isaset (oblique_mor p n).
  Proof.
    apply isaset_total2.
    1: apply homset_property.
    intro f.
    apply isaset_total2.
    1: apply homset_property.
    intro g.
    apply isasetaprop, homset_property.
  Qed.

  Definition oblique_mor_negative_path {p : P} {n : N}
    (f g : oblique_mor p n) (H : f♭ = g♭) : f = g.
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

  Lemma isweq_oblique_mor_negative (p : P) (n : N) : isweq (@oblique_mor_negative p n).
  Proof.
    use isweq_iso.
    - exact oblique_mor_from_negative.
    - intro f; now apply oblique_mor_negative_path.
    - easy.
  Defined.

  Lemma isweq_oblique_mor_from_negative (p : P) (n : N) : isweq (@oblique_mor_from_negative p n).
  Proof.
    exact (weqproperty (invweq (make_weq _ (isweq_oblique_mor_negative p n)))).
  Defined.

  Definition oblique_mor_negative_path_weq {p : P} {n : N}
    (f g : oblique_mor p n) : f = g ≃ f♭ = g♭.
  Proof.
    apply weqonpathsincl, isinclweq, isweq_oblique_mor_negative.
  Defined.

  Definition oblique_mor_positive_path {p : P} {n : N}
    (f g : oblique_mor p n) (H : f♯ = g♯) : f = g.
  Proof.
    set (Hf := oblique_mor_positive_transpose f).
    set (Hg := oblique_mor_positive_transpose g).
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

  Lemma isweq_oblique_mor_positive (p : P) (n : N) : isweq (@oblique_mor_positive p n).
  Proof.
    use isweq_iso.
    - exact oblique_mor_from_positive.
    - intro f; now apply oblique_mor_positive_path.
    - easy.
  Defined.

  Lemma isweq_oblique_mor_from_positive (p : P) (n : N) : isweq (@oblique_mor_from_positive p n).
  Proof.
    exact (weqproperty (invweq (make_weq _ (isweq_oblique_mor_positive p n)))).
  Defined.

  Definition oblique_mor_positive_path_weq {p : P} {n : N}
    (f g : oblique_mor p n) : f = g ≃ f♯ = g♯.
  Proof.
    apply weqonpathsincl, isinclweq, isweq_oblique_mor_positive.
  Defined.

  (** Constructors and compositions *)
  Lemma φ_adj_inv_identity (n : N)
    : φ_adj_inv θ (identity (R n)) = ε n.
  Proof.
    unfold φ_adj_inv.
    etrans; [apply cancel_postcomposition, functor_id|].
    apply id_left.
  Qed.

  Definition oblique_is_negative_iso {p : P} {n : N} (f : oblique_mor p n) : UU := is_z_isomorphism f♭.
  Identity Coercion Id_oblique_is_negative_iso : oblique_is_negative_iso >-> is_z_isomorphism.
  Definition oblique_is_positive_iso {p : P} {n : N} (f : oblique_mor p n) : UU := is_z_isomorphism f♯.
  Identity Coercion Id_oblique_is_positive_iso : oblique_is_positive_iso >-> is_z_isomorphism.

  Lemma isaprop_oblique_is_negative_iso {p : P} {n : N} (f : oblique_mor p n)
    : isaprop (oblique_is_negative_iso f).
  Proof. apply isaprop_is_z_isomorphism. Qed.
  Lemma isaprop_oblique_is_positive_iso {p : P} {n : N} (f : oblique_mor p n)
    : isaprop (oblique_is_positive_iso f).
  Proof. apply isaprop_is_z_isomorphism. Qed.

  Definition oblique_positive_identity (p : P) : oblique_mor p (L p).
  Proof.
    use make_oblique_mor_negative.
    - exact (identity (L p)).
    - exact (η p).
    - apply φ_adj_identity.
  Defined.

  Definition oblique_positive_identity_is_negative_iso (p : P)
    : oblique_is_negative_iso (oblique_positive_identity p).
  Proof. apply is_z_isomorphism_identity. Defined.

  Definition oblique_negative_identity (n : N) : oblique_mor (R n) n.
  Proof.
    use make_oblique_mor_positive.
    - exact (ε n).
    - exact (identity (R n)).
    - apply φ_adj_inv_identity.
  Defined.

  Definition oblique_negative_identity_is_positive_iso (n : N)
    : oblique_is_positive_iso (oblique_negative_identity n).
  Proof. apply is_z_isomorphism_identity. Defined.

  (** Compose a negative morphism on the right *)
  Definition oblique_compose_negative {p : P} {n m : N}
    (f : oblique_mor p n) (g : N⟦n, m⟧) : oblique_mor p m.
  Proof.
    use make_oblique_mor_negative.
    - exact (f♭ · g).
    - exact (f♯ · #R g).
    - etrans; [apply φ_adj_natural_postcomp|].
      apply cancel_postcomposition.
      apply oblique_mor_negative_transpose.
  Defined.

  (** Compose a positive morphism on the left *)
  Definition oblique_compose_positive {p q : P} {n : N}
    (f : P⟦p, q⟧) (g : oblique_mor q n) : oblique_mor p n.
  Proof.
    use make_oblique_mor_positive.
    - exact (#L f · g♭).
    - exact (f · g♯).
    - etrans; [apply φ_adj_inv_natural_precomp|].
      apply cancel_precomposition.
      apply oblique_mor_positive_transpose.
  Defined.

  (** Embed a negative morphism *)
  Definition oblique_lift_negative {n m : N}
    (f : n --> m) : oblique_mor (R n) m.
  Proof.
    use make_oblique_mor_positive.
    - exact (ε n · f).
    - exact (#R f).
    - etrans; [apply maponpaths, pathsinv0, id_left|].
      etrans; [apply φ_adj_inv_natural_postcomp|].
      apply cancel_postcomposition.
      apply φ_adj_inv_identity.
  Defined.

  Definition oblique_lift_negative_is_positive_iso_of_iso {n m : N}
    (f : n --> m) (H : is_z_isomorphism f)
    : oblique_is_positive_iso (oblique_lift_negative f).
  Proof. apply functor_on_is_z_isomorphism, H. Defined.

  (** Embed a positive morphism *)
  Definition oblique_lift_positive {p q : P}
    (f : p --> q) : oblique_mor p (L q).
  Proof.
    use make_oblique_mor_negative.
    - exact (#L f).
    - exact (f · η q).
    - etrans; [apply maponpaths, pathsinv0, id_right|].
      etrans; [apply φ_adj_natural_precomp|].
      apply cancel_precomposition.
      apply φ_adj_identity.
  Defined.

  Definition oblique_lift_positive_is_negative_iso_of_iso {p q : P}
    (f : p --> q) (H : is_z_isomorphism f)
    : oblique_is_negative_iso (oblique_lift_positive f).
  Proof. apply functor_on_is_z_isomorphism, H. Defined.

  (** Characterizations of polarities of oblique morphisms *)

  Definition is_negative_oblique_mor_linear
    {n m : N} (f : oblique_mor (R n) m) : UU
    := #(R ∙ L) (ε n) · f♭ = ε ((R ∙ L) n) · f♭.
  Lemma isaprop_is_negative_oblique_mor_linear
    {n m : N} (f : oblique_mor (R n) m)
    : isaprop (is_negative_oblique_mor_linear f).
  Proof. apply homset_property. Qed.

  Definition is_positive_oblique_mor_thunkable
    {p q : P} (f : oblique_mor p (L q)) : UU
    := f♯ · #(L ∙ R) (η q) = f♯ · η ((L ∙ R) q).
  Lemma isaprop_is_positive_oblique_mor_thunkable
    {p q : P} (f : oblique_mor p (L q))
    : isaprop (is_positive_oblique_mor_thunkable f).
  Proof. apply homset_property. Qed.

End oblique_mor_defs.

Notation "f '♭'" := (oblique_mor_negative _ f) : oblique_mor.
Notation "f '♯'" := (oblique_mor_positive _ f) : oblique_mor.

(** ** 2. Definition of the equalizing requirement *)

Section equalized.
  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.

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

  Definition is_fully_equalizing : UU
    := is_negative_equalizing × is_positive_equalizing.
  Definition make_is_fully_equalizing
    (Hnegative : is_negative_equalizing)
    (Hpositive : is_positive_equalizing)
    : is_fully_equalizing := Hnegative,,Hpositive.
  Coercion is_fully_equalizing_to_is_negative_equalizing
    (H : is_fully_equalizing) : is_negative_equalizing := pr1 H.
  Coercion is_fully_equalizing_to_is_positive_equalizing
    (H : is_fully_equalizing) : is_positive_equalizing := pr2 H.

  (** Characterizations of the equalizing requirements *)
  Lemma is_negative_equalizing_from_is_epi_and_equation
    (Hepi : ∏ (n : N), is_epi (ε n))
    (Himage : ∏ (n m : N) (f : oblique_mor θ (R n) m) (H : is_negative_oblique_mor_linear θ f),
        ishinh (hfiber (λ g, ε n · g) f♭))
    : is_negative_equalizing.
  Proof.
    intros a b f Hf.
    isaprop_goal Hprop; [apply isapropiscontr|].
    refine (squash_to_prop (Himage _ _ (oblique_mor_from_negative θ f) Hf) Hprop (λ Hfib, _)).
    induction Hfib as [g Hg].
    use (unique_exists g).
    - exact Hg.
    - intro; apply homset_property.
    - intros g' Hg'; cbn in Hg'.
      apply Hepi.
      exact (Hg' @ !Hg).
  Qed.

  Lemma is_negative_equalizing_from_is_epi_and_linear_image
    (Hepi : ∏ (n : N), is_epi (ε n))
    (Himage : ∏ (n m : N) (f : oblique_mor θ (R n) m) (H : is_negative_oblique_mor_linear θ f),
        ishinh (hfiber (#R) f♯))
    : is_negative_equalizing.
  Proof.
    apply (is_negative_equalizing_from_is_epi_and_equation Hepi).
    intros a b f Hf.
    isaprop_goal Hprop; [apply propproperty|].
    refine (squash_to_prop (Himage _ _ f Hf) Hprop (λ Hfib, _)).
    induction Hfib as [g Hg].
    apply hinhpr; exists g.
    change ((oblique_lift_negative θ g)♭ = f♭).
    apply (maponpaths (oblique_mor_negative θ)), oblique_mor_positive_path.
    exact Hg.
  Defined.

  Lemma is_positive_equalizing_from_is_monic_and_equation
    (Hmonic : ∏ (p : P), is_monic (η p))
    (Himage : ∏ (p q : P) (f : oblique_mor θ p (L q)) (H : is_positive_oblique_mor_thunkable θ f),
        ishinh (hfiber (λ g, g · η q) f♯))
    : is_positive_equalizing.
  Proof.
    intros a b f Hf.
    isaprop_goal Hprop; [apply isapropiscontr|].
    refine (squash_to_prop (Himage _ _ (oblique_mor_from_positive θ f) Hf) Hprop (λ Hfib, _)).
    induction Hfib as [g Hg].
    use (unique_exists g).
    - exact Hg.
    - intro; apply homset_property.
    - intros g' Hg'; cbn in Hg'.
      apply Hmonic.
      exact (Hg' @ !Hg).
  Qed.

  Lemma is_positive_equalizing_from_is_monic_and_thunkable_image
    (Hmonic : ∏ (p : P), is_monic (η p))
    (Himage : ∏ (p q : P) (f : oblique_mor θ p (L q)) (H : is_positive_oblique_mor_thunkable θ f),
        ishinh (hfiber (#L) f♭))
    : is_positive_equalizing.
  Proof.
    apply (is_positive_equalizing_from_is_monic_and_equation Hmonic).
    intros a b f Hf.
    isaprop_goal Hprop; [apply propproperty|].
    refine (squash_to_prop (Himage _ _ f Hf) Hprop (λ Hfib, _)).
    induction Hfib as [g Hg].
    apply hinhpr; exists g.
    change ((oblique_lift_positive θ g)♯ = f♯).
    apply (maponpaths (oblique_mor_positive θ)), oblique_mor_negative_path.
    exact Hg.
  Qed.

  (** Lemmas about the negative fixed point of the adjunction *)
  Section negative_fixed_point.
    Definition is_negative_pre_fixed_point (n : N) : UU
      := #(R ∙ L) (ε n) = ε ((R ∙ L) n).
    Lemma isaprop_is_negative_pre_fixed_point (n : N)
      : isaprop (is_negative_pre_fixed_point n).
    Proof. apply homset_property. Qed.

    Definition is_negative_fixed_point (n : N) : UU
      := is_z_isomorphism (ε n).
    Identity Coercion Id_is_negative_fixed_point : is_negative_fixed_point >-> is_z_isomorphism.
    Lemma isaprop_is_negative_fixed_point (n : N)
      : isaprop (is_negative_fixed_point n).
    Proof. apply isaprop_is_z_isomorphism. Qed.

    Lemma is_epi_counit_from_negative_equalizing
      (Hnegative_eq : is_negative_equalizing) (n : N)
      : is_epi (ε n).
    Proof.
      intros b f g H.
      apply (base_paths (B:=λ f', ε n · f' = ε n · g) (f,,H) (g,,idpath _)).
      eassert (H' : ∃! f' : N⟦n, b⟧, ε n · f' = ε n · g). {
        refine (Hnegative_eq _ _ (ε n · g) _).
        now rewrite !assoc, nat_trans_ax.
      }
      intermediate_path (iscontrpr1 H').
      - apply iscontr_uniqueness.
      - apply pathsinv0, iscontr_uniqueness.
    Qed.

    Lemma is_negative_fixed_point_from_pre_fixed_point
      (Hnegative_eq : is_negative_equalizing)
      (n : N) (Hn : is_negative_pre_fixed_point n)
      : is_negative_fixed_point n.
    Proof.
      eassert (f' : ∃! f' : N⟦n, (R ∙ L) n⟧, ε n · f' = identity ((R ∙ L) n)). {
        apply Hnegative_eq.
        abstract (rewrite !id_right; exact Hn).
      }
      induction f' as [f' _], f' as [f' Hf'].
      use make_is_z_isomorphism; [|use make_is_inverse_in_precat].
      - exact f'.
      - exact Hf'.
      - abstract (apply (is_epi_counit_from_negative_equalizing Hnegative_eq);
                  now rewrite assoc, Hf', id_left, id_right).
    Defined.

    Lemma is_negative_fixed_point_to_pre_fixed_point
      (n : N) (Hn : is_negative_fixed_point n)
      : is_negative_pre_fixed_point n.
    Proof.
      refine (pre_comp_with_z_iso_is_inj
                (_ : is_z_isomorphism (#(R ∙ L) (is_z_isomorphism_mor Hn)))
                _ _ _).
      1: apply functor_on_is_z_isomorphism, is_z_isomorphism_inv.
      intermediate_path (identity ((R ∙ L) n)).
      - rewrite <- functor_comp, <- functor_id.
        apply (maponpaths (#(R ∙ L))).
        apply (is_inverse_in_precat2 Hn).
      - apply pathsinv0.
        refine (nat_trans_ax ε n _ _ @ _).
        apply (is_inverse_in_precat1 Hn).
    Qed.

    Lemma is_negative_fixed_point_iff_pre_fixed_point
      (Hnegative_eq : is_negative_equalizing) (n : N)
      : is_negative_fixed_point n <-> is_negative_pre_fixed_point n.
    Proof.
      split.
      - apply is_negative_fixed_point_to_pre_fixed_point.
      - apply (is_negative_fixed_point_from_pre_fixed_point Hnegative_eq).
    Defined.

    (** The negative equalizing requirement makes the negative pre-fixed and
        fixed points coincide *)
    Lemma is_negative_fixed_point_weq_pre_fixed_point
      (Hnegative_eq : is_negative_equalizing) (n : N)
      : is_negative_fixed_point n ≃ is_negative_pre_fixed_point n.
    Proof.
      apply weqiff.
      - exact (is_negative_fixed_point_iff_pre_fixed_point Hnegative_eq n).
      - apply isaprop_is_z_isomorphism.
      - apply homset_property.
    Defined.
  End negative_fixed_point.

  (** Lemmas about the positive fixed point of the adjunction *)
  Section positive_fixed_point.
    Definition is_positive_pre_fixed_point (p : P) : UU
      := #(L ∙ R) (η p) = η ((L ∙ R) p).
    Lemma isaprop_is_positive_pre_fixed_point (p : P)
      : isaprop (is_positive_pre_fixed_point p).
    Proof. apply homset_property. Qed.

    Definition is_positive_fixed_point (p : P) : UU
      := is_z_isomorphism (η p).
    Identity Coercion Id_is_positive_fixed_point : is_positive_fixed_point >-> is_z_isomorphism.
    Lemma isaprop_is_positive_fixed_point (p : P)
      : isaprop (is_positive_fixed_point p).
    Proof. apply isaprop_is_z_isomorphism. Qed.

    Lemma is_monic_unit_from_positive_equalizing
      (Hpositive_eq : is_positive_equalizing) (p : P)
      : is_monic (η p).
    Proof.
      intros b f g H.
      apply (base_paths (B:=λ f', f' · η p = g · η p) (f,,H) (g,,idpath _)).
      eassert (H' : ∃! f' : P⟦b, p⟧, f' · η p = g · η p). {
        refine (Hpositive_eq _ _ (g · η p) _).
        now rewrite !assoc', (!nat_trans_ax η _ _ _).
      }
      intermediate_path (iscontrpr1 H').
      - apply iscontr_uniqueness.
      - apply pathsinv0, iscontr_uniqueness.
    Qed.

    Lemma is_positive_fixed_point_from_pre_fixed_point
      (Hpositive_eq : is_positive_equalizing)
      (p : P) (Hp : is_positive_pre_fixed_point p)
      : is_positive_fixed_point p.
    Proof.
      eassert (f' : ∃! f' : P⟦(L ∙ R) p, p⟧, f' · η p = identity ((L ∙ R) p)). {
        apply Hpositive_eq.
        abstract (rewrite !id_left; exact Hp).
      }
      induction f' as [f' _], f' as [f' Hf'].
      use make_is_z_isomorphism; [|use make_is_inverse_in_precat].
      - exact f'.
      - abstract (apply (is_monic_unit_from_positive_equalizing Hpositive_eq);
                  rewrite assoc';
                  etrans; [apply cancel_precomposition, Hf'|];
                  now rewrite id_right, id_left).
      - exact Hf'.
    Defined.

    Lemma is_positive_fixed_point_to_pre_fixed_point
      (p : P) (Hp : is_positive_fixed_point p)
      : is_positive_pre_fixed_point p.
    Proof.
      refine (post_comp_with_z_iso_is_inj
                (_ : is_z_isomorphism (#(L ∙ R) (is_z_isomorphism_mor Hp)))
                _ _ _).
      1: apply functor_on_is_z_isomorphism, is_z_isomorphism_inv.
      intermediate_path (identity ((L ∙ R) p)).
      - rewrite <- functor_comp, <- functor_id.
        apply (maponpaths (#(L ∙ R))).
        apply (is_inverse_in_precat1 Hp).
      - refine (_ @ nat_trans_ax η _ p _).
        apply pathsinv0, (is_inverse_in_precat2 Hp).
    Qed.

    Lemma is_positive_fixed_point_iff_pre_fixed_point
      (Hpositive_eq : is_positive_equalizing) (p : P)
      : is_positive_fixed_point p <-> is_positive_pre_fixed_point p.
    Proof.
      split.
      - apply is_positive_fixed_point_to_pre_fixed_point.
      - apply (is_positive_fixed_point_from_pre_fixed_point Hpositive_eq).
    Defined.

    (** The positive equalizing requirement makes the positive pre-fixed and
        fixed points coincide *)
    Lemma is_positive_fixed_point_weq_pre_fixed_point
      (Hpositive_eq : is_positive_equalizing) (p : P)
      : is_positive_fixed_point p ≃ is_positive_pre_fixed_point p.
    Proof.
      apply weqiff.
      - exact (is_positive_fixed_point_iff_pre_fixed_point Hpositive_eq p).
      - apply isaprop_is_z_isomorphism.
      - apply homset_property.
    Defined.
  End positive_fixed_point.

End equalized.

(** ** 3. The shift adjunction of a duploid is fully equalizing *)

Section shift_is_equalizing.
  Context (D : duploid).
  Let θ := left_adjoint_to_adjunction (are_adjoints_upshift_downshift_negative_linear_to_positive_thunkable D).

  Local Open Scope duploid.

  Let ε' (a : D) : D⟦⇑(⇓a), a⟧ := force (⇓a) · unwrap a.
  Let ε_sec (a : D) : D⟦a, ⇑(⇓a)⟧ := wrap a · delay (⇓a).

  Local Lemma ε'_has_section (a : D)
    : ε_sec a · ε' a = identity a.
  Proof.
    etrans; [apply (assoc'_thunkable _ (wrap _))|].
    etrans; [apply cancel_precomposition, delay_force_left|].
    apply wrap_unwrap_id.
  Qed.

  Local Lemma ε_sec_natural (a b : D) (f : a --> b)
    : f · ε_sec b = ε_sec a · #⇑(#⇓f).
  Proof.
    subst ε_sec; cbn beta.
    etrans; [|apply (assoc_thunkable _ (wrap a))].
    etrans; [|apply cancel_precomposition, delay_natural].
    etrans; [|apply (assoc'_thunkable _ (wrap a))].
    etrans; [|apply cancel_postcomposition, wrap_natural].
    apply (assoc_linear _ (delay _)).
  Qed.

  Local Lemma is_epi_ε' (a : negative_ob D)
    : is_epi (adjcounit θ a).
  Proof.
    intros b f g Hfg.
    do 2 apply base_paths in Hfg.
    apply (maponpaths (precomp_with (ε_sec a))) in Hfg.
    change (ε_sec a · (ε' a · pr11 f) = ε_sec a · (ε' a · pr11 g)) in Hfg.
    do 2 apply carrier_eq.
    refine (_ @ Hfg @ _).
    - now rewrite (assoc_linear _ (pr21 f)), ε'_has_section, magmoid_id_left.
    - now rewrite (assoc_linear _ (pr21 g)), ε'_has_section, magmoid_id_left.
  Qed.

  Let η' (a : D) : D⟦a, ⇓(⇑a)⟧ := wrap (⇑a) ∘ delay a.
  Let η_ret (a : D) : D⟦⇓(⇑a), a⟧ := force a ∘ unwrap (⇑a).

  Local Lemma η'_has_retract (a : D)
    : η_ret a ∘ η' a = identity a.
  Proof.
    etrans; [apply (assoc_linear _ (force _))|].
    etrans; [apply cancel_postcomposition, wrap_unwrap_right|].
    apply delay_force_id.
  Qed.

  Local Lemma η_ret_natural (a b : D) (f : a <-- b)
    : f ∘ η_ret b = η_ret a ∘ #⇓(#⇑f).
  Proof.
    subst η_ret; cbn beta.
    etrans; [|apply (assoc'_linear _ (force a))].
    etrans; [|apply cancel_postcomposition, pathsinv0, unwrap_natural].
    etrans; [|apply (assoc_linear _ (force a))].
    etrans; [|apply cancel_precomposition, pathsinv0, force_natural].
    apply (assoc'_thunkable _ (unwrap _)).
  Qed.

  Local Lemma is_monic_η' (a : positive_ob D)
    : is_monic (adjunit θ a).
  Proof.
    intros b f g Hfg.
    do 2 apply base_paths in Hfg.
    apply (maponpaths (postcomp_with (η_ret a))) in Hfg.
    change (η_ret a ∘ (η' a ∘ pr11 f) = η_ret a ∘ (η' a ∘ pr11 g)) in Hfg.
    do 2 apply carrier_eq.
    refine (_ @ Hfg @ _).
    - now rewrite (assoc'_thunkable _ (pr21 f)), η'_has_retract, magmoid_id_right.
    - now rewrite (assoc'_thunkable _ (pr21 g)), η'_has_retract, magmoid_id_right.
  Qed.

  Lemma is_negative_equalizing_upshift_downshift_negative_linear_to_positive_thunkable
    : is_negative_equalizing θ.
  Proof.
    apply is_negative_equalizing_from_is_epi_and_equation.
    1: apply is_epi_ε'.
    intros n m f Hf; cbn in n, m, f.
    set (f' := ε_sec n · pr11 f♭).
    assert (Hf' : ε' n · f' = pr11 f♭). {
      etrans; [apply (assoc_linear _ (pr21 f♭))|].
      etrans; [|apply magmoid_id_left].
      etrans; [|apply cancel_postcomposition, (ε'_has_section _)].
      etrans; [|apply (assoc_linear _ (pr21 f♭))].
      do 2 apply base_paths in Hf.
      intermediate_path (ε_sec (⇑(⇓n)) · (#⇑(#⇓ε' n) · pr11 f♭));
        [|refine (maponpaths (λ f, ε_sec _ · f) _); exact Hf].
      etrans; [|apply (assoc'_linear _ (pr21 f♭))].
      apply cancel_postcomposition, ε_sec_natural.
    }
    assert (Hlinear : is_linear f'). {
      apply is_linear_of_force_unwrap.
      fold (ε' n).
      refine (Hf' @ _).
      apply pathsinv0.
      subst f' ε_sec; cbn.
      etrans. {
        refine (maponpaths (λ f, force _ · f) _).
        etrans; [refine (maponpaths (λ f, unwrap _ · f) _);
                 apply (assoc'_thunkable _ (wrap n) (delay (⇓n)))|].
        etrans; [apply assoc_linear, (is_linear_compose (delay (⇓n)) (pr11 f♭)
                                        (is_linear_of_positive _ (⇓n))
                                        (pr21 f♭))|].
        etrans; [apply cancel_postcomposition, unwrap_wrap_id|].
        apply magmoid_id_left.
      }
      etrans; [apply (assoc_linear _ (pr21 f♭))|].
      etrans; [apply cancel_postcomposition, force_delay_id|].
      apply magmoid_id_left.
    }
    apply hinhpr.
    exists (make_linear_mor _ Hlinear,,tt).
    do 2 apply carrier_eq.
    exact Hf'.
  Qed.

  Lemma is_positive_equalizing_downshift_upshift_positive_thunkable_to_negative_linear
    : is_positive_equalizing θ.
  Proof.
    apply is_positive_equalizing_from_is_monic_and_equation.
    1: apply is_monic_η'.
    intros p q f Hf; cbn in p, q, f.
    set (f' := η_ret q ∘ pr11 f♯).
    assert (Hf' : η' q ∘ f' = pr11 f♯). {
      etrans; [apply (assoc'_thunkable _ (pr21 f♯))|].
      etrans; [|apply magmoid_id_right].
      etrans; [|apply cancel_precomposition, (η'_has_retract _)].
      etrans; [|apply (assoc'_thunkable _ (pr21 f♯))].
      do 2 apply base_paths in Hf.
      intermediate_path (η_ret (⇓(⇑q)) ∘ (#⇓(#⇑η' q) ∘ pr11 f♯));
        [|refine (maponpaths (λ f, η_ret _ ∘ f) _); exact Hf].
      etrans; [|apply (assoc_thunkable _ (pr21 f♯))].
      apply cancel_precomposition, η_ret_natural.
    }
    assert (Hthunkable : is_thunkable f'). {
      apply is_thunkable_of_delay_wrap.
      fold (η' q).
      refine (Hf' @ _).
      apply pathsinv0.
      subst f' η_ret; cbn.
      etrans. {
        refine (maponpaths (λ f, wrap _ ∘ f) _).
        etrans; [refine (maponpaths (λ f, delay _ ∘ f) _);
                 apply (assoc_linear _ (force q) (unwrap (⇑q)))|].
        etrans; [apply assoc'_thunkable, (is_thunkable_compose (pr11 f♯) (unwrap (⇑q))
                                            (pr21 f♯)
                                            (is_thunkable_of_negative _ (⇑q)))|].
        etrans; [apply cancel_precomposition, force_delay_id|].
        apply magmoid_id_right.
      }
      etrans; [apply (assoc'_thunkable _ (pr21 f♯))|].
      etrans; [apply cancel_precomposition, unwrap_wrap_id|].
      apply magmoid_id_right.
    }
    apply hinhpr.
    exists (make_thunkable_mor _ Hthunkable,,tt).
    do 2 apply carrier_eq.
    exact Hf'.
  Qed.

  Lemma is_fully_equalizing_upshift_downshift_negative_linear_to_positive_thunkable
    : is_fully_equalizing θ.
  Proof.
    apply make_is_fully_equalizing.
    - apply is_negative_equalizing_upshift_downshift_negative_linear_to_positive_thunkable.
    - apply is_positive_equalizing_downshift_upshift_positive_thunkable_to_negative_linear.
  Qed.

End shift_is_equalizing.

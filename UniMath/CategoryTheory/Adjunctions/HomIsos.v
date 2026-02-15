(********************************************************************************

 Natural Hom-Type Isomorhisms

 Author: B. Szilvasy
 January 2026

 Adjunctions defined by natural isomorphisms of hom-types behave better than
 unit-counit isomorphisms do when lacking associativity. For example, such
 isomorphisms can easily be composed without invoking associativity. This file
 generalises the [natural_hom_weq] construction to permit inverses, more general
 composition, and the construction of a hom-type isomorphism from a
 fully-faithful functor.

 [natural_bi_hom_weq]s are isomorphisms between pairs of functors sharing a
 codomain [C₁ᵒᵖ -F⟶ D ⟵G- C₂] (which look like cospans in Cat), when those pairs of
 functors are taken to their hom-functors in [[C₁ᵒᵖ × C₂, SET]].

 Contents:
 1. Definition of a natural isomorphism of hom-types
 2. Groupoid structure and lemmas for hom-type isomorphisms

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.

(** ** 1. Definition of a natural isomorphism of hom-types *)

Section bi_nat_hom_weq_def.
  Context {C₁ C₂ D₁ D₂ : precategory_data}
    {L₁ : functor_data D₁ C₁} {R₁ : functor_data D₂ C₁}
    {L₂ : functor_data D₁ C₂} {R₂ : functor_data D₂ C₂}.

  (** An isomorphism of hom-types *)
  Definition bi_hom_weq : UU
    := ∏ (a : D₁) (b : D₂), C₁⟦L₁ a, R₁ b⟧ ≃ C₂⟦L₂ a, R₂ b⟧.

  (** Naturality in [a] *)
  Definition bi_hom_weq_precomp_law (hom_weq : bi_hom_weq) : UU
    := ∏ (a : D₁) (b : D₂) (f : L₁ a --> R₁ b) (c : D₁) (h : c --> a),
        hom_weq _ _ (#L₁ h · f) = #L₂ h · (hom_weq _ _ f).

  (** Naturality in [b] *)
  Definition bi_hom_weq_postcomp_law (hom_weq : bi_hom_weq) : UU
    := ∏ (a : D₁) (b : D₂) (f : L₁ a --> R₁ b) (c : D₂) (h : b --> c),
      hom_weq _ _ (f · #R₁ h) = (hom_weq _ _ f) · #R₂ h.

  (** Bundling of the natural isomorphism *)
  Definition natural_bi_hom_weq : UU
    := ∑ (hom_weq : bi_hom_weq),
      bi_hom_weq_precomp_law hom_weq ×
        bi_hom_weq_postcomp_law hom_weq.

  Definition make_natural_bi_hom_weq
    (hom_weq : bi_hom_weq)
    (H1 : bi_hom_weq_precomp_law hom_weq)
    (H2 : bi_hom_weq_postcomp_law hom_weq)
    : natural_bi_hom_weq := hom_weq,,H1,,H2.

  Definition natural_bi_hom_weq_to_weq (φ : natural_bi_hom_weq)
    : bi_hom_weq := pr1 φ.
  Definition natural_bi_hom_weq_to_precomp_law (φ : natural_bi_hom_weq)
    : bi_hom_weq_precomp_law (natural_bi_hom_weq_to_weq φ) := pr12 φ.
  Definition natural_bi_hom_weq_to_postcomp_law (φ : natural_bi_hom_weq)
    : bi_hom_weq_postcomp_law (natural_bi_hom_weq_to_weq φ) := pr22 φ.

End bi_nat_hom_weq_def.
Arguments bi_hom_weq {_ _ _ _}.
Arguments natural_bi_hom_weq {_ _ _ _}.

(** [natural_bi_hom_weq] is definitionally equal to [natural_hom_weq] with identities *)
Example eq_natural_hom_weq_natural_bi_hom_weq
  {C D : precategory_data} (F : functor_data C D) (G : functor_data D C)
  : natural_hom_weq F G = natural_bi_hom_weq F (functor_identity D) (functor_identity C) G.
Proof. apply idpath. Qed.

(** Projections of the natural isomorphism *)
Section bi_nat_hom_weq_ops.
  Context {C₁ C₂ D₁ D₂ : precategory_data}
    {L₁ : functor_data D₁ C₁} {R₁ : functor_data D₂ C₁}
    {L₂ : functor_data D₁ C₂} {R₂ : functor_data D₂ C₂}.

  Definition hom_weq2 (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂) {a : D₁} {b : D₂}
    : C₁⟦L₁ a, R₁ b⟧ ≃ C₂⟦L₂ a, R₂ b⟧ := natural_bi_hom_weq_to_weq φ a b.

  Definition hom_weq2_precomp (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂) {a : D₁} {b : D₂} {c : D₁}
    (f : L₁ a --> R₁ b) (h : c --> a)
    : hom_weq2 φ (#L₁ h · f) = #L₂ h · (hom_weq2 φ f)
    := natural_bi_hom_weq_to_precomp_law φ a b f c h.

  Definition hom_weq2_postcomp (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂) {a : D₁} {b : D₂} {c : D₂}
    (f : L₁ a --> R₁ b) (h : b --> c)
    : hom_weq2 φ (f · #R₁ h) = (hom_weq2 φ f) · #R₂ h
    := natural_bi_hom_weq_to_postcomp_law φ a b f c h.

  Definition hom_weq2_inv (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂) {a : D₁} {b : D₂}
    : C₂⟦L₂ a, R₂ b⟧ ≃ C₁⟦L₁ a, R₁ b⟧ := invweq (hom_weq2 φ).

  Corollary hom_weq2_inv_precomp (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂) {a : D₁} {b : D₂} {c : D₁}
    (g : L₂ a --> R₂ b) (h : c --> a)
    : hom_weq2_inv φ (# L₂ h · g) = # L₁ h · hom_weq2_inv φ g.
  Proof.
    apply pathsinv0, pathsweq1.
    refine (hom_weq2_precomp φ _ h @ _).
    apply cancel_precomposition.
    apply homotweqinvweq.
  Defined.

  Corollary hom_weq2_inv_postcomp (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂) {a : D₁} {b : D₂} {c : D₂}
    (g : L₂ a --> R₂ b) (h : b --> c)
    : hom_weq2_inv φ (g · # R₂ h) = hom_weq2_inv φ g · # R₁ h.
  Proof.
    apply pathsinv0, pathsweq1.
    refine (hom_weq2_postcomp φ _ h @ _).
    apply cancel_postcomposition.
    apply homotweqinvweq.
  Defined.
End bi_nat_hom_weq_ops.

(** ** 2. Groupoid structure and lemmas for hom-type isomorphisms

Such natural isomorphisms have identity, vertical composition, and inverses,
even without any functor or category laws. *)

Section bi_nat_hom_weq_groupoid.
  Context {C₁ C₂ C₃ D₁ D₂ : precategory_data}
    {L₁ : functor_data D₁ C₁} {R₁ : functor_data D₂ C₁}
    {L₂ : functor_data D₁ C₂} {R₂ : functor_data D₂ C₂}
    {L₃ : functor_data D₁ C₃} {R₃ : functor_data D₂ C₃}.

  Definition natural_bi_hom_weq_identity
    : natural_bi_hom_weq L₁ R₁ L₁ R₁.
  Proof.
    use make_natural_bi_hom_weq.
    1: intros a b; apply idweq.
    all: easy.
  Defined.

  Definition natural_bi_hom_weq_compose
    (φ₁ : natural_bi_hom_weq L₁ R₁ L₂ R₂)
    (φ₂ : natural_bi_hom_weq L₂ R₂ L₃ R₃)
    : natural_bi_hom_weq L₁ R₁ L₃ R₃.
  Proof.
    use make_natural_bi_hom_weq.
    - intros a b.
      exact (weqcomp (hom_weq2 φ₁) (hom_weq2 φ₂)).
    - intros a b f c h.
      refine (maponpaths _ (hom_weq2_precomp φ₁ _ h) @ _).
      apply (hom_weq2_precomp φ₂ _ h).
    - intros a b f c h.
      refine (maponpaths _ (hom_weq2_postcomp φ₁ _ h) @ _).
      apply (hom_weq2_postcomp φ₂ _ h).
  Defined.

  Definition natural_bi_hom_weq_inv (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂)
    : natural_bi_hom_weq L₂ R₂ L₁ R₁.
  Proof.
    use make_natural_bi_hom_weq.
    - intros a b; exact (hom_weq2_inv φ).
    - intros a b g c h; apply (hom_weq2_inv_precomp φ).
    - intros a b g c h; apply (hom_weq2_inv_postcomp φ).
  Defined.
End bi_nat_hom_weq_groupoid.

Section bi_nat_hom_weq_lemmas.
  (** We also have a form of horizontal composition. *)
  Lemma natural_bi_hom_weq_hcomp {C₁ C₂ D₁ C₁' D₂' : precategory_data}
    {L₁ : functor_data D₁ C₁}
    {L₂ : functor_data D₁ C₂} {R₂ : functor_data C₁ C₂}
    {L₁' : functor_data C₁ C₁'} {R₁' : functor_data D₂' C₁'}
    {R₂' : functor_data D₂' C₁}
    (φ : natural_bi_hom_weq L₁ (functor_identity _) L₂ R₂)
    (φ' : natural_bi_hom_weq L₁' R₁' (functor_identity _) R₂')
    : natural_bi_hom_weq
        (functor_composite_data L₁ L₁')
        R₁' L₂
        (functor_composite_data R₂' R₂).
  Proof.
    use make_natural_bi_hom_weq.
    - intros a b.
      intermediate_weq (C₁⟦L₁ a, R₂' b⟧).
      + apply (hom_weq2 φ').
      + apply (hom_weq2 φ).
    - intros a b f c h; cbn.
      refine (maponpaths _ (hom_weq2_precomp φ' _ _) @ _).
      apply (hom_weq2_precomp φ).
    - intros a b f c h; cbn.
      refine (maponpaths _ (hom_weq2_postcomp φ' _ _) @ _).
      apply (hom_weq2_postcomp φ).
  Defined.

  (** Any fully faithful functor gives a [bi_nat_hom_weq].
      This is generalized below. *)
  Remark natural_bi_hom_weq_from_fully_faithful {C C' : precategory_data}
    (F : functor C C') (Hff : fully_faithful F)
    : natural_bi_hom_weq (functor_identity C) (functor_identity C) F F.
  Proof.
    use make_natural_bi_hom_weq.
    1: exact (weq_from_fully_faithful Hff).
    1, 2: intros a b f c h; apply functor_comp.
  Defined.

  (** Pre-composition with a functor gives a new homweq *)
  Lemma natural_bi_hom_weq_precomp_functors {C₁ C₂ D₁ D₂ E₁ E₂ : precategory_data}
    {L₁ : functor_data D₁ C₁} {R₁ : functor_data D₂ C₁}
    {L₂ : functor_data D₁ C₂} {R₂ : functor_data D₂ C₂}
    (Lpre : functor_data E₁ D₁) (Rpre : functor_data E₂ D₂)
    (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂)
    : natural_bi_hom_weq
        (functor_composite_data Lpre L₁)
        (functor_composite_data Rpre R₁)
        (functor_composite_data Lpre L₂)
        (functor_composite_data Rpre R₂).
  Proof.
    use make_natural_bi_hom_weq.
    - intros a b.
      exact (hom_weq2 φ).
    - intros a b f c g.
      apply (hom_weq2_precomp φ).
    - intros a b f c g.
      apply (hom_weq2_postcomp φ).
  Defined.

  Corollary natural_bi_hom_weq_precomp_functor_l {C₁ C₂ D₁ D₂ E₁ : precategory_data}
    {L₁ : functor_data D₁ C₁} {R₁ : functor_data D₂ C₁}
    {L₂ : functor_data D₁ C₂} {R₂ : functor_data D₂ C₂}
    (Lpre : functor_data E₁ D₁)
    (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂)
    : natural_bi_hom_weq
        (functor_composite_data Lpre L₁) R₁
        (functor_composite_data Lpre L₂) R₂.
  Proof.
    exact (natural_bi_hom_weq_precomp_functors Lpre (functor_identity _) φ).
  Defined.

  Corollary natural_bi_hom_weq_precomp_functor_r {C₁ C₂ D₁ D₂ E₁ : precategory_data}
    {L₁ : functor_data D₁ C₁} {R₁ : functor_data D₂ C₁}
    {L₂ : functor_data D₁ C₂} {R₂ : functor_data D₂ C₂}
    (Rpre : functor_data E₁ D₂)
    (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂)
    : natural_bi_hom_weq
        L₁ (functor_composite_data Rpre R₁)
        L₂ (functor_composite_data Rpre R₂).
  Proof.
    exact (natural_bi_hom_weq_precomp_functors (functor_identity _) Rpre φ).
  Defined.

  (** Post-composition with a fully faithful functor gives a new homweq *)
  Lemma natural_bi_hom_weq_postcomp_functors {C₁ C₂ D₁ D₂ E₁ E₂ : precategory_data}
    {L₁ : functor_data D₁ C₁} {R₁ : functor_data D₂ C₁}
    {L₂ : functor_data D₁ C₂} {R₂ : functor_data D₂ C₂}
    (C₁post : functor C₁ E₁) (C₂post : functor C₂ E₂)
    (Hff₁ : fully_faithful C₁post) (Hff₂ : fully_faithful C₂post)
    (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂)
    : natural_bi_hom_weq
        (functor_composite_data L₁ C₁post)
        (functor_composite_data R₁ C₁post)
        (functor_composite_data L₂ C₂post)
        (functor_composite_data R₂ C₂post).
  Proof.
    use make_natural_bi_hom_weq.
    - intros a b.
      refine (_ ∘ hom_weq2 φ ∘ _)%weq.
      + apply invweq, (weq_from_fully_faithful Hff₁).
      + apply (weq_from_fully_faithful Hff₂).
    - intros a b f c g.
      etrans; [|apply (functor_comp C₂post)].
      apply (maponpaths (#C₂post)).
      etrans; [apply maponpaths, fully_faithful_inv_comp|].
      etrans; [apply maponpaths, cancel_postcomposition,
          (homotinvweqweq (weq_from_fully_faithful Hff₁ _ _))|].
      apply (hom_weq2_precomp φ).
    - intros a b f c g.
      etrans; [|apply (functor_comp C₂post)].
      apply (maponpaths (#C₂post)).
      etrans; [apply maponpaths, fully_faithful_inv_comp|].
      etrans; [apply maponpaths, cancel_precomposition,
          (homotinvweqweq (weq_from_fully_faithful Hff₁ _ _))|].
      apply (hom_weq2_postcomp φ).
  Defined.

  Corollary natural_bi_hom_weq_postcomp_functor_l {C₁ C₂ D₁ D₂ E₁ : precategory_data}
    {L₁ : functor_data D₁ C₁} {R₁ : functor_data D₂ C₁}
    {L₂ : functor_data D₁ C₂} {R₂ : functor_data D₂ C₂}
    (C₁post : functor C₁ E₁) (Hff₁ : fully_faithful C₁post)
    (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂)
    : natural_bi_hom_weq
        (functor_composite_data L₁ C₁post)
        (functor_composite_data R₁ C₁post)
        L₂
        R₂.
  Proof.
    exact (natural_bi_hom_weq_postcomp_functors C₁post (functor_identity _) Hff₁
             identity_functor_is_fully_faithful φ).
  Defined.

  Corollary natural_bi_hom_weq_postcomp_functor_r {C₁ C₂ D₁ D₂ E₁ : precategory_data}
    {L₁ : functor_data D₁ C₁} {R₁ : functor_data D₂ C₁}
    {L₂ : functor_data D₁ C₂} {R₂ : functor_data D₂ C₂}
    (C₂post : functor C₂ E₁) (Hff₂ : fully_faithful C₂post)
    (φ : natural_bi_hom_weq L₁ R₁ L₂ R₂)
    : natural_bi_hom_weq
        L₁
        R₁
        (functor_composite_data L₂ C₂post)
        (functor_composite_data R₂ C₂post).
  Proof.
    exact (natural_bi_hom_weq_postcomp_functors (functor_identity _) C₂post
             identity_functor_is_fully_faithful Hff₂ φ).
  Defined.

End bi_nat_hom_weq_lemmas.

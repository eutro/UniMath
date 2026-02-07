(********************************************************************************

 Natural Transformations of Duploid Functors

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition of a linear and thunkable natural transformation
 1. Definition of a linear and thunkable natural isomorphism

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

Section nat_lt_trans.
  Definition is_nat_lt_trans {C : precategory_ob_mor} {C' : unital_premagmoid_data}
    {F G : functor_data C C'} (α : nat_trans_data F G) : UU
    := ∏ a, is_linear_and_thunkable (α a).

  Definition isaprop_is_nat_lt_trans' {C : precategory_ob_mor} {C' : unital_premagmoid_data}
    {F G : functor_data C C'} (hs : has_homsets C') (α : nat_trans_data F G)
    : isaprop (is_nat_lt_trans α).
  Proof.
    apply impred; intro.
    apply isaprop_is_linear_and_thunkable', hs.
  Qed.

  Definition isaprop_is_nat_lt_trans {C : precategory_ob_mor} {C' : unital_magmoid}
    {F G : functor_data C C'} (α : nat_trans_data F G)
    : isaprop (is_nat_lt_trans α).
  Proof. apply isaprop_is_nat_lt_trans', unital_magmoid_has_homsets. Qed.

  Definition is_nat_lt_trans_comp
    {C : precategory_ob_mor} {C' : unital_premagmoid_data} {F G H : functor_data C C'}
    (α : nat_trans_data F G) (β : nat_trans_data G H)
    (Hα : is_nat_lt_trans α) (Hβ : is_nat_lt_trans β)
    : is_nat_lt_trans (λ a, α a · β a).
  Proof.
    intro a; apply is_linear_and_thunkable_compose.
    - apply Hα.
    - apply Hβ.
  Qed.

  (** Natural transformations compose when they are linear-and-thunkable. *)
  Definition is_nat_trans_comp_of_is_lt
    {C C' : unital_premagmoid_data} {F G H : functor_data C C'}
    (α : nat_trans F G) (β : nat_trans G H)
    (Hα : is_nat_lt_trans α) (Hβ : is_nat_lt_trans β)
    : is_nat_trans _ _ (λ a, α a · β a).
  Proof.
    intros a b f.
    etrans; [apply assoc_linear, (Hβ b)|].
    etrans; [apply cancel_postcomposition, nat_trans_ax|].
    etrans; [apply assoc'_linear, (Hβ b)|].
    etrans; [apply cancel_precomposition, nat_trans_ax|].
    now apply assoc_thunkable, (Hα a).
  Qed.

  Definition nat_trans_comp_of_is_lt
    {C C' : unital_premagmoid_data} {F G H : functor_data C C'}
    (α : nat_trans F G) (β : nat_trans G H)
    (Hα : is_nat_lt_trans α) (Hβ : is_nat_lt_trans β)
    : nat_trans F H
    := make_nat_trans _ _ _ (is_nat_trans_comp_of_is_lt α β Hα Hβ).

  Definition is_nat_trans_identity
    {C : unital_premagmoid_data} {C' : unital_premagmoid} (F : functor_data C C')
    : is_nat_trans F F (λ a, identity (F a)).
  Proof.
    intros a b f.
    etrans; [apply magmoid_id_right | apply pathsinv0, magmoid_id_left].
  Qed.

  Definition nat_trans_identity
    {C : unital_premagmoid_data} {C' : unital_premagmoid} (F : functor_data C C')
    : nat_trans F F := make_nat_trans _ _ _ (is_nat_trans_identity F).

  Definition is_nat_lt_trans_identity
    {C : unital_premagmoid_data} {C' : unital_premagmoid} (F : functor_data C C')
    : is_nat_lt_trans (nat_trans_identity F).
  Proof. intros a; apply is_linear_and_thunkable_identity. Qed.

  Definition nat_lt_trans {C C' : unital_premagmoid_data} (F G : functor_data C C') : UU
    := ∑ (α : nat_trans F G), is_nat_lt_trans α.
  Coercion nat_lt_trans_to_nat_trans {C C' : unital_premagmoid_data} (F G : functor_data C C')
    (α : nat_lt_trans F G) : nat_trans F G := pr1 α.
  Definition nat_lt_trans_is_lt {C C' : unital_premagmoid_data} (F G : functor_data C C')
    (α : nat_lt_trans F G) : is_nat_lt_trans α := pr2 α.
  Definition make_nat_lt_trans {C C' : unital_premagmoid_data} {F G : functor_data C C'}
    (α : nat_trans F G) (H : is_nat_lt_trans α) : nat_lt_trans F G := α,,H.

  Lemma nat_lt_trans_eq {C : unital_premagmoid_data} {C' : unital_magmoid} (F G : functor_data C C')
    (α β : nat_lt_trans F G)
    : (α : nat_trans _ _) = β -> α = β.
  Proof.
    intro H.
    apply subtypePath'; [|apply isaprop_is_nat_lt_trans].
    exact H.
  Defined.

  Definition nat_lt_trans_identity
    {C : unital_premagmoid_data} {C' : unital_premagmoid} (F : functor_data C C')
    : nat_lt_trans F F := make_nat_lt_trans _ (is_nat_lt_trans_identity F).

  Definition nat_lt_trans_comp
    {C : unital_premagmoid_data} {C' : unital_premagmoid} {F G H : functor_data C C'}
    (α : nat_lt_trans F G) (β : nat_lt_trans G H)
    : nat_lt_trans F H.
  Proof.
    use make_nat_lt_trans.
    - apply (nat_trans_comp_of_is_lt α β); apply nat_lt_trans_is_lt.
    - apply is_nat_lt_trans_comp; apply nat_lt_trans_is_lt.
  Defined.

  Definition nat_lt_trans_horcomp
    {C₁ : unital_premagmoid_data} {C₂ C₃ : unital_magmoid}
    {F₁ G₁ : functor C₁ C₂} {F₂ G₂ : C₂ ⟶d C₃}
    (α : nat_lt_trans F₁ G₁) (β : nat_lt_trans F₂ G₂)
    : nat_lt_trans (F₁ ∙ F₂) (G₁ ∙ G₂).
  Proof.
    use make_nat_lt_trans.
    - use make_nat_trans.
      + intros a; exact (β (F₁ a) · #G₂ (α a)).
      + abstract (intros a b f; cbn;
            rewrite assoc_linear; [|apply functor_linear, nat_lt_trans_is_lt];
            rewrite (nat_trans_ax β);
            rewrite assoc'_thunkable; [|apply nat_lt_trans_is_lt];
            rewrite <- functor_comp, (nat_trans_ax α);
            rewrite functor_comp;
            rewrite assoc_thunkable; [|apply nat_lt_trans_is_lt];
            reflexivity).
    - abstract (
          intros a;
          apply is_linear_and_thunkable_compose;
          [ apply (nat_lt_trans_is_lt _ _ β (F₁ a))
          | apply functor_linear_and_thunkable, nat_lt_trans_is_lt ]).
  Defined.

End nat_lt_trans.

Section nat_lt_iso.
  Definition is_nat_lt_iso
    {C : precategory_ob_mor} {D : unital_magmoid}
    {F G : functor_data C D} (α : nat_trans_data F G) : UU
    := ∏ a, is_lt_iso (α a).

  Definition is_nat_lt_iso_to_is_nat_lt_trans {C : precategory_ob_mor} {D : unital_magmoid}
    {F G : functor_data C D} (α : nat_trans_data F G)
    (H : is_nat_lt_iso α) : is_nat_lt_trans α.
  Proof. intro a; apply (H a). Defined.

  Lemma isaprop_is_nat_lt_iso {C : precategory_ob_mor} {D : unital_magmoid}
    {F G : functor_data C D} (α : nat_trans_data F G)
    : isaprop (is_nat_lt_iso α).
  Proof. apply impred; intro; apply isaprop_is_lt_iso. Qed.

  Definition is_nat_lt_iso_inv_is_nat_trans
    {C : precategory_data} {D : unital_magmoid}
    {F G : functor_data C D} (α : nat_trans F G)
    (β : is_nat_lt_iso α)
    : is_nat_trans _ _ (λ a, β a).
  Proof.
    intros a b f; cbn.
    apply (cancel_lt_iso_left (make_lt_iso _ (β a))); cbn.
    etrans; [apply assoc_linear, linear_and_thunkable_mor_is_linear_and_thunkable|].
    etrans; [apply cancel_postcomposition, pathsinv0, nat_trans_ax|].
    intermediate_path (#F f).
    - apply (lt_iso_right (make_lt_iso _ (β b))).
    - apply pathsinv0, (lt_iso_inverse_left (make_lt_iso _ (β a))).
  Qed.

  Definition is_nat_lt_iso_inv_is_nat_lt_iso
    {C D : unital_magmoid}
    {F G : functor_data C D} (α : nat_trans_data F G)
    (β : is_nat_lt_iso α)
    : is_nat_lt_iso (λ a, β a).
  Proof.
    intro a.
    apply (lt_iso_inv (make_lt_iso _ (β a))).
  Defined.

  Definition is_nat_lt_iso_inv_nat_trans
    {C D : unital_magmoid}
    {F G : functor_data C D} (α : nat_trans F G)
    (β : is_nat_lt_iso α)
    : nat_trans G F
    := make_nat_trans _ _ _ (is_nat_lt_iso_inv_is_nat_trans α β).

  Definition nat_lt_iso
    {C : precategory_data} {D : unital_magmoid}
    (F G : functor_data C D) : UU
    := ∑ (α : nat_trans F G), is_nat_lt_iso α.

  Definition make_nat_lt_iso {C : precategory_data} {D : unital_magmoid}
    {F G : functor_data C D} (α : nat_trans F G) (H : is_nat_lt_iso α)
    : nat_lt_iso F G := α,,H.

  Coercion nat_lt_iso_to_nat_trans
    {C : precategory_data} {D : unital_magmoid}
    {F G : functor_data C D} (α : nat_lt_iso F G)
    : nat_trans F G := pr1 α.
  Coercion nat_lt_iso_is_lt_iso
    {C : precategory_data} {D : unital_magmoid}
    {F G : functor_data C D} (α : nat_lt_iso F G)
    : is_nat_lt_iso α := pr2 α.

  Coercion nat_lt_iso_to_nat_lt_trans
    {C : precategory_data} {D : unital_magmoid}
    {F G : functor_data C D} (α : nat_lt_iso F G)
    : nat_lt_trans F G.
  Proof.
    use (make_nat_lt_trans α).
    apply is_nat_lt_iso_to_is_nat_lt_trans, α.
  Defined.

  Definition nat_lt_iso_inv {C D : unital_magmoid}
    (F G : functor_data C D) (α : nat_lt_iso F G)
    : nat_lt_iso G F.
  Proof.
    use make_nat_lt_iso.
    - apply (is_nat_lt_iso_inv_nat_trans α α).
    - apply (is_nat_lt_iso_inv_is_nat_lt_iso α α).
  Defined.

End nat_lt_iso.

(********************************************************************************

 The Hom-Functors of a Unital Magmoid

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition of the hom-functors of a unital magmoid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Export UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.

Local Open Scope cat.
Local Open Scope unital_magmoid.

(** ** 1. Definition of the hom-functors of a unital magmoid *)
Section defs.
  Context [M : unital_magmoid].

  Definition um_homset (a b : M) : hSet
    := make_hSet (M⟦a, b⟧) (unital_magmoid_has_homsets M a b).

  Definition um_hom_functor
    : profunctor (M ₗ) (M ₜ).
  Proof.
    use make_profunctor.
    - use make_profunctor_data.
      + intros a b; apply (um_homset a b).
      + cbn; intros a b f c d g h.
        refine (_ · h · _).
        * apply f.
        * apply g.
    - refine (_,,_,,_); cbn.
      + intros a b h.
        apply (magmoid_id_right _ @ magmoid_id_left _).
      + intros y₁ y₂ y₃ g₁ g₂ x₁ x₂ x₃ f₁ f₂ h.
        rewrite (assoc_linear _ f₁).
        rewrite (assoc_linear _ f₂).
        rewrite (assoc'_thunkable _ g₂).
        reflexivity.
      + apply unital_magmoid_has_homsets.
  Defined.

  Definition um_hom_functor1 (a : M⁻) : M ₜ ^opp ⟶ HSET.
  Proof.
    eapply functor_fix_snd_arg.
    - apply um_hom_functor.
    - apply a.
  Defined.

  Definition um_hom_functor2 (a : M⁺) : M ₗ ⟶ HSET.
  Proof.
    eapply functor_fix_fst_arg.
    - apply um_hom_functor.
    - apply a.
  Defined.

End defs.

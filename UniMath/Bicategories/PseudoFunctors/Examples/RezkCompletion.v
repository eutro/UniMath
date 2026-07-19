(********************************************************************************

 Rezk-completion of 1-categories as a pseudofunctor

 Author: B. Szilvasy
 May 2026

 Contents:
 1. Rezk-completion as a pseudofunctor

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.RezkCompletions.RezkCompletions.

Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.FromUniversalArrow.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.

Local Open Scope cat.

Definition rezk_completion_left_universal_arrow
  (ℜ : RezkCat) (* type in Emacs with agda-input as \MfR *)
  : left_universal_arrow univ_cats_to_cats.
Proof.
  exists (λ C, rezk_completion_to_category (ℜ C)).
  exists (λ C, rezk_completion_functor (ℜ C)).
  intros C D; cbn in C, D.
  exact (rezk_completion_functor_equivalence C (ℜ C) _ (univalent_category_is_univalent D)).
Defined.

Definition rezk_completion_psfunctor
  (ℜ : RezkCat) (* type in Emacs with agda-input as \MfR *)
  : psfunctor bicat_of_cats bicat_of_univ_cats
  := psfunctor_from_left_universal_arrow univ_cats_to_cats
       (rezk_completion_left_universal_arrow ℜ).

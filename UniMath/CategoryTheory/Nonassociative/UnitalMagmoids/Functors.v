(********************************************************************************

 Functors of Unital Magmoids

 Author: B. Szilvasy
 January 2026

 Contents:
 TODO

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.

Local Open Scope cat.

Section functor_facts.
  Context {C C' : unital_premagmoid} (F : C ⟶ C').
  Hypothesis (Hfull : full F).

  Lemma is_linear_in_full_functor {a b : C} (f : a --> b)
    (H : is_linear f) : is_linear (#F f).
  Proof.
    intros c d g h.
    Fail Check (Hfull _ _ h).
  Abort.

End functor_facts.

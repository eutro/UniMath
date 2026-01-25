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

(** ** 1. Definition of the submagmoid in the image of a functor.

 The full unital premagmoid in the image of [F : M ⟶ M'] has objects of the form
 [F a : M'] for objects [a : M], with morphisms and composition given by those
 in [M']. *)

Section functor_image.
  Context {M M' : unital_premagmoid} (F : functor_data M M').
  Hypothesis (hs : has_homsets M').

  Definition functor_full_image_premagmoid_data : unital_premagmoid_data.
  Proof.
    use make_precategory_data.
    - use (make_precategory_ob_mor (ob M)).
      intros a b; exact (M'⟦F a, F b⟧).
    - intro a; exact (identity (F a)).
    - intros a b c f g; exact (f · g).
  Defined.

  Definition functor_full_image_premagmoid_is_unital
    : is_unital_premagmoid functor_full_image_premagmoid_data.
  Proof.
    use make_is_unital_premagmoid.
    - intros a b f; apply magmoid_id_left.
    - intros a b f; apply magmoid_id_right.
  Qed.

  Definition functor_full_image_premagmoid : unital_premagmoid
    := make_unital_premagmoid _ functor_full_image_premagmoid_is_unital.

  Definition functor_full_image_magmoid' : unital_magmoid.
  Proof.
    apply (make_unital_magmoid functor_full_image_premagmoid).
    intros a b; apply hs.
  Defined.

End functor_image.

Definition functor_full_image_magmoid
  {M : unital_premagmoid} {M' : unital_magmoid} (F : M ⟶ M') : unital_magmoid.
Proof. apply (functor_full_image_magmoid' F), unital_magmoid_has_homsets. Defined.

Section functor_facts.
  Context {M : unital_premagmoid} {M' : unital_magmoid} (F : M ⟶ M').

  (** F applied to a linear morphism is not necessarily linear in the codomain
      of F, even if it is full, as there may extra objects in the codomain
      unrelated to those in F's image. *)
  Lemma is_linear_in_full_functor {a b : M} (f : a --> b)
    (Hfull : full F) (H : is_linear f) : is_linear (#F f).
  Proof.
    intros c d g h.
    Fail Check (Hfull _ _ h). (* Fails because h is not of the form M'⟦F _, F _⟧ *)
  Abort.

  (** However, once restricted to the full subcategory of objects in F's image, fullness is
      sufficient. *)
  Lemma is_linear_in_full_functor_image {a b : M} (f : a --> b)
    (Hfull : full F) (Hlinear : is_linear f) : is_linear (M:=functor_full_image_magmoid F) (#F f).
  Proof.
    intros c d g h.
    eset (Hprop := unital_magmoid_has_homsets _ _ _ _ _).
    refine (factor_through_squash Hprop (λ Hh, _) (Hfull _ _ h)).
    refine (factor_through_squash Hprop (λ Hg, _) (Hfull _ _ g)).
    induction Hh as [h' Hh'], Hg as [g' Hg'].
    rewrite <- Hh', <- Hg'; cbn.
    do 4 rewrite <- (functor_comp F).
    apply maponpaths, Hlinear.
  Qed.

  Lemma is_thunkable_in_full_functor_image {a b : M} (f : a --> b)
    (Hfull : full F) (Hthunkable : is_thunkable f) : is_thunkable (M:=functor_full_image_magmoid F) (#F f).
  Proof.
    intros c d g h.
    eset (Hprop := unital_magmoid_has_homsets _ _ _ _ _).
    refine (factor_through_squash Hprop (λ Hh, _) (Hfull _ _ h)).
    refine (factor_through_squash Hprop (λ Hg, _) (Hfull _ _ g)).
    induction Hh as [h' Hh'], Hg as [g' Hg'].
    rewrite <- Hh', <- Hg'; cbn.
    do 4 rewrite <- (functor_comp F).
    apply maponpaths, Hthunkable.
  Qed.

  Lemma is_linear_and_thunkable_in_full_functor_image {a b : M} (f : a --> b)
    (Hfull : full F) (Hlt : is_linear_and_thunkable f)
    : is_linear_and_thunkable (M:=functor_full_image_magmoid F) (#F f).
  Proof.
    use make_is_linear_and_thunkable.
    - apply (is_linear_in_full_functor_image f Hfull Hlt).
    - apply (is_thunkable_in_full_functor_image f Hfull Hlt).
  Qed.

End functor_facts.

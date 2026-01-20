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
  Context {M M' : unital_premagmoid} (F : M ⟶ M').

  (* Lemma of shame *)
  Lemma is_linear_in_full_functor {a b : M} (f : a --> b)
    (Hfull : full F) (H : is_linear f) : is_linear (#F f).
  Proof.
    intros c d g h.
    Fail Check (Hfull _ _ h).
  Abort.

End functor_facts.

(** ** 1. Definition of the submagmoid in the image of a functor. *)

Section functor_image.
  Context {M M' : unital_premagmoid} (F : M ⟶ M').
  Hypothesis (hs : has_homsets M').

  Definition functor_full_image_premagmoid_data : unital_premagmoid_data.
  Proof.
    use make_precategory_data.
    - use (make_precategory_ob_mor M).
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

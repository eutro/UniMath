(********************************************************************************

 Categories as Unital (Pre)magmoids

 Author: B. Szilvasy
 January 2026

 This file provides alternative definitions of (pre)categories in terms of their
 unital (pre)magmoid, and coercions to reassociate all of the relevant data.

 Contents:
 1. Coercions from (pre)categories to unital (pre)magmoids
 2. Alternative definition of [precategory]
 3. Alternative definition of [category]
 4. Lemmas about polarization

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.

Local Open Scope cat.
Local Open Scope unital_magmoid.

(** ** 1. Coercions from (pre)categories to unital (pre)magmoids *)

Definition precategory_is_unital (C : precategory) : is_unital_premagmoid C.
Proof.
  use make_is_unital_premagmoid.
  - apply id_left.
  - apply id_right.
Defined.

Definition precategory_is_assoc (C : precategory) : is_assoc_premagmoid C.
Proof.
  use make_is_assoc_premagmoid.
  - apply assoc.
  - apply assoc'.
Defined.

Coercion precategory_to_unital_premagmoid (C : precategory) : unital_premagmoid
  := make_unital_premagmoid C (precategory_is_unital C).
Coercion category_to_unital_magmoid (M : category) : unital_magmoid
  := make_unital_magmoid M (homset_property M).

(** ** 1. Alternative definition of [precategory] *)

Definition magmoid_precategory : UU
:= ∑ (M : unital_premagmoid), is_assoc_premagmoid M.
Definition make_magmoid_precategory
  (M : unital_premagmoid)
  (H : is_assoc_premagmoid M) : magmoid_precategory
  := M,,H.
Coercion magmoid_precategory_to_unital_premagmoid (C : magmoid_precategory) : unital_premagmoid := pr1 C.
Definition magmoid_precategory_is_assoc (C : magmoid_precategory) : is_assoc_premagmoid C := pr2 C.

Definition magmoid_precategory_is_precategory (C : magmoid_precategory) : is_precategory C.
Proof.
  use make_dirprod.
  - apply unital_premagmoid_is_unital.
  - apply magmoid_precategory_is_assoc.
Defined.

Coercion magmoid_precategory_to_precategory (C : magmoid_precategory) : precategory
  := make_precategory C (magmoid_precategory_is_precategory C).

Coercion precategory_to_magmoid_precategory (C : precategory) : magmoid_precategory
  := make_magmoid_precategory C (precategory_is_assoc C).

(** ** 2. Alternative definition of [category] *)

Definition magmoid_category : UU
  := ∑ (M : unital_magmoid), is_assoc_premagmoid M.
Definition make_magmoid_category
  (M : unital_magmoid)
  (H : is_assoc_premagmoid M)
  : magmoid_category
  := M,,H.
Coercion magmoid_category_to_unital_magmoid (M : magmoid_category) : unital_magmoid := pr1 M.
Definition magmoid_category_is_assoc (M : magmoid_category) : is_assoc_premagmoid M := pr2 M.
Coercion magmoid_category_to_magmoid_precategory (M : magmoid_category) : magmoid_precategory
  := make_magmoid_precategory M (magmoid_category_is_assoc M).

Coercion magmoid_category_to_category (M : magmoid_category) : category
  := make_category M (unital_magmoid_has_homsets M).

Coercion category_to_magmoid_category (M : category) : magmoid_category
  := make_magmoid_category M (precategory_is_assoc M).

(** ** 4. Lemmas about polarization *)

Section polarity_lemmas.
  Context {C : precategory}.

  (** All morphisms in a category are linear and thunkable, and hence objects in a
      category are both positive and negative. *)

  Lemma is_linear_of_precategory {a b : C} (f : a --> b) : is_linear f.
  Proof.
    intros c d g h.
    apply assoc'.
  Defined.

  Lemma is_thunkable_of_precategory {a b : C} (f : a --> b) : is_thunkable f.
  Proof.
    intros c d g h.
    apply assoc.
  Defined.

  Lemma is_negative_and_thunkable_of_precategory {a b : C} (f : a --> b) : is_linear_and_thunkable f.
  Proof.
    use make_is_linear_and_thunkable.
    - apply is_linear_of_precategory.
    - apply is_thunkable_of_precategory.
  Defined.

  Lemma is_positive_of_precategory (a : C) : is_positive a.
  Proof.
    intros b f.
    apply is_linear_of_precategory.
  Defined.

  Lemma is_negative_of_precategory (a : C) : is_negative a.
  Proof.
    intros b f.
    apply is_thunkable_of_precategory.
  Defined.
End polarity_lemmas.

Section polarity_lemmas.
  Context {C : category}.

  (** Linear and positive morphisms are the same as morphisms in C. *)
  Lemma isweq_linear_mor_to_mor_of_category (a b : C)
    : isweq (λ (f : linear_mor (M:=C) a b), linear_mor_to_mor f).
  Proof.
    apply isweqpr1; intro f.
    apply (iscontraprop1 (propproperty _)),
      is_linear_of_precategory.
  Qed.

  Definition weq_linear_mor_to_mor_of_category (a b : C)
    : linear_mor (M:=C) a b ≃ C⟦a, b⟧
    := make_weq _ (isweq_linear_mor_to_mor_of_category a b).

  Lemma isweq_thunkable_mor_to_mor_of_category (a b : C)
    : isweq (λ (f : thunkable_mor (M:=C) a b), thunkable_mor_to_mor f).
  Proof.
    apply isweqpr1; intro f.
    apply (iscontraprop1 (propproperty _)),
      is_thunkable_of_precategory.
  Qed.

  Definition weq_thunkable_mor_to_mor_of_category (a b : C)
    : thunkable_mor (M:=C) a b ≃ C⟦a, b⟧
    := make_weq _ (isweq_thunkable_mor_to_mor_of_category a b).

  (** Positive and negative objects are the same as objects in C. *)
  Lemma isweq_positive_ob_to_ob_of_category
    : isweq (positive_ob_to_ob (M:=C)).
  Proof.
    change (isweq (X:=positive_ob C) pr1).
    apply isweqpr1; intro f.
    apply (iscontraprop1 (propproperty _)),
      is_positive_of_precategory.
  Qed.

  Definition weq_positive_ob_to_ob_of_category
    : positive_ob C ≃ ob C
    := make_weq _ isweq_positive_ob_to_ob_of_category.

  Lemma isweq_negative_ob_to_ob_of_category
    : isweq (negative_ob_to_ob (M:=C)).
  Proof.
    change (isweq (X:=negative_ob C) pr1).
    apply isweqpr1; intro f.
    apply (iscontraprop1 (propproperty _)),
      is_negative_of_precategory.
  Qed.

  Definition weq_negative_ob_to_ob_of_category
    : negative_ob C ≃ ob C
    := make_weq _ isweq_negative_ob_to_ob_of_category.
End polarity_lemmas.

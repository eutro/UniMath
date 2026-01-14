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

Local Open Scope cat.

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

(** ** 4. Lemmas about polarization

 All morphisms in a category are linear and thunkable, and all objects in a
 category are both positive and negative.

 *)

(* TODO *)

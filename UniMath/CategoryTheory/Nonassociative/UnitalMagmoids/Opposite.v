(********************************************************************************

 Opposite Magmoids

 Author: B. Szilvasy
 January 2026

 The opposite of a unital magmoid is the same magmoid obtained by reversing all
 of the arrows. Important properties in a unital magmoid have duals: [is_linear]
 and [is_thunkable] are dual, [is_positive] and [is_negative] are dual,
 [is_linear_and_thunkable] is self-dual etc. Where possible, the properties and
 types are carefully written so that this duality holds definitionally, or if
 not possible, up to an involution.

 Contents:
 1. Definition of the opposite magmoid
 2. Dualities defined in terms of the opposite magmoid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.

Local Open Scope cat.
Local Open Scope unital_magmoid.

(** ** 1. Definition of the opposite magmoid *)

Definition is_unital_premagmoid_opp_precat_data (M : unital_premagmoid)
  : is_unital_premagmoid (opp_precat_data M).
Proof.
  use make_is_unital_premagmoid.
  - intros a b f; apply magmoid_id_right.
  - intros a b f; apply magmoid_id_left.
Defined.

Definition opp_premagmoid (M : unital_premagmoid) : unital_premagmoid
  := make_unital_premagmoid _ (is_unital_premagmoid_opp_precat_data M).

Local Notation "C '^op'" := (opp_premagmoid C) (at level 1, format "C ^op") : unital_magmoid.

Goal ∏ C:unital_premagmoid, C^op^op = C. reflexivity. Qed.

Definition opp_magmoid (M : unital_magmoid) : unital_magmoid.
Proof.
  use (make_unital_magmoid M^op).
  intros a b; apply unital_magmoid_has_homsets.
Defined.

Local Notation "C '^opm'" := (opp_magmoid C) (at level 1, format "C ^opm") : unital_magmoid.

(** ** 2. Dualities defined in terms of the opposite magmoid *)

(** [is_linear] and [is_thunkable] are dual, definitionally *)
Lemma opp_magmoid_is_linear {M : unital_premagmoid} {a b : M} (f : a --> b)
  : is_linear (M:=M^op) f = is_thunkable f.
Proof. reflexivity. Defined.
Lemma opp_magmoid_is_thunkable {M : unital_premagmoid} {a b : M} (f : a --> b)
  : is_thunkable (M:=M^op) f = is_linear f.
Proof. reflexivity. Defined.

(** [is_positive] and [is_negative] are dual, definitionally *)
Lemma opp_magmoid_is_positive {M : unital_premagmoid} (a : M)
  : is_positive (M:=M^op) a = is_negative a.
Proof. reflexivity. Defined.
Lemma opp_magmoid_is_negative {M : unital_premagmoid} (a : M)
  : is_negative (M:=M^op) a = is_positive a.
Proof. reflexivity. Defined.

(** [is_linear_and_thunkable] is self-dual, not definitionally *)
Lemma opp_magmoid_is_linear_and_thunkable {M : unital_premagmoid} {a b : M} (f : a --> b)
  : is_linear_and_thunkable (M:=M^op) f -> is_linear_and_thunkable f.
Proof.
  intro H; use make_dirprod.
  - apply (is_linear_and_thunkable_to_is_thunkable (M:=M^op) f H).
  - apply (is_linear_and_thunkable_to_is_linear (M:=M^op) f H).
Defined.

(** Tactic to close a goal of the form [isweq (opp_magmoid_XYZ M [_ ...])] with
    inverse [@opp_magmoid_XYZ M^op]. *)
Ltac opp_magmoid_do_involution inverse :=
  use isweq_iso; first [ use inverse | abstract easy | idtac ].

Ltac opp_magmoid_involution_on F M Mop :=
  lazymatch F with
  | ?f M ?a1 => opp_magmoid_do_involution (f Mop)
  | ?f M ?a1 ?a2 => opp_magmoid_do_involution (f Mop)
  | ?f M ?a1 ?a2 ?a3 => opp_magmoid_do_involution (f Mop)
  end.

Ltac opp_magmoid_involution :=
  lazymatch goal with
  | M : unital_premagmoid |- isweq ?F => opp_magmoid_involution_on F M (opp_premagmoid M)
  | M : unital_magmoid |- isweq ?F => opp_magmoid_involution_on F M (opp_magmoid M)
  | |- isweq _ => fail "No unital magmoid in context"
  | |- _ => fail "Goal is not isweq"
  end.

Lemma isweq_opp_magmoid_is_linear_and_thunkable {M : unital_premagmoid} {a b : M} (f : a --> b)
  : isweq (opp_magmoid_is_linear_and_thunkable f).
Proof. opp_magmoid_involution. Defined.

(** [linear_and_thunkable_mor] is self-dual, not definitionally *)
Lemma opp_magmoid_linear_and_thunkable_mor {M : unital_magmoid} (a b : M)
  : linear_and_thunkable_mor (M:=M^opm) b a -> linear_and_thunkable_mor a b.
Proof.
  intro f.
  use make_linear_and_thunkable_mor.
  - exact f.
  - apply opp_magmoid_is_linear_and_thunkable,
      (linear_and_thunkable_mor_is_linear_and_thunkable f).
Defined.

Lemma isweq_opp_magmoid_linear_and_thunkable_mor {M : unital_magmoid} (a b : M)
  : isweq (opp_magmoid_linear_and_thunkable_mor a b).
Proof. opp_magmoid_involution. Defined.

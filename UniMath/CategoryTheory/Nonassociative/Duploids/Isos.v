(********************************************************************************

 Isomorphisms of Duploids

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Lemmas about isomorphisms in duploids

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

(** ** 1. Lemmas about isomorphisms in duploids *)

Section isos_facts.
  Context {M : preduploid}.

  (** Every [lt_iso] is also intermediate in a preduploid *)
  Lemma preduploid_lt_iso_is_intermediate {a b : M} (p : lt_iso a b) : is_intermediate p.
  Proof.
    isaprop_goal Hprop; [apply isaprop_is_intermediate|].
    apply (has_polarity_rec (polarity_of M a) Hprop).
    1: intro H; apply is_intermediate_of_negative, H.
    intro Hp; apply is_intermediate_of_positive.
    apply (is_positive_of_lt_iso p Hp).
  Qed.

  Lemma preduploid_lt_iso_interpose {a b b' c : M}
    (p : lt_iso b b') (f : a --> b) (g : b --> c)
    : (f · p) · (lt_iso_inv p · g) = f · g.
  Proof.
    apply (intermediate_z_iso_interpose p).
    - apply preduploid_lt_iso_is_intermediate.
    - apply (preduploid_lt_iso_is_intermediate (lt_iso_inv p)).
  Qed.

  Lemma preduploid_lt_iso_inv_interpose {a b b' c : M}
    (p : lt_iso b' b) (f : a --> b) (g : b --> c)
    : (f · lt_iso_inv p) · (p · g) = f · g.
  Proof. apply (preduploid_lt_iso_interpose (lt_iso_inv p)). Qed.

  (** Every morphism in a preduploid is linear-and-thunkable or intermediate. *)
  Lemma preduploid_linear_and_thunkable_or_intermediate {a b : M} (f : a --> b)
    : ∥ is_linear_and_thunkable f ⨿ is_intermediate f ∥.
  Proof.
    isaprop_goal Hprop; [apply isapropishinh|].
    apply (has_polarity_rec (polarity_of M a) Hprop).
    1: intro H; apply hinhpr, ii2, is_intermediate_of_negative, H.
    intro Hp.
    apply (has_polarity_rec (polarity_of M b) Hprop).
    2: intro H; apply hinhpr, ii2, is_intermediate_of_positive, H.
    intro Hn.
    apply hinhpr, ii1.
    use make_is_linear_and_thunkable.
    - apply is_linear_of_positive, Hp.
    - apply is_thunkable_of_negative, Hn.
  Qed.

End isos_facts.

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
  Proof. apply lt_iso_is_intermediate_from_polarized, (polarity_of M). Qed.

  Lemma isweq_lti_iso_to_lt_iso_in_preduploid (a b : M)
    : isweq (@lti_iso_to_lt_iso M a b).
  Proof. apply isweq_lti_iso_to_lt_iso_from_polarized, (polarity_of M). Qed.

  Definition weq_lti_iso_to_lt_iso_in_preduploid (a b : M)
    : lti_iso a b ≃ lt_iso a b
    := weq_lti_iso_to_lt_iso_from_polarized a b (polarity_of M _).

  Lemma preduploid_lt_iso_interpose {a b b' c : M}
    (p : lt_iso b b') (f : a --> b) (g : b --> c)
    : (f · p) · (lt_iso_inv p · g) = f · g.
  Proof.
    pose (p' := invmap (weq_lti_iso_to_lt_iso_in_preduploid _ _) p).
    apply (i_iso_interpose (lti_iso_to_i_iso p')).
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

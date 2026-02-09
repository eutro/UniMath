(********************************************************************************

 Univalence of Duploids

 Author: B. Szilvasy
 January 2026

 Contents:
 TODO

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

(** ** 1. Definition of Univalence for Duploids *)
Section univalence_def.
  Definition is_duploid_univalent (M : unital_magmoid)
    := ∏ (a b: M), isweq (λ (p : a = b), id_to_lt_iso p).

  Definition lt_iso_to_id {M : unital_magmoid}
    (ua : is_duploid_univalent M) {a b : M}
    : lt_iso a b -> a = b
    := invmap (make_weq _ (ua a b)).

  Lemma id_to_lt_iso_after_lt_iso_to_id {M : unital_magmoid}
    (ua : is_duploid_univalent M) (a b : M) (f : lt_iso a b)
    : id_to_lt_iso (lt_iso_to_id ua f) = f.
  Proof. exact (homotweqinvweq (make_weq _ (ua a b)) f). Qed.

  Lemma lt_iso_to_id_after_id_to_lt_iso {M : unital_magmoid}
    (ua : is_duploid_univalent M) (a b : M) (p : a = b)
    : lt_iso_to_id ua (id_to_lt_iso p) = p.
  Proof. exact (homotinvweqweq (make_weq _ (ua a b)) p). Qed.

  Lemma id_to_lt_iso_postcompose {M : unital_magmoid} (a b b' : M)
    (p : b = b') (f : a --> b)
    : f · id_to_lt_iso p = transportf (λ b, a --> b) p f.
  Proof. induction p; apply magmoid_id_right. Qed.

  Lemma id_to_lt_iso_precompose {M : unital_magmoid} (a a' b : M)
    (p : a = a') (f : a --> b)
    : id_to_lt_iso (!p) · f = transportf (λ a, a --> b) p f.
  Proof. induction p; apply magmoid_id_left. Qed.

  Definition id_to_lt_iso_mor {M : unital_magmoid} {a b : M}
    (p : a = b) : lt_iso_mor (id_to_lt_iso p) = idtomor _ _ p.
  Proof. now induction p. Qed.

  Lemma id_to_lt_iso_inv {M : unital_magmoid} (a a' : M)
    (p : a = a') : id_to_lt_iso (!p) = lt_iso_inv (id_to_lt_iso p).
  Proof.
    apply lt_iso_eq.
    now induction p.
  Qed.

  Lemma lt_iso_to_id_precompose {M : unital_magmoid}
    (ua : is_duploid_univalent M) {a a' b : M}
    (p : lt_iso a a') (f : a --> b)
    : transportf (λ a, a --> b) (lt_iso_to_id ua p) f = lt_iso_inverse p · f.
  Proof.
    rewrite <- id_to_lt_iso_precompose, id_to_lt_iso_inv.
    now rewrite id_to_lt_iso_after_lt_iso_to_id.
  Qed.

  Lemma lt_iso_to_id_postcompose {M : unital_magmoid}
    (ua : is_duploid_univalent M) {a b b' : M}
    (p : lt_iso b b') (f : a --> b)
    : transportf (λ b, a --> b) (lt_iso_to_id ua p) f = f · p.
  Proof.
    rewrite <- id_to_lt_iso_postcompose.
    now rewrite id_to_lt_iso_after_lt_iso_to_id.
  Qed.

End univalence_def.

Section univalence_consequences.
  Lemma isaprop_is_duploid_univalent (M : unital_magmoid)
    : isaprop (is_duploid_univalent M).
  Proof. do 2 (apply impred; intro); apply isapropisweq. Qed.

  (** Polarity shifts become properties in a univalent duploid. *)

  Lemma isaprop_has_negative_shifts (M : unital_magmoid)
    (ua : is_duploid_univalent M)
    : isaprop (has_negative_shifts M).
  Proof.
    apply isaproptotal2; [intro; apply isaprop_negative_shift_axioms|].
    intros U1 U2 H1 H2.
    use negative_shift_data_eq.
    - intro a.
      apply (lt_iso_to_id ua).
      apply (upshift_unique_up_to_lt_iso M (U1,,H1) (U2,,H2) a).
    - intro a; cbn.
      etrans; [apply lt_iso_to_id_precompose|].
      apply (force_unique_up_to_lt_iso M (U2,,H2) (U1,,H1) a).
  Qed.

  Lemma isaprop_has_positive_shifts (M : unital_magmoid)
    (ua : is_duploid_univalent M)
    : isaprop (has_positive_shifts M).
  Proof.
    apply isaproptotal2; [intro; apply isaprop_positive_shift_axioms|].
    intros U1 U2 H1 H2.
    use positive_shift_data_eq.
    - intro a.
      apply (lt_iso_to_id ua).
      apply (downshift_unique_up_to_lt_iso M (U1,,H1) (U2,,H2) a).
    - intro a; cbn.
      etrans; [apply lt_iso_to_id_postcompose|].
      apply (wrap_unique_up_to_lt_iso M (U2,,H2) (U1,,H1) a).
  Qed.

  Lemma isaprop_has_polarity_shifts (M : unital_magmoid) (ua : is_duploid_univalent M)
    : isaprop (has_polarity_shifts M).
  Proof.
    apply isapropdirprod.
    - apply isaprop_has_negative_shifts, ua.
    - apply isaprop_has_positive_shifts, ua.
  Qed.
End univalence_consequences.

Section equivalences.
  Context (D D' : duploid).
  Hypothesis (ua : is_duploid_univalent D) (ua' : is_duploid_univalent D').

  (** Two univalent duploids are identical if their objects are *)
  Lemma duploid_eq_from_univalent (H1 : (D : precategory_data) = D') : D = D'.
  Proof.
    apply subtypePath'; [|apply isaprop_has_polarity_shifts, ua'].
    apply subtypePath'; [|apply isaprop_has_polarities].
    apply subtypePath'; [|apply isaprop_has_homsets].
    apply subtypePath'; [|apply isaprop_is_unital_premagmoid, unital_magmoid_has_homsets].
    apply H1.
  Defined.

  Lemma isweq_on_objects_from_equivalence (F : duploid_equivalence D D')
    : isweq (functor_on_objects F).
  Proof.
    use isweq_iso.
    - exact (functor_on_objects (duploid_equivalence_inverse F)).
    - intro a; apply ua.
      exact (lt_surjective_inverse_ob_iso _ (duploid_equivalence_inverse F) a).
    - intro a; apply ua'.
      exact (lt_surjective_inverse_ob_iso _ F a).
  Defined.

  Lemma catiso_from_duploid_equivalence (F : duploid_equivalence D D')
    : catiso D D'.
  Proof.
    exists F.
    split.
    - exact F.
    - apply isweq_on_objects_from_equivalence.
  Defined.

  Lemma duploid_eq_from_duploid_equivalence (F : duploid_equivalence D D') : D = D'.
  Proof.
    apply duploid_eq_from_univalent.
    apply precategory_data_path_from_catiso.
    apply catiso_from_duploid_equivalence, F.
  Defined.

End equivalences.

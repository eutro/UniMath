(********************************************************************************

 The Algebra Duploid arising from an Adjunction

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition of the algebra duploid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.Comonads.

Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Oblique.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Envelope.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

Section algebra_defs.

  (** ** 1. Definition of the envelope duploid *)

  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let HFG : are_adjoints L R := θ.
  Let η : functor_identity P ⟹ L ∙ R := unit_from_are_adjoints HFG.
  Let ε : R ∙ L ⟹ functor_identity N := counit_from_are_adjoints HFG.

  Let T := Monad_from_adjunction HFG.
  Let U := Comonad_from_adjunction HFG.

  Local Notation "a '⁻'" := (envelope_negative_ob θ a) : duploid.
    (* type in Emacs with agda-input using \^- *)
  Local Notation "a '⁺'" := (envelope_positive_ob θ a) : duploid.
    (* type in Emacs with agda-input using \^+ *)
  Local Notation "a '►'" := (envelope_cross_mor θ a) : duploid.
    (* type in Emacs with agda-input using \t *)
  Local Notation "a '▻'" := (envelope_cross_mor' θ a) : duploid.
    (* type in Emacs with agda-input using \t *)

  (** A pre-object of the algebra. *)
  Definition algebra_data (a : envelope_preob θ) : UU
    := N⟦a⁻, L a⁺⟧ × P⟦R a⁻, a⁺⟧.

  Definition algebra_alg_mor {a : envelope_preob θ} (α : algebra_data a) : N⟦a⁻, L a⁺⟧ := pr1 α.
  Definition algebra_coalg_mor {a : envelope_preob θ} (α : algebra_data a) : P⟦R a⁻, a⁺⟧ := pr2 α.
  Local Notation "a '◄'" := (algebra_alg_mor a) : duploid.
    (* type in Emacs with agda-input using \t *)
  Local Notation "a '◅'" := (algebra_coalg_mor a) : duploid.
    (* type in Emacs with agda-input using \t *)

  Definition algebra_semiob_data := total2 algebra_data.

  Definition is_algebra_semiob (a : envelope_preob θ) (α : algebra_data a) : UU
    := is_retraction (α◄) (a►) × is_retraction (a▻) (α◅).

  Definition is_algebra_positive (a : envelope_preob θ) (α : algebra_data a) : UU
    := is_retraction (a►) (α◄).

  Definition is_algebra_negative (a : envelope_preob θ) (α : algebra_data a) : UU
    := is_retraction (α◅) (a▻).

  Definition algebra_semiob : UU
    := ∑ (a : envelope_preob θ) (α : algebra_data a), is_algebra_semiob a α.
  Coercion algebra_semiob_to_envelope_preob (a : algebra_semiob) : envelope_preob θ := pr1 a.
  Coercion algebra_semiob_to_algebra_data (a : algebra_semiob) : algebra_data a := pr12 a.
  Coercion algebra_semiob_is_algebra_semiob (a : algebra_semiob) : is_algebra_semiob a a := pr22 a.

  Definition positive_semiob (p : P) : algebra_semiob.
  Proof.
    use (_,,_,,_).
    - apply envelope_preob_of_positive, (R (L p)).
    - use (_,,_).
      + apply identity.
      + apply (μ T p).
    - use (_,,_).
      + abstract (apply id_left).
      + abstract (intermediate_path (η (T p) · μ T p);
                  [ apply cancel_postcomposition, (φ_adj_identity θ)
                  | apply (Monad_law1 (T:=T) p) ]).
  Defined.

  Definition positive_semiob_is_positive (p : P)
    : is_algebra_positive _ (positive_semiob p).
  Proof. apply id_left. Qed.

  Lemma φ_adj_inv_identity (n : N) : φ_adj_inv θ (identity (R n)) = ε _.
  Proof.
    unfold φ_adj_inv.
    refine (_ @ id_left _).
    apply cancel_postcomposition, functor_id.
  Qed.

  Definition negative_semiob (n : N) : algebra_semiob.
  Proof.
    use (_,,_,,_).
    - apply envelope_preob_of_negative, (L (R n)).
    - use (_,,_).
      + apply (δ U n).
      + apply identity.
    - use (_,,_).
      + abstract (intermediate_path (δ U n · ε (U n));
                  [ apply cancel_precomposition, φ_adj_inv_identity
                  | apply (Comonad_law1 (T:=U) n) ]).
      + abstract (refine (_ @ id_right _);
                  apply cancel_postcomposition, φ_adj_after_φ_adj_inv).
  Defined.

  Definition negative_semiob_is_negative (n : N)
    : is_algebra_negative _ (negative_semiob n).
  Proof.
    etrans; [apply cancel_precomposition, φ_adj_after_φ_adj_inv|].
    apply id_right.
  Qed.

  Definition algebra_ob :=
    ∑ a : algebra_semiob,
        ∥ is_algebra_negative _ a ⨿ is_algebra_positive _ a ∥.

  Definition algebra_ob_to_envelope_ob (a : algebra_ob) : envelope_ob θ.
  Proof.
    use make_envelope_ob.
    - exact (pr1 a).
    - refine (factor_through_squash _ (λ H, _) (pr2 a)).
      1: apply isaprop_envelope_polarization.
      induction H as [Hn | Hp]; apply hinhpr.
      + left; exists ((pr1 a)◅); split.
        * apply ((pr1 a) : is_algebra_semiob _ _).
        * apply Hn.
      + right; exists ((pr1 a)◄); split.
        * apply Hp.
        * apply ((pr1 a) : is_algebra_semiob _ _).
  Defined.

  Lemma positive_in_oblique_to_is_algebra_positive (n : N)
    (H : is_positive (M:=oblique_duploid θ) (oblique_negative θ n))
    : is_algebra_positive _ (negative_semiob n).
  Proof.
    apply is_positive_oblique_negative_iff_pre_fixed_point in H.
    change (#U (ε n) = ε (U n)) in H.
    intermediate_path (ε (U n) · δ U n).
    1: apply cancel_postcomposition, φ_adj_inv_identity.
    intermediate_path (δ U (U n) · #U (ε (U n))).
    2: apply (Comonad_law2 (T:=U) (U n)).
    rewrite <- H.
    apply (nat_trans_ax (δ U) _ n).
  Qed.

  Lemma negative_in_oblique_to_is_algebra_negative (p : P)
    (H : is_negative (M:=oblique_duploid θ) (oblique_positive θ p))
    : is_algebra_negative _ (positive_semiob p).
  Proof.
    (* unfold is_algebra_negative, is_retraction, envelope_cross_mor', envelope_mor_to_', envelope_cross_mor;
      cbn. *)
    apply is_negative_oblique_positive_iff_pre_fixed_point in H.
    change (#T (η p) = η (T p)) in H.
    intermediate_path (μ T p · η (T p)).
    1: apply cancel_precomposition, (φ_adj_identity θ).
    intermediate_path (# T (η (T p)) · μ T (T p)).
    2: apply (Monad_law2 (T:=T) (T p)).
    rewrite <- H.
    apply pathsinv0, (nat_trans_ax (μ T) p).
  Qed.

  (* TODO: clean up this file *)

End algebra_defs.

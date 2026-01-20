(********************************************************************************

 Functors of Duploids

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition of a linearity and thunkability preserving functor
 2. Definition of a (pre)duploid functor

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

(** ** 1. Definition of a linearity and thunkability preserving functor *)

Section functor_defs.
  Context {M M' : unital_premagmoid} (F : functor_data M M').
  Hypothesis (hs : has_homsets M').

  (** Preserving linearity *)
  Definition preserves_linearity : UU
    := ∏ (a b : M) (f : a --> b), is_linear f -> is_linear (#F f).

  Lemma isaprop_preserves_linearity' : isaprop preserves_linearity.
  Proof.
    do 4 (apply impred; intro).
    apply isaprop_is_linear', hs.
  Qed.

  Lemma functor_linear' (H : preserves_linearity) {a b : M} (f : a --> b)
    : is_linear f -> is_linear (#F f).
  Proof. apply H. Defined.

  (** Preserving thunkability *)
  Definition preserves_thunkability : UU
    := ∏ (a b : M) (f : a --> b), is_thunkable f -> is_thunkable (#F f).

  Lemma isaprop_preserves_thunkability' : isaprop preserves_thunkability.
  Proof.
    do 4 (apply impred; intro).
    apply isaprop_is_thunkable', hs.
  Qed.

  Lemma functor_thunkable' (H : preserves_thunkability) {a b : M} (f : a --> b)
    : is_thunkable f -> is_thunkable (#F f).
  Proof. apply H. Defined.

  (** Preserving linearity and also thunkability *)
  Definition preserves_linearity_and_thunkability : UU
    := preserves_linearity × preserves_thunkability.
  Definition make_preserves_linearity_and_thunkability
    (H1 : preserves_linearity)
    (H2 : preserves_thunkability)
    : preserves_linearity_and_thunkability
    := H1,,H2.
  Coercion preserves_linearity_and_thunkability_to_preserves_linearity
    (H : preserves_linearity_and_thunkability) : preserves_linearity := pr1 H.
  Coercion preserves_linearity_and_thunkability_to_preserves_thunkability
    (H : preserves_linearity_and_thunkability) : preserves_thunkability := pr2 H.

  Lemma isaprop_preserves_linearity_and_thunkability' :
    isaprop preserves_linearity_and_thunkability.
  Proof.
    apply isofhleveldirprod.
    - apply isaprop_preserves_linearity'.
    - apply isaprop_preserves_thunkability'.
  Qed.

  Lemma functor_linear_and_thunkable'
    (H : preserves_linearity_and_thunkability) {a b : M} (f : a --> b)
    : is_linear_and_thunkable f -> is_linear_and_thunkable (#F f).
  Proof.
    intro H'; induction H' as [Hlinear Hthunkable].
    apply make_is_linear_and_thunkable.
    - exact (functor_linear' H _ Hlinear).
    - exact (functor_thunkable' H _ Hthunkable).
  Defined.

End functor_defs.

Section functor_defs.
  (** Versions of above [isaprop] lemmas without the hypothesis. *)

  Context {M : unital_premagmoid} {M' : unital_magmoid} (F : M ⟶ M').

  Lemma isaprop_preserves_linearity : isaprop (preserves_linearity F).
  Proof. apply isaprop_preserves_linearity', unital_magmoid_has_homsets. Qed.

  Lemma isaprop_preserves_thunkability : isaprop (preserves_thunkability F).
  Proof. apply isaprop_preserves_thunkability', unital_magmoid_has_homsets. Qed.

  Lemma isaprop_preserves_linearity_and_thunkability : isaprop (preserves_linearity_and_thunkability F).
  Proof. apply isaprop_preserves_linearity_and_thunkability', unital_magmoid_has_homsets. Qed.

End functor_defs.

Section functor_defs.
  Lemma preserves_linearity_identity (M : unital_premagmoid) : preserves_linearity (functor_identity M).
  Proof. intros a b f H. exact H. Qed.

  Lemma preserves_linearity_comp {M₁ M₂ M₃ : unital_premagmoid}
    (F : functor_data M₁ M₂) (G : functor_data M₂ M₃)
    (HF : preserves_linearity F) (HG : preserves_linearity G)
    : preserves_linearity (functor_composite_data F G).
  Proof.
    intros a b f H.
    apply (functor_linear' _ HG).
    apply (functor_linear' _ HF).
    assumption.
  Qed.

  Lemma preserves_thunkability_identity (M : unital_premagmoid) : preserves_thunkability (functor_identity M).
  Proof. intros a b f H. exact H. Qed.

  Lemma preserves_thunkability_comp {M₁ M₂ M₃ : unital_premagmoid}
    (F : functor_data M₁ M₂) (G : functor_data M₂ M₃)
    (HF : preserves_thunkability F) (HG : preserves_thunkability G)
    : preserves_thunkability (functor_composite_data F G).
  Proof.
    intros a b f H.
    apply (functor_thunkable' _ HG).
    apply (functor_thunkable' _ HF).
    assumption.
  Qed.

  Lemma preserves_linearity_and_thunkability_identity (M : unital_premagmoid)
    : preserves_linearity_and_thunkability (functor_identity M).
  Proof.
    apply make_preserves_linearity_and_thunkability.
    - apply preserves_linearity_identity.
    - apply preserves_thunkability_identity.
  Qed.

  Lemma preserves_linearity_and_thunkability_comp {M₁ M₂ M₃ : unital_premagmoid}
    (F : functor_data M₁ M₂) (G : functor_data M₂ M₃)
    (HF : preserves_linearity_and_thunkability F) (HG : preserves_linearity_and_thunkability G)
    : preserves_linearity_and_thunkability (functor_composite_data F G).
  Proof.
    apply make_preserves_linearity_and_thunkability.
    - apply preserves_linearity_comp.
      + apply HF.
      + apply HG.
    - apply preserves_thunkability_comp.
      + apply HF.
      + apply HG.
  Qed.

End functor_defs.

(** ** 2. Definition of a (pre)duploid functor *)

(** *** 1. Definitions of duploid functor *)
Definition duploid_functor (M M' : unital_premagmoid) : UU
  := ∑ (f : M ⟶ M'), preserves_linearity_and_thunkability f.
Notation "M '⟶d' M'" := (duploid_functor M M') (at level 39) : duploid.
Coercion duploid_functor_to_functor {M M' : unital_premagmoid}
  (F : M ⟶d M') : M ⟶ M' := pr1 F.
Coercion duploid_functor_preserves_linearity_and_thunkability {M M' : unital_premagmoid}
  (F : M ⟶d M') : preserves_linearity_and_thunkability F := pr2 F.

Lemma duploid_functor_eq {M : unital_premagmoid} {M' : unital_magmoid}
  (F F' : M ⟶d M')
  (H : (F : functor _ _) = F')
  : F = F'.
Proof.
  refine (subtypePath' _ (isaprop_preserves_linearity_and_thunkability _)).
  apply H.
Defined.

Section duploid_functor.
  Context {M M' : unital_premagmoid}.

  Definition make_duploid_functor
    (F : M ⟶ M')
    (H : preserves_linearity_and_thunkability F)
    : M ⟶d M' := F,,H.

  (** *** 2. Lemmas about duploid functors *)

  Lemma functor_linear (F : M ⟶d M') {a b : M} (f : a --> b)
    : is_linear f -> is_linear (#F f).
  Proof. apply functor_linear', F. Defined.

  Lemma functor_thunkable (F : M ⟶d M') {a b : M} (f : a --> b)
    : is_thunkable f -> is_thunkable (#F f).
  Proof. apply functor_thunkable', F. Defined.

  Lemma functor_linear_and_thunkable (F : M ⟶d M') {a b : M} (f : a --> b)
    : is_linear_and_thunkable f -> is_linear_and_thunkable (#F f).
  Proof. apply functor_linear_and_thunkable', F. Defined.
End duploid_functor.

Definition duploid_functor_identity (M : unital_premagmoid) : duploid_functor M M
  := make_duploid_functor (functor_identity M) (preserves_linearity_and_thunkability_identity M).

Definition duploid_functor_comp {M₁ M₂ M₃ : unital_premagmoid}
  (F : duploid_functor M₁ M₂) (G : duploid_functor M₂ M₃)
  : duploid_functor M₁ M₃
  := make_duploid_functor (F ∙ G)
       (preserves_linearity_and_thunkability_comp F G F G).

Section duploid_functor.
  Context {M M' : unital_magmoid}.

  (** Restriction of a duploid functor to linear morphisms. *)
  Lemma duploid_functor_to_linear (F : M ⟶d M') : M ₗ ⟶ M' ₗ.
  Proof.
    use make_functor.
    - use make_functor_data.
      + cbn; intro a; exact (F a).
      + cbn; intros a b f.
        use (make_linear_mor (#F f)).
        apply functor_linear, f.
    - abstract (use make_is_functor;
                [ intro a; apply carrier_eq; apply functor_id
                | intros a b c f g; apply carrier_eq; apply functor_comp ]).
  Defined.

  (** Restriction of a duploid functor to thunkable morphisms. *)
  Lemma duploid_functor_to_thunkable (F : M ⟶d M') : M ₜ ⟶ M' ₜ.
  Proof.
    use make_functor.
    - use make_functor_data.
      + cbn; intro a; exact (F a).
      + cbn; intros a b f.
        use (make_thunkable_mor (#F f)).
        apply functor_thunkable, f.
    - abstract (use make_is_functor;
                [ intro a; apply carrier_eq; apply functor_id
                | intros a b c f g; apply carrier_eq; apply functor_comp ]).
  Defined.

End duploid_functor.

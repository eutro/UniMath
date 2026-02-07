(********************************************************************************

 Functors of Duploids

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition of a linearity and thunkability preserving functor
 2. Definition of a (pre)duploid functor
 3. Properties of (pre)duploid functors

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Isos.

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

(** ** 3. Properties of (pre)duploid functors *)

Section equivalences.
  Definition lt_essentially_surjective {C : precategory_data} {D : unital_magmoid} (F : functor_data C D) : UU
    := ∏ (b : D), ∃ (a : C), lt_iso (F a) b.

  Definition is_weak_duploid_equivalence {D D' : unital_magmoid} (F : D ⟶ D') : UU
    := fully_faithful F × lt_essentially_surjective F.
  Coercion is_weak_duploid_equivalence_to_fully_faithful {D D' : unital_magmoid} (F : D ⟶ D')
    (H : is_weak_duploid_equivalence F) : fully_faithful F := pr1 H.
  Coercion is_weak_duploid_equivalence_to_lt_essentially_surjective {D D' : unital_magmoid} (F : D ⟶ D')
    (H : is_weak_duploid_equivalence F) : lt_essentially_surjective F := pr2 H.
  Definition make_is_weak_duploid_equivalence {D D' : unital_magmoid} (F : D ⟶ D')
    (H1 : fully_faithful F) (H2 : lt_essentially_surjective F)
    : is_weak_duploid_equivalence F
    := H1,,H2.

  Definition weak_duploid_equivalence (D D' : unital_magmoid)
    := ∑ (F : D ⟶ D'), is_weak_duploid_equivalence F.
  Coercion weak_duploid_equivalence_functor {D D' : unital_magmoid}
    (F : weak_duploid_equivalence D D') : D ⟶ D' := pr1 F.
  Coercion weak_duploid_equivalence_is_weak_duploid_equivalence {D D' : unital_magmoid}
    (F : weak_duploid_equivalence D D') : is_weak_duploid_equivalence F := pr2 F.
  Definition make_weak_duploid_equivalence {D D' : unital_magmoid}
    (F : D ⟶ D') (H : is_weak_duploid_equivalence F)
    : weak_duploid_equivalence D D' := F,,H.

  Definition split_lt_essentially_surjective {C : precategory_data} {D : unital_magmoid} (F : functor_data C D) : UU
    := ∏ (b : D), ∑ (a : C), lt_iso (F a) b.

  Definition lt_surjective_inverse_ob {C : precategory_data} {D : unital_magmoid}
    (F : functor_data C D) (H : split_lt_essentially_surjective F) (b : D) : C := pr1 (H b).
  Definition lt_surjective_inverse_ob_iso {C : precategory_data} {D : unital_magmoid}
    (F : functor_data C D) (H : split_lt_essentially_surjective F) (b : D)
    : lt_iso (F (lt_surjective_inverse_ob F H b)) b := pr2 (H b).

  Definition is_duploid_equivalence {D D' : unital_magmoid} (F : D ⟶ D') : UU
    := fully_faithful F × split_lt_essentially_surjective F.
  Coercion is_duploid_equivalence_to_fully_faithful {D D' : unital_magmoid} (F : D ⟶ D')
    (H : is_duploid_equivalence F) : fully_faithful F := pr1 H.
  Coercion is_duploid_equivalence_to_split_lt_essentially_surjective {D D' : unital_magmoid} (F : D ⟶ D')
    (H : is_duploid_equivalence F) : split_lt_essentially_surjective F := pr2 H.
  Definition make_is_duploid_equivalence {D D' : unital_magmoid} (F : D ⟶ D')
    (H1 : fully_faithful F) (H2 : split_lt_essentially_surjective F)
    : is_duploid_equivalence F
    := H1,,H2.

  Definition duploid_equivalence (D D' : unital_magmoid)
    := ∑ (F : D ⟶ D'), is_duploid_equivalence F.
  Coercion duploid_equivalence_functor {D D' : unital_magmoid}
    (F : duploid_equivalence D D') : D ⟶ D' := pr1 F.
  Coercion duploid_equivalence_is_duploid_equivalence {D D' : unital_magmoid}
    (F : duploid_equivalence D D') : is_duploid_equivalence F := pr2 F.
  Definition make_duploid_equivalence {D D' : unital_magmoid}
    (F : D ⟶ D') (H : is_duploid_equivalence F)
    : duploid_equivalence D D' := F,,H.

  Coercion duploid_equivalence_to_weak_duploid_equivalence {D D' : unital_magmoid}
    (F : duploid_equivalence D D') : weak_duploid_equivalence D D'.
  Proof.
    use make_weak_duploid_equivalence.
    - exact F.
    - use make_dirprod.
      + exact F.
      + intros a.
        apply hinhpr.
        apply (F : split_lt_essentially_surjective _).
  Defined.

  Definition is_duploid_equivalence_to_inverse_functor_data {M M' : preduploid}
    (F : M ⟶ M') (H : is_duploid_equivalence F) : functor_data M' M.
  Proof.
    use make_functor_data.
    - intro a.
      exact (lt_surjective_inverse_ob F H a).
    - intros a b f; cbn.
      apply (fully_faithful_inv_hom H).
      exact (lt_surjective_inverse_ob_iso F H a · f ·
               lt_iso_inverse (lt_surjective_inverse_ob_iso F H b)).
  Defined.

  Lemma is_duploid_equivalence_to_inverse_is_functor  {M M' : preduploid}
    (F : M ⟶ M') (H : is_duploid_equivalence F)
    : is_functor (is_duploid_equivalence_to_inverse_functor_data F H).
  Proof.
    use make_is_functor.
    - intro a; cbn.
      apply pathsinv0, pathsweq1, pathsinv0.
      etrans; [apply cancel_postcomposition, magmoid_id_right|].
      etrans; [apply lt_iso_is_inverse|].
      apply pathsinv0, functor_id.
    - intros a b c g f; cbn.
      apply pathsinv0, pathsweq1, pathsinv0.
      etrans. {
        apply cancel_postcomposition, cancel_precomposition.
        apply pathsinv0, (preduploid_lt_iso_inv_interpose (lt_surjective_inverse_ob_iso F H b)).
      }
      etrans; [|apply pathsinv0, (functor_comp F)].
      etrans; [|apply cancel_postcomposition, pathsinv0, (homotweqinvweq (weq_from_fully_faithful H _ _))].
      etrans; [|apply cancel_precomposition, pathsinv0, (homotweqinvweq (weq_from_fully_faithful H _ _))].
      etrans; [apply cancel_postcomposition, assoc_thunkable, (lt_surjective_inverse_ob_iso F H a)|].
      etrans; [apply assoc'_linear, (lt_iso_inverse _)|].
      apply cancel_postcomposition.
      apply assoc_linear, (lt_iso_inverse _).
  Qed.

  Definition is_duploid_equivalence_to_inverse_functor {M M' : preduploid}
    (F : M ⟶ M') (H : is_duploid_equivalence F)
    : M' ⟶ M := make_functor _ (is_duploid_equivalence_to_inverse_is_functor F H).

End equivalences.

Section full.
  Context {M : unital_premagmoid} {D : preduploid} (F : M ⟶ D).
  Hypothesis (Hfull : full F) (Hltsurj : lt_essentially_surjective F).

  Lemma preserves_linearity_of_full_and_lt_essentially_surjective : preserves_linearity F.
  Proof.
    intros a b f Hf c d g h.
    isaprop_goal Hprop; [apply unital_magmoid_has_homsets|].
    refine (factor_through_squash Hprop (λ Hc, _) (Hltsurj c)).
    refine (factor_through_squash Hprop (λ Hd, _) (Hltsurj d)).
    induction Hc as [c' Hc'], Hd as [d' Hd'].
    refine (factor_through_squash Hprop (λ Hh, _) (Hfull _ _ (Hd' · h · lt_iso_inverse Hc'))).
    refine (factor_through_squash Hprop (λ Hg, _) (Hfull _ _ (Hc' · g))).
    induction Hh as [h' Hh'], Hg as [g' Hg'].
    rewrite <- (preduploid_lt_iso_inv_interpose Hc' h g).
    rewrite <- (preduploid_lt_iso_inv_interpose Hc' h (g · #F f)).
    apply (cancel_lt_iso_left Hd').
    rewrite !(assoc_thunkable _ Hd'), !(assoc_thunkable _ Hc').
    cbn; rewrite <- Hh', <- Hg', <- !functor_comp.
    apply maponpaths, assoc'_linear, Hf.
  Qed.

  Lemma preserves_thunkability_of_full_and_lt_essentially_surjective : preserves_thunkability F.
  Proof.
    intros a b f Hf c d g h.
    isaprop_goal Hprop; [apply unital_magmoid_has_homsets|].
    refine (factor_through_squash Hprop (λ Hc, _) (Hltsurj c)).
    refine (factor_through_squash Hprop (λ Hd, _) (Hltsurj d)).
    induction Hc as [c' Hc'], Hd as [d' Hd'].
    refine (factor_through_squash Hprop (λ Hh, _) (Hfull _ _ (Hc' · (h · lt_iso_inverse Hd')))).
    refine (factor_through_squash Hprop (λ Hg, _) (Hfull _ _ (g · lt_iso_inverse Hc'))).
    induction Hh as [h' Hh'], Hg as [g' Hg'].
    rewrite <- (preduploid_lt_iso_inv_interpose Hc' g h).
    rewrite <- (preduploid_lt_iso_inv_interpose Hc' (#F f · g) h).
    apply (cancel_lt_iso_right (lt_iso_inv Hd')).
    rewrite !(assoc'_linear _ (lt_iso_inv Hd')).
    rewrite !(assoc'_linear _ (lt_iso_inverse Hc')).
    cbn; rewrite <- Hh', <- Hg', <- !functor_comp.
    apply maponpaths, assoc_thunkable, Hf.
  Qed.

  Theorem full_and_lt_essentially_surjective_preserves_linearity_and_thunkability
    : preserves_linearity_and_thunkability F.
  Proof.
    use make_preserves_linearity_and_thunkability.
    - apply preserves_linearity_of_full_and_lt_essentially_surjective.
    - apply preserves_thunkability_of_full_and_lt_essentially_surjective.
  Qed.

End full.

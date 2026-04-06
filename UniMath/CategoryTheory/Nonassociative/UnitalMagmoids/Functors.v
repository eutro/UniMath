(********************************************************************************

 Functors of Unital Magmoids

 Author: B. Szilvasy
 January 2026

 The ordinary definition of a [functor] defines the appropriate notion of
 homomorphism of unital magmoids. However, numerous maps between unital magmoids
 fail to satisfy the composition axiom [functor_compax], while still satisfying
 the identity axiom [functor_idax]. We call such maps "reflexive graph
 functors", or [rxfunctor]s, because they are the homomorphisms between the
 underlying reflexive graphs if we forget the composition operator of a unital
 magmoid.

 The ordinary definition of [nat_trans] also works for [rxfunctor]s between
 unital magmoids (though it is still too strong sometimes). Such natural
 transformations do not compose in general however, as [nat_trans_comp] requires
 associativity.

 Contents:
 1. Definition of a reflexive graph functor
 2. Definition of the submagmoid in the image of a functor

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.

Local Open Scope cat.
Local Open Scope unital_magmoid.

(** ** 1. Definition of a reflexive graph functor *)
Section rxfunctor_defs.
  Definition rxfunctor (M M' : unital_premagmoid_data) : UU
    := ∑ (F : functor_data M M'), functor_idax F.

  (** Constructor and projections *)
  Definition make_rxfunctor {M M' : unital_premagmoid_data}
    (F : functor_data M M') (H : functor_idax F)
    : rxfunctor M M' := F,,H.
  Coercion rxfunctor_to_functor_data {M M' : unital_premagmoid_data} (F : rxfunctor M M')
    : functor_data M M' := pr1 F.
  Definition rxfunctor_id {M M' : unital_premagmoid_data} (F : rxfunctor M M')
    : functor_idax F (* [∏ a : M, #F (identity a) = identity (F a)] *) := pr2 F.

  (** Conversions to and from [functor] *)
  Coercion functor_to_rxfunctor {M M' : unital_premagmoid_data} (F : functor M M')
    : rxfunctor M M' := make_rxfunctor F (pr12 F).

  Definition make_functor_from_rxfunctor {M M' : unital_premagmoid_data}
    (F : rxfunctor M M') (H : functor_compax F) : functor M M'.
  Proof.
    use (make_functor F); use make_is_functor.
    - exact (rxfunctor_id F).
    - exact H.
  Qed.
End rxfunctor_defs.

Notation "M '⟶¹' M'" := (rxfunctor M M') (at level 39) : unital_magmoid.
  (* type in Emacs using agda-input with \--> \^1 *)

Section rxfunctor_ops.
  (** Being a [rxfunctor] is a property if the codomain has homsets *)
  Definition isaprop_functor_idax' {M M' : unital_premagmoid_data}
    (hs : has_homsets M') (F : functor_data M M') : isaprop (functor_idax F).
  Proof.
    apply impred; intro.
    apply hs.
  Qed.

  Definition isaprop_functor_idax {M : unital_premagmoid_data} {M' : unital_magmoid}
    (hs : has_homsets M') (F : functor_data M M') : isaprop (functor_idax F).
  Proof. apply isaprop_functor_idax', unital_magmoid_has_homsets. Qed.

  (** There is an identity [rxfunctor] on *any* unital premagmoid *)
  Definition rxfunctor_identity (M : unital_premagmoid_data) : M ⟶¹ M
    := functor_identity M.

  (** Composition preserves identities, even without associativity *)
  Lemma functor_idax_compose {M₁ M₂ M₃ : unital_premagmoid_data}
    (F : functor_data M₁ M₂) (G : functor_data M₂ M₃)
    : functor_idax F -> functor_idax G -> functor_idax (functor_composite_data F G).
  Proof.
    intros HF HG a.
    exact (maponpaths _ (HF a) @ HG (F a)).
  Defined.

  Definition rxfunctor_compose {M₁ M₂ M₃ : unital_premagmoid_data}
    (F : M₁ ⟶¹ M₂) (G : M₂ ⟶¹ M₃) : M₁ ⟶¹ M₃
    := make_rxfunctor _ (functor_idax_compose _ _ (rxfunctor_id F) (rxfunctor_id G)).
End rxfunctor_ops.

(** ** 2. Definition of the submagmoid in the image of a functor

 The full unital premagmoid in the image of [F : M ⟶ M'] has objects of the form
 [F a : M'] for objects [a : M], with morphisms and composition given by those
 in [M']. *)

Section functor_image.
  Context {M M' : unital_premagmoid} (F : functor_data M M').
  Hypothesis (hs : has_homsets M').

  Definition functor_full_image_premagmoid_data : unital_premagmoid_data.
  Proof.
    use make_precategory_data.
    - use (make_precategory_ob_mor (image F)).
      intros a b; exact (M'⟦pr1 a, pr1 b⟧).
    - intro a; exact (identity (pr1 a)).
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

  Definition ob_in_functor_full_image (a : M)
    : ob functor_full_image_premagmoid
    := prtoimage _ a.

  Definition morphism_in_functor_full_image {a b : M} (f : a --> b)
    : functor_full_image_premagmoid⟦ob_in_functor_full_image a, ob_in_functor_full_image b⟧
    := #F f.

End functor_image.

Definition functor_full_image_magmoid
  {M : unital_premagmoid} {M' : unital_magmoid} (F : M ⟶ M') : unital_magmoid.
Proof. apply (functor_full_image_magmoid' F), unital_magmoid_has_homsets. Defined.

Section functor_facts.
  Context {M : unital_premagmoid} {M' : unital_magmoid} (F : M ⟶ M').
  Hypothesis (Hfull : full F) (Hff : fully_faithful F).

  (** F applied to a linear morphism is not necessarily linear in the codomain
      of F, even if it is full, as there may extra objects in the codomain
      unrelated to those in F's image. *)
  Lemma is_linear_in_full_functor {a b : M} (f : a --> b)
    (H : is_linear f) : is_linear (#F f).
  Proof.
    intros c d g h.
    Fail Check (Hfull _ _ h). (* Fails because h is not of the form M'⟦F _, F _⟧ *)
  Abort.

  (** However, once restricted to the full subcategory of objects in F's image, fullness is
      sufficient. *)
  Lemma is_linear_in_full_functor_image {a b : M} (f : a --> b)
    (Hlinear : is_linear f) : is_linear (morphism_in_functor_full_image F f).
  Proof.
    intros c d.
    (* Bookkeeping to consider c and d as some [F c'] and [F d']. *)
    isaprop_goal Hprop; [do 2 (apply impred; intro); apply unital_magmoid_has_homsets|].
    refine (factor_through_squash Hprop (λ Hc, _) (pr2 c)).
    refine (factor_through_squash Hprop (λ Hd, _) (pr2 d)).
    clear Hprop.
    induction Hc as [c' Hc'], Hd as [d' Hd']; cbn.
    induction Hc', Hd'.
    (* End of bookkeeping *)
    intros g h.
    isaprop_goal Hprop; [apply unital_magmoid_has_homsets|].
    refine (factor_through_squash Hprop (λ Hh, _) (Hfull _ _ h)).
    refine (factor_through_squash Hprop (λ Hg, _) (Hfull _ _ g)).
    induction Hh as [h' Hh'], Hg as [g' Hg'].
    rewrite <- Hh', <- Hg'; cbn.
    unfold morphism_in_functor_full_image.
    do 4 rewrite <- (functor_comp F).
    apply maponpaths, Hlinear.
  Qed.

  Lemma is_thunkable_in_full_functor_image {a b : M} (f : a --> b)
    (Hthunkable : is_thunkable f) : is_thunkable (morphism_in_functor_full_image F f).
  Proof.
    intros c d.
    (* Bookkeeping to consider c and d as some [F c'] and [F d']. *)
    isaprop_goal Hprop; [do 2 (apply impred; intro); apply unital_magmoid_has_homsets|].
    refine (factor_through_squash Hprop (λ Hc, _) (pr2 c)).
    refine (factor_through_squash Hprop (λ Hd, _) (pr2 d)).
    clear Hprop.
    induction Hc as [c' Hc'], Hd as [d' Hd']; cbn.
    induction Hc', Hd'.
    (* End of bookkeeping *)
    intros g h.
    isaprop_goal Hprop; [apply unital_magmoid_has_homsets|].
    refine (factor_through_squash Hprop (λ Hh, _) (Hfull _ _ h)).
    refine (factor_through_squash Hprop (λ Hg, _) (Hfull _ _ g)).
    induction Hh as [h' Hh'], Hg as [g' Hg'].
    rewrite <- Hh', <- Hg'; cbn.
    unfold morphism_in_functor_full_image.
    do 4 rewrite <- (functor_comp F).
    apply maponpaths, Hthunkable.
  Qed.

  Lemma is_linear_and_thunkable_in_full_functor_image {a b : M} (f : a --> b)
    (Hlt : is_linear_and_thunkable f)
    : is_linear_and_thunkable (morphism_in_functor_full_image F f).
  Proof.
    use make_is_linear_and_thunkable.
    - apply (is_linear_in_full_functor_image f Hlt).
    - apply (is_thunkable_in_full_functor_image f Hlt).
  Qed.

  (** Fully faithful functors reflect linearity and thunkability *)
  Lemma is_linear_from_fully_faithful_functor_image {a b : M} (f : F a --> F b)
    (Hlinear : is_linear f) : is_linear (fully_faithful_inv_hom Hff _ _ f).
  Proof.
    intros c d g h.
    apply (Injectivity (#F)).
    1: apply isweqonpathsincl, fully_faithful_implies_full_and_faithful, Hff.
    rewrite !functor_comp.
    etrans; [apply cancel_precomposition,
        (homotweqinvweq (weq_from_fully_faithful Hff a b) f)|].
    etrans; [|apply cancel_precomposition, cancel_precomposition,
              (!homotweqinvweq (weq_from_fully_faithful Hff a b) f)].
    apply assoc'_linear, Hlinear.
  Qed.

  Lemma is_thunkable_from_fully_faithful_functor_image {a b : M} (f : F a <-- F b)
    (Hthunkable : is_thunkable f) : is_thunkable (fully_faithful_inv_hom Hff _ _ f).
  Proof.
    intros c d g h.
    apply (Injectivity (#F)).
    1: apply isweqonpathsincl, fully_faithful_implies_full_and_faithful, Hff.
    rewrite !functor_comp.
    etrans; [apply cancel_postcomposition,
        (homotweqinvweq (weq_from_fully_faithful Hff b a) f)|].
    etrans; [|apply cancel_postcomposition, cancel_postcomposition,
              (!homotweqinvweq (weq_from_fully_faithful Hff b a) f)].
    apply assoc_thunkable, Hthunkable.
  Qed.

  Lemma is_linear_and_thunkable_from_fully_faithful_functor_image {a b : M} (f : F a --> F b)
    (Hlt : is_linear_and_thunkable f)
    : is_linear_and_thunkable (fully_faithful_inv_hom Hff _ _ f).
  Proof.
    use make_is_linear_and_thunkable.
    - apply (is_linear_from_fully_faithful_functor_image f Hlt).
    - apply (is_thunkable_from_fully_faithful_functor_image f Hlt).
  Qed.

End functor_facts.

Section functor_facts.
  Context {M M' : unital_magmoid} (F : M ⟶ M').
  Hypothesis (Hfull : full F) (Hff : fully_faithful F).

  Lemma is_lt_iso_from_fully_faithful_functor_image {a b : M} (f : F a --> F b)
    (Hlt_iso : is_lt_iso f) : is_lt_iso (M:=M) (fully_faithful_inv_hom Hff _ _ f).
  Proof.
    use make_is_lt_iso'.
    - abstract (apply is_linear_and_thunkable_from_fully_faithful_functor_image, Hlt_iso).
    - exact (fully_faithful_inv_hom Hff _ _ Hlt_iso).
    - abstract (apply is_linear_and_thunkable_from_fully_faithful_functor_image,
                 linear_and_thunkable_mor_is_linear_and_thunkable).
    - abstract (exact (inv_of_ff_inv_is_inv _ _ _ Hff _ _ (lt_iso_to_z_iso (make_lt_iso _ Hlt_iso)))).
  Defined.

  Lemma lt_iso_from_fully_faithful_functor_image {a b : M} (f : lt_iso (F a) (F b)) : lt_iso a b.
  Proof.
    eapply make_lt_iso, is_lt_iso_from_fully_faithful_functor_image.
    exact (lt_iso_is_lt_iso f).
  Defined.
End functor_facts.

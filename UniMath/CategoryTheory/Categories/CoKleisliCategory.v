(********************************************************************

 The CoKleisli category of a comonad.

 This is the dualization of [KleisliCategory.v]. The usual definition
 of the CoKleisli category found in `Monads.CoKleisliCategory.v` does
 not give rise to a univalent category. In this file, a weakly
 equivalent but univalent definition is given as a subcategory of the
 CoEilenbergMoore category.

 Contents
 1. The free coalgebra functor
 2. The univalent CoKleisli category
 3. The weak equivalence

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Categories.CoEilenbergMoore.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monads.CoKleisliCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecompEquivalence.

Local Open Scope cat.

(**
 1. The free coalgebra functor.
 *)
Section FreeCoalgebraFunctor.
  Context {C : category} (m : Comonad C).

  Definition free_coalg_em_data
    : functor_data C (co_eilenberg_moore_cat m).
  Proof.
    use make_functor_data.
    - refine (λ x, make_ob_co_eilenberg_moore m (m x) (δ m x) _ _).
      + apply Comonad_law1.
      + refine (!_).
        apply Comonad_law3.
    - simple refine (λ x y f, make_mor_co_eilenberg_moore _ _ _).
      + exact (#m f).
      + exact (!(nat_trans_ax (δ m) _ _ f)).
  Defined.

  Definition free_coalg_em_is_functor
    : is_functor free_coalg_em_data.
  Proof.
    split.
    - intro x.
      use eq_mor_co_eilenberg_moore ; cbn.
      apply functor_id.
    - intros x y z f g.
      use eq_mor_co_eilenberg_moore ; cbn.
      apply functor_comp.
  Qed.

  Definition free_coalg_em
    : C ⟶ co_eilenberg_moore_cat m.
  Proof.
    use make_functor.
    - exact free_coalg_em_data.
    - exact free_coalg_em_is_functor.
  Defined.
End FreeCoalgebraFunctor.

(**
 2. The univalent CoKleisli category
 *)
Definition cokleisli_cat
           {C : category}
           (m : Comonad C)
  : category
  := full_img_sub_precategory (free_coalg_em m).

Definition univalent_cokleisli_cat
           {C : univalent_category}
           (m : Comonad C)
  : univalent_category
  := @univalent_image
       C
       (co_eilenberg_moore_univalent_cat C m)
       (free_coalg_em m).

Definition is_z_iso_cokleisli_cat
           {C : category}
           (m : Comonad C)
           {x₁ x₂ : cokleisli_cat m}
           {f : x₁ --> x₂}
           (Hf : is_z_isomorphism (pr111 f))
  : is_z_isomorphism f.
Proof.
  use is_iso_full_sub.
  use is_z_iso_co_eilenberg_moore.
  exact Hf.
Defined.

Definition z_iso_cokleisli_cat
           {C : category}
           (m : Comonad C)
           {x₁ x₂ : cokleisli_cat m}
           (f : z_iso (pr1 x₁) (pr1 x₂))
  : z_iso x₁ x₂.
Proof.
  simple refine (_ ,, _).
  - exact (pr1 f ,, tt).
  - use is_iso_full_sub.
    exact (pr2 f).
Defined.

Definition from_z_iso_cokleisli_cat
           {C : category}
           (m : Comonad C)
           {x₁ x₂ : cokleisli_cat m}
           (f : z_iso x₁ x₂)
  : z_iso (pr111 x₁) (pr111 x₂).
Proof.
  use make_z_iso.
  - exact (pr1 (pr111 f)).
  - exact (pr111 (inv_from_z_iso f)).
  - split.
    + exact (maponpaths (λ z, pr111 z) (z_iso_inv_after_z_iso f)).
    + exact (maponpaths (λ z, pr111 z) (z_iso_after_z_iso_inv f)).
Defined.

Definition eq_mor_cokleisli_cat
           {C : category}
           (m : Comonad C)
           {x₁ x₂ : cokleisli_cat m}
           {f₁ f₂ : x₁ --> x₂}
           (p : pr111 f₁ = pr111 f₂)
  : f₁ = f₂.
Proof.
  use subtypePath.
  {
    intro.
    apply isapropunit.
  }
  use eq_mor_co_eilenberg_moore.
  exact p.
Qed.

Definition cokleisli_incl
           {C : category}
           (m : Comonad C)
  : C ⟶ cokleisli_cat m
  := functor_full_img _.

Definition cokleisli_nat_trans
           {C : category}
           (m : Comonad C)
  : cokleisli_incl m ⟹ m ∙ cokleisli_incl m.
Proof.
  use make_nat_trans.
  - intro x.
    simple refine (_ ,, tt).
    use make_mor_co_eilenberg_moore ; cbn.
    + exact (δ m x).
    + abstract
        (apply Comonad_law3).
  - abstract
      (intros x y f ;
       use eq_mor_cokleisli_cat ; cbn ;
       apply (nat_trans_ax (δ m))).
Defined.

(**
 3. The weak equivalence
 *)
Definition functor_to_cokleisli_cat_data
           {C : category}
           (m : Comonad C)
  : functor_data (Cokleisli_cat_monad m) (cokleisli_cat m).
Proof.
  use make_functor_data.
  - refine (λ x, free_coalg_em m x ,, hinhpr (x ,, _)).
    apply identity_z_iso.
  - refine (λ x y f, _ ,, tt).
    use make_mor_co_eilenberg_moore.
    + exact (δ m x · # m f).
    + abstract
        (cbn ;
         rewrite assoc' ;
         rewrite (nat_trans_ax (δ m)) ;
         rewrite functor_comp ;
         do 2 rewrite assoc ;
         apply (maponpaths (λ z, z · _)) ;
         apply Comonad_law3).
Defined.

Definition functor_to_cokleisli_cat_is_functor
           {C : category}
           (m : Comonad C)
  : is_functor (functor_to_cokleisli_cat_data m).
Proof.
  split.
  - intro x.
    use eq_mor_cokleisli_cat.
    cbn.
    apply Comonad_law2.
  - intros x y z f g.
    use eq_mor_cokleisli_cat.
    cbn ; unfold cobind.
    rewrite !functor_comp.
    etrans. {
      do 2 rewrite assoc.
      do 2 apply cancel_postcomposition.
      apply Comonad_law3.
    }
    etrans. {
      do 2 rewrite assoc'.
      apply cancel_precomposition.
      rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0.
      apply (nat_trans_ax (δ m)).
    }
    now do 3 rewrite assoc.
Qed.

Definition functor_to_cokleisli_cat
           {C : category}
           (m : Comonad C)
  : Cokleisli_cat_monad m ⟶ cokleisli_cat m.
Proof.
  use make_functor.
  - exact (functor_to_cokleisli_cat_data m).
  - exact (functor_to_cokleisli_cat_is_functor m).
Defined.

Definition functor_to_cokleisli_cat_incl_nat_trans
           {C : category}
           (m : Comonad C)
  : cokleisli_incl m
    ⟹
    Right_Cokleisli_functor m ∙ functor_to_cokleisli_cat m.
Proof.
  use make_nat_trans.
  - refine (λ x, make_mor_co_eilenberg_moore _ (identity _) _ ,, tt).
    abstract
      (cbn ;
       rewrite functor_id, id_left, id_right ;
       apply idpath).
  - abstract
      (intros x y f ;
       use eq_mor_cokleisli_cat ; cbn ;
       rewrite id_left, id_right ;
       rewrite functor_comp ;
       rewrite !assoc ;
       refine (!_) ;
       refine (_ @ id_left _) ;
       apply cancel_postcomposition ;
       apply Comonad_law2).
Defined.

Definition functor_to_cokleisli_cat_incl_nat_z_iso
           {C : category}
           (m : Comonad C)
  : nat_z_iso
      (cokleisli_incl m)
      (Right_Cokleisli_functor m ∙ functor_to_cokleisli_cat m).
Proof.
  use make_nat_z_iso.
  - exact (functor_to_cokleisli_cat_incl_nat_trans m).
  - intro.
    use is_z_iso_cokleisli_cat.
    apply is_z_isomorphism_identity.
Defined.

Definition full_functor_to_cokleisli_cat
           {C : category}
           (m : Comonad C)
  : full (functor_to_cokleisli_cat m).
Proof.
  intros x y f.
  apply hinhpr.
  simple refine (_ ,, _).
  - exact (pr111 f · ε m y).
  - use eq_mor_cokleisli_cat.
    cbn.
    rewrite functor_comp.
    rewrite !assoc.
    etrans.
    {
      apply cancel_postcomposition.
      exact (pr211 f).
    }
    cbn.
    rewrite assoc'.
    etrans.
    {
      apply maponpaths.
      apply Comonad_law2.
    }
    apply id_right.
Qed.

Definition faithful_functor_to_cokleisli_cat
           {C : category}
           (m : Comonad C)
  : faithful (functor_to_cokleisli_cat m).
Proof.
  intros x y f.
  use invproofirrelevance.
  intros ψ₁ ψ₂.
  use subtypePath.
  {
    intro.
    apply homset_property.
  }
  pose (pr2 ψ₁ @ !(pr2 ψ₂)) as p.
  cbn in p.
  pose (maponpaths (λ z, pr111 z · ε m _) p) as q.
  cbn in q.
  refine (_ @ q @ _).
  - refine (!_).
    rewrite assoc'.
    etrans.
    {
      apply maponpaths.
      exact ((nat_trans_ax (ε m) _ _ (pr1 ψ₁))).
    }
    cbn.
    rewrite assoc.
    etrans.
    {
      apply maponpaths_2.
      apply Comonad_law1.
    }
    apply id_left.
  - etrans.
    rewrite assoc'.
    {
      apply maponpaths.
      exact ((nat_trans_ax (ε m) _ _ (pr1 ψ₂))).
    }
    cbn.
    rewrite assoc.
    etrans.
    {
      apply maponpaths_2.
      apply Comonad_law1.
    }
    apply id_left.
Qed.

Definition fully_faithful_functor_to_cokleisli_cat
           {C : category}
           (m : Comonad C)
  : fully_faithful (functor_to_cokleisli_cat m).
Proof.
  use full_and_faithful_implies_fully_faithful.
  split.
  - exact (full_functor_to_cokleisli_cat m).
  - exact (faithful_functor_to_cokleisli_cat m).
Defined.

Definition essentially_surjective_functor_to_cokleisli_cat
           {C : category}
           (m : Comonad C)
  : essentially_surjective (functor_to_cokleisli_cat m).
Proof.
  intro x.
  induction x as [ x Hx ].
  revert Hx.
  use factor_dep_through_squash.
  - intro.
    apply isapropishinh.
  - intros Hx.
    apply hinhpr.
    refine (pr1 Hx ,, _).
    use z_iso_cokleisli_cat.
    exact (pr2 Hx).
Defined.

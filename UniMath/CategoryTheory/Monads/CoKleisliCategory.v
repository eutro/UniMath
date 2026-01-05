(** **********************************************************
The CoKleisli category of a comonad, dualization of [KleisliCategory.v].

Contents:
        - Definition of the CoKleisli category of a comonad.
        - The canonical adjunction between a category C and the
          CoKleisli category of a comonad on C.

Written by: B. Szilvasy (January 2026)
************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Section Comonad_Lemmas.

(*A couple of lemmas involving cobind*)

Lemma cobind_comp_ε {C : category} {T : Comonad C} {a b : C} (f : C ⟦a , b⟧) :
  cobind ((ε T) a · f) = # T f.
Proof.
  unfold cobind; rewrite functor_comp.
  rewrite <- assoc'.
  rewrite <- id_left.
  apply cancel_postcomposition.
  apply cobind_ε.
Qed.

Lemma cobind_identity {C : category} {T : Comonad C} (a : C) :
  cobind (identity (T a)) = (δ T) a.
Proof.
  unfold cobind.
  rewrite functor_id.
  apply id_right.
Qed.

End Comonad_Lemmas.

Section Cokleisli_Categories.

Definition Cokleisli_precat_ob_mor_monad {C : category} (T : Comonad C) :
  precategory_ob_mor.
Proof.
  use tpair.
  - exact (ob C).
  - intros X Y.
    exact (T X --> Y).
Defined.

Definition Cokleisli_precat_data_monad {C : category} (T : Comonad C) :
  precategory_data.
Proof.
  use make_precategory_data.
  - exact (Cokleisli_precat_ob_mor_monad T).
  - intro c.
    exact (ε T c).
  - intros a b c f g.
    exact ((cobind f) · g).
Defined.

Lemma Cokleisli_precat_monad_is_precat {C : category} (T : Comonad C) :
  is_precategory (Cokleisli_precat_data_monad T).
Proof.
  apply is_precategory_one_assoc_to_two.
  split.
  - split.
    + intros a b f.
      unfold identity; unfold compose; cbn.
      rewrite <- id_left.
      apply cancel_postcomposition.
      apply cobind_ε.
    + intros a b f.
      unfold identity; unfold compose; cbn.
      apply ε_cobind.
  - intros a b c d f g h.
    unfold compose; cbn.
    rewrite <- cobind_cobind.
    apply assoc.
Defined.

Definition Cokleisli_precat_monad {C : category} (T : Comonad C) : precategory := (Cokleisli_precat_data_monad T,,Cokleisli_precat_monad_is_precat T).

Lemma Cokleisli_precat_monad_has_homsets {C : category} (T : Comonad C)
      (hs : has_homsets C) : has_homsets (Cokleisli_precat_data_monad T).
Proof.
  intros a b.
  apply hs.
Defined.

Definition Cokleisli_cat_monad {C : category} (T : Comonad C): category
  := (Cokleisli_precat_monad T,, Cokleisli_precat_monad_has_homsets T
  (homset_property C)).

(*TODO: show that this is equivalent to the definition of the Cokleisli category of a relative monad with respect to the identity*)

(*The canonical adjunction between C and the Cokleisli category of a monad on C*)

Definition Right_Cokleisli_functor_data {C : category} (T: Comonad C) :
  functor_data C (Cokleisli_precat_monad T).
Proof.
  use make_functor_data.
  - apply idfun.
  - intros a b f; unfold idfun.
    exact ((ε T) a · f).
Defined.

Lemma Right_Cokleisli_is_functor {C : category} (T: Comonad C) :
  is_functor (Right_Cokleisli_functor_data T).
Proof.
  split.
  - intro a.
    unfold Right_Cokleisli_functor_data; cbn.
    apply id_right.
  - intros a b c f g.
    unfold Right_Cokleisli_functor_data; cbn.
    do 2 (rewrite <- assoc').
    apply cancel_postcomposition.
    apply pathsinv0.
    apply ε_cobind.
Defined.

Definition Right_Cokleisli_functor {C : category} (T : Comonad C) :
  functor C (Cokleisli_cat_monad T)
  := (Right_Cokleisli_functor_data T,,Right_Cokleisli_is_functor T).

Definition Left_Cokleisli_functor_data {C : category} (T : Comonad C) :
  functor_data (Cokleisli_cat_monad T) C.
Proof.
  use make_functor_data.
  - exact T.
  - intros a b.
    apply cobind.
Defined.

Lemma Left_Cokleisli_is_functor {C : category} (T : Comonad C) :
  is_functor (Left_Cokleisli_functor_data T).
Proof.
  use tpair.
  - intro a.
    unfold Left_Cokleisli_functor_data; unfold identity;
    unfold functor_on_morphisms; cbn.
    apply cobind_ε.
  - intros a b c f g; cbn.
    apply pathsinv0.
    apply cobind_cobind.
Defined.

Definition Left_Cokleisli_functor {C : category} (T : Comonad C) :
  functor (Cokleisli_cat_monad T) C
  := (Left_Cokleisli_functor_data T,,Left_Cokleisli_is_functor T).

(*Composition of the left and right Cokleisli functors is equal to T as a functor*)

Definition Cokleisli_functor_left_right_compose {C : category} (T : Comonad C) :
  (Right_Cokleisli_functor T) ∙ (Left_Cokleisli_functor T) = T.
Proof.
  use functor_eq.
  - apply homset_property.
  - use functor_data_eq_from_nat_trans.
    + intro a; apply idpath.
    + intros a b f; cbn.
      rewrite id_right.
      rewrite id_left.
      apply cobind_comp_ε.
Defined.

(*Showing that these functors are adjoints*)

Definition Cokleisli_homset_iso {C : category} (T : Comonad C) : natural_hom_weq (Left_Cokleisli_functor T) (Right_Cokleisli_functor T).
Proof.
  use tpair.
  - intros a b; cbn.
    apply idweq.
  - cbn; split.
    + intros; apply idpath.
    + intros.
      rewrite <- assoc'.
      apply cancel_postcomposition.
      apply pathsinv0.
      apply ε_cobind.
Defined.

Definition Cokleisli_functors_are_adjoints {C : category} (T : Comonad C) : are_adjoints (Left_Cokleisli_functor T) (Right_Cokleisli_functor T) := adj_from_nathomweq (Cokleisli_homset_iso T).

Definition Left_Cokleisli_is_left_adjoint {C : category} (T : Comonad C)
  : is_left_adjoint (Left_Cokleisli_functor T)
    := are_adjoints_to_is_left_adjoint (Left_Cokleisli_functor T)
    (Right_Cokleisli_functor T) (Cokleisli_functors_are_adjoints T).

Definition Right_Cokleisli_is_right_adjoint {C : category} (T : Comonad C)
  : is_right_adjoint (Right_Cokleisli_functor T)
    := are_adjoints_to_is_right_adjoint (Left_Cokleisli_functor T)
    (Right_Cokleisli_functor T) (Cokleisli_functors_are_adjoints T).

Theorem Cokleisli_adjunction_comonad_eq {C : category} (T : Comonad C)  : Comonad_from_adjunction (Cokleisli_functors_are_adjoints T) = T.
Proof.
  use Comonad_eq_raw_data.
  apply total2_paths_equiv; use tpair.
  + cbn.
    apply idpath.
  + cbn.
    apply total2_paths_equiv; use tpair.
    * cbn.
      apply total2_paths_equiv; use tpair.
      -- cbn.
         do 2 (apply funextsec; intro).
         apply funextfun; intro f.
         cbn.
         apply cobind_comp_ε.
      -- cbn.
         rewrite transportf_const.
         cbn.
         apply funextsec; intro c.
         apply cobind_identity.
    * cbn.
      rewrite transportf_const.
      apply idpath.
Defined.

End Cokleisli_Categories.

(**
 Two useful laws
 *)
Definition ε_ε_cobind
           {C : category}
           (M : Comonad C)
           (x : C)
  : cobind (identity _) · ε M _ · ε M x = ε M x.
Proof.
  rewrite cobind_identity.
  refine (_ @ id_left _).
  apply maponpaths_2.
  apply Comonad_law1.
Qed.

Definition ε_cobind_cobind
           {C : category}
           (M : Comonad C)
           (x : C)
  : cobind (identity _) · cobind (identity _) · ε M (M(M x))
    =
    cobind (identity _) · ε M (M x) · δ M x.
Proof.
  rewrite !cobind_identity.
  rewrite assoc'.
  etrans.
  {
    apply maponpaths.
    apply Comonad_law1.
  }
  refine (!_).
  rewrite id_right, <- id_left.
  apply maponpaths_2.
  apply Comonad_law1.
Qed.

(********************************************************************************

 Examples of Duploids

 Contents:
 1. Duploids from monads.
 2. Thunk-force categories.

 Author: B. Szilvasy
 April 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.RXGraph.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.ComonadCoalgebras.
Require Import UniMath.CategoryTheory.Categories.EilenbergMoore.
Require Import UniMath.CategoryTheory.Categories.KleisliCategory.
Require Import UniMath.CategoryTheory.Monads.KleisliCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Envelope.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.EqualizingRequirement.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Univalence.

Local Open Scope cat.
Local Open Scope duploid.
Local Open Scope oblique_mor.

Section duploids_from_monads.

  Definition is_monad_equalizing
    {C : category} (T : Monad C) : UU
    := ∏ (a b : C) (f : a --> T b)
        (Hf : f · # T (η T b) = f · η T (T b)),
      ∃! f' : a --> b, f' · η T b = f.

  Let eilenberg_moore_adjunction
    {C : category} (T : Monad C)
    := left_adjoint_to_adjunction (is_left_adjoint_eilenberg_moore_free T).

  Definition eilenberg_moore_duploid
    {C : category} (T : Monad C)
    : duploid
    := envelope_duploid (eilenberg_moore_adjunction T).

  Definition weq_eilenberg_moore_duploid_mor
    {C : category} (T : Monad C) {a b : C}
    : C⟦a, T b⟧ ≃ eilenberg_moore_duploid T⟦envelope_ob_of_positive _ a, envelope_ob_of_positive _ b⟧
    := weq_oblique_mor_from_positive (eilenberg_moore_adjunction T)
         a (eilenberg_moore_free T b).

  Definition eilenberg_moore_duploid_incl
    {C : category} (T : Monad C)
    : functor (Kleisli_cat_monad T) (eilenberg_moore_duploid T).
  Proof.
    use make_functor; [use make_functor_data|].
    - exact (envelope_ob_of_positive (eilenberg_moore_adjunction T)).
    - exact (@weq_eilenberg_moore_duploid_mor C T).
    - abstract (
          use make_is_functor;
          [ intro a; now apply oblique_mor_positive_path
          | intros a b c f g; apply oblique_mor_positive_path; cbn;
            now rewrite !id_left ]).
  Defined.

  Definition fully_faithful_eilenberg_moore_duploid_incl_functor
    {C : category} (T : Monad C)
    : fully_faithful (eilenberg_moore_duploid_incl T).
  Proof.
    intros a b; apply weqproperty.
  Defined.

  Lemma is_negative_equalizing_eilenberg_moore_adjunction
    {C : category} (T : Monad C)
    : is_negative_equalizing (eilenberg_moore_adjunction T).
  Proof.
    intros x y f Hf.
    do 2 apply base_paths in Hf; cbn in Hf; rewrite !id_left in Hf.
    intermediate_iscontr (∑ f' : x --> y, mor_of_eilenberg_moore_ob x · pr11 f' = pr11 f). {
      use weqbandf; [exact (idweq _)|intro f'].
      eapply weqcomp; [apply subtypeInjectivity; intro; apply propproperty|].
      eapply weqcomp; [apply subtypeInjectivity; intro; apply homset_property|].
      cbn; rewrite id_left; exact (idweq _).
    }
    assert (Hf' := eq_of_eilenberg_moore_mor f); cbn in Hf'.
    assert (lemma : mor_of_eilenberg_moore_ob x · (η T (pr11 x) · pr11 f) = pr11 f). {
      etrans; [apply assoc|].
      etrans; [apply cancel_postcomposition, (nat_trans_ax (η T))|].
      etrans; [apply assoc'|].
      etrans; [apply cancel_precomposition, (Hf @ Hf')|].
      etrans; [apply assoc|].
      etrans; [apply cancel_postcomposition, pathsinv0, (nat_trans_ax (η T))|].
      etrans; [apply assoc'|].
      apply remove_id_right; [|reflexivity].
      apply (eilenberg_moore_ob_unit y).
    }
    use unique_exists.
    + apply (make_mor_eilenberg_moore T (η T (pr11 x) · pr11 f)).
      intermediate_path (pr11 f).
      * exact lemma.
      * etrans; [|apply cancel_postcomposition, pathsinv0, functor_comp].
        etrans; [|apply assoc].
        etrans; [|apply cancel_precomposition, (Hf @ Hf')].
        etrans; [|apply assoc'].
        etrans; [|apply cancel_postcomposition, functor_comp].
        apply pathsinv0, remove_id_left; [|reflexivity].
        etrans; [|apply functor_id].
        apply maponpaths, (eilenberg_moore_ob_unit x).
    + exact lemma.
    + intro g; apply homset_property.
    + intros g Hg; cbn in Hg.
      apply eq_mor_eilenberg_moore; cbn.
      rewrite <- Hg, assoc.
      apply pathsinv0, remove_id_left; [|reflexivity].
      apply (eilenberg_moore_ob_unit x).
  Qed.

  Example is_positive_equalizing_eilenberg_moore_adjunction {C : category} (T : Monad C)
    : is_positive_equalizing (eilenberg_moore_adjunction T)
      = is_monad_equalizing T.
  Proof. reflexivity. Defined.

  Lemma is_univalent_eilenberg_moore_duploid
    {C : category} (T : Monad C)
    (HC : is_univalent C)
    (Heq : ∏ (a b : C) (f : a --> T b)
             (Hf : f · # T (η T b) = f · η T (T b)),
        ∃! f' : a --> b, f' · η T b = f)
    : is_duploid_univalent (eilenberg_moore_duploid T).
  Proof.
    use is_univalent_envelope_duploid'.
    - exact (is_univalent_eilenberg_moore_cat T HC).
    - exact HC.
    - exact (is_negative_equalizing_eilenberg_moore_adjunction T).
    - exact Heq.
  Qed.

  Let kleisli_adjunction
    {C : category} (T : Monad C)
    := left_adjoint_to_adjunction (is_left_adjoint_kleisli_incl T).

  Definition kleisli_duploid
    {C : category} (T : Monad C)
    : duploid
    := envelope_duploid (kleisli_adjunction T).

  Definition weq_kleisli_duploid_mor
    {C : category} (T : Monad C) {a b : C}
    : C⟦a, T b⟧ ≃ kleisli_duploid T⟦envelope_ob_of_positive _ a, envelope_ob_of_positive _ b⟧
    := weq_oblique_mor_from_positive (kleisli_adjunction T) a (kleisli_incl T b).

  Definition kleisli_duploid_incl
    {C : category} (T : Monad C)
    : functor (Kleisli_cat_monad T) (kleisli_duploid T).
  Proof.
    use make_functor; [use make_functor_data|].
    - exact (envelope_ob_of_positive (kleisli_adjunction T)).
    - exact (@weq_kleisli_duploid_mor C T).
    - abstract (
          use make_is_functor;
          [ intro a; now apply oblique_mor_positive_path
          | intros a b c f g; apply oblique_mor_positive_path; cbn;
            now rewrite !id_left ]).
  Defined.

  Definition fully_faithful_kleisli_duploid_incl_functor
    {C : category} (T : Monad C)
    : fully_faithful (kleisli_duploid_incl T).
  Proof.
    intros a b; apply weqproperty.
  Defined.

  Lemma is_negative_equalizing_kleisli_adjunction
    {C : category} (T : Monad C)
    (H : is_univalent C)
    : is_negative_equalizing (kleisli_adjunction T).
  Proof.
    intros x y f Hf.
    intermediate_iscontr
      (∑ f' : eilenberg_moore_cat T⟦pr1 x, pr1 y⟧,
          adjcounit (eilenberg_moore_adjunction T) (pr1 x) · f' = pr1 f). {
      use weqbandf; [apply weqtotalsubtype | intro f'].
      eapply weqcomp; [apply subtypeInjectivity; intro; apply propproperty|].
      exact (idweq _).
    }
    apply base_paths in Hf.
    apply is_negative_equalizing_eilenberg_moore_adjunction, Hf.
  Qed.

  Example is_positive_equalizing_kleisli_adjunction {C : category} (T : Monad C)
    : is_positive_equalizing (kleisli_adjunction T)
      = is_monad_equalizing T.
  Proof. reflexivity. Defined.

  Lemma is_univalent_kleisli_duploid
    {C : category} (T : Monad C)
    (HC : is_univalent C)
    (Heq : is_monad_equalizing T)
    : is_duploid_univalent (kleisli_duploid T).
  Proof.
    use is_univalent_envelope_duploid'.
    - exact (univalent_category_is_univalent
               (univalent_kleisli_cat (C:=C,,HC) T)).
    - exact HC.
    - exact (is_negative_equalizing_kleisli_adjunction T HC).
    - exact Heq.
  Qed.

End duploids_from_monads.

Section thunk_force_def.

  (** Thunk-force (un)natural transformations. *)
  Definition thunk_force_trans_data
    {K : precategory_data} (L : functor_data K K) : UU
    := nat_trans_data (functor_identity K) L
         × nat_trans L (functor_identity K).

  Definition make_thunk_force_trans_data
    {K : precategory_data} (L : functor_data K K)
    (θ : nat_trans_data (functor_identity K) L)
    (ε : nat_trans L (functor_identity K))
    : thunk_force_trans_data L
    := θ,,ε.

  Definition thunk₀
    {K : precategory_data} {L : functor_data K K}
    (T : thunk_force_trans_data L)
    : nat_trans_data (functor_identity K) L
    := pr1 T.

  Definition force₀
    {K : precategory_data} {L : functor_data K K}
    (T : thunk_force_trans_data L)
    : nat_trans L (functor_identity K)
    := pr2 T.

  (** Thunk-force laws. *)
  (* type in Emacs with agda-input as id \_1 *)
  Local Notation "F '∙₀' G" := (functor_composite_data F G) (at level 40, left associativity).

  Let vcomp_data₀
    {C D : precategory_data}
    {F G H : functor_data C D}
    (α : nat_trans_data F G)
    (β : nat_trans_data G H)
    : nat_trans_data F H
      := λ c : C, α c · β c.
  Local Notation "α '◦' β" := (vcomp_data₀ β α) (at level 40, no associativity).
  (* type in Emacs with agda-input as \bu 3 *)
  Local Notation "α '•' β" := (vcomp_data₀ α β) (at level 40, no associativity, only parsing).
  (* type in Emacs with agda-input as \bu 2 *)

  Let prewhisker_data₀
    {C D E : precategory_data}
    {G G' : functor_data D E}
    (α : nat_trans_data G G')
    (F : functor_data C D)
    : nat_trans_data (F ∙₀ G) (F ∙₀ G')
      := λ c : C, α (F c).
  Local Notation "α '▻' F" := (prewhisker_data₀ α F) (at level 40, no associativity).
  (* type in Emacs with agda-input as \t 8 *)

  Let postwhisker_data₀
    {C D E : precategory_data}
    {F F' : functor_data C D}
    (G : functor_data D E)
    (α : nat_trans_data F F')
    : nat_trans_data (F ∙₀ G) (F' ∙₀ G)
      := λ c : C, #G (α c).
  Local Notation "G '◅' α" := (postwhisker_data₀ G α) (at level 40, no associativity).
  (* type in Emacs with agda-input as \t 4 *)

  Let id₁
    {C D : precategory_data}
    (F : functor_data C D)
    : nat_trans_data F F
      := λ c : C, identity (F c).

  Definition thunk_force_trans_laws
    {K : precategory_data} {L : functor_data K K}
    (θε : thunk_force_trans_data L) : UU
    := let θ := pr1 θε in
       let ε := pr2 θε in
       (* [θ a : a -> L a] is a coalgebra: multiplication *)
       ((L ◅ θ) ◦ θ ~ (θ ▻ L) ◦ θ)
         × (* [θ a : a -> L a] is a coalgebra: unit *)
         (ε ◦ θ ~ id₁ (functor_identity K))
         × (* [(L,,ε,,θL)] is a comonad: naturality *)
         is_nat_trans L (L ∙₀ L) (θ ▻ L)
         × (* [(L,,ε,,θL)] is a comonad: triangle *)
         ((L ◅ ε) ◦ (θ ▻ L) ~ id₁ L).

  Definition make_thunk_force_trans_laws
    {K : precategory_data} {L : functor_data K K}
    (θε : thunk_force_trans_data L)
    (* [θ a : a -> L a] is a coalgebra: multiplication *)
    (H1 : (L ◅ thunk₀ θε) ◦ thunk₀ θε ~ (thunk₀ θε ▻ L) ◦ thunk₀ θε)
    (* [θ a : a -> L a] is a coalgebra: unit *)
    (H2 : force₀ θε ◦ thunk₀ θε ~ id₁ (functor_identity K))
    (* [(L,,ε,,θL)] is a comonad: naturality *)
    (H3 : is_nat_trans L (L ∙₀ L) (thunk₀ θε ▻ L))
    (* [(L,,ε,,θL)] is a comonad: triangle *)
    (H4 : (L ◅ force₀ θε) ◦ (thunk₀ θε ▻ L) ~ id₁ L)
    : thunk_force_trans_laws θε
    := H1,,H2,,H3,,H4.

  Definition thunk_force_coalg_comult
    {K : precategory_data} {L : functor_data K K}
    {θε : thunk_force_trans_data L}
    (H : thunk_force_trans_laws θε)
    : (L ◅ thunk₀ θε) ◦ thunk₀ θε ~ (thunk₀ θε ▻ L) ◦ thunk₀ θε
    := pr1 H.

  Definition thunk_force_coalg_counit
    {K : precategory_data} {L : functor_data K K}
    {θε : thunk_force_trans_data L}
    (H : thunk_force_trans_laws θε)
    : force₀ θε ◦ thunk₀ θε ~ id₁ (functor_identity K)
    := pr12 H.

  Definition thunk_force_comult_is_nat_trans
    {K : precategory_data} {L : functor_data K K}
    {θε : thunk_force_trans_data L}
    (H : thunk_force_trans_laws θε)
    : is_nat_trans L (L ∙₀ L) (thunk₀ θε ▻ L)
    := pr122 H.

  Definition thunk_force_comult
    {K : precategory_data} {L : functor_data K K}
    {θε : thunk_force_trans_data L}
    (H : thunk_force_trans_laws θε)
    : nat_trans L (L ∙₀ L)
    := make_nat_trans _ _
         (thunk₀ θε ▻ L)
         (thunk_force_comult_is_nat_trans H).

  Definition thunk_force_triangle
    {K : precategory_data} {L : functor_data K K}
    {θε : thunk_force_trans_data L}
    (H : thunk_force_trans_laws θε)
    : (L ◅ force₀ θε) ◦ (thunk₀ θε ▻ L) ~ id₁ L
    := pr222 H.

  Lemma isaprop_thunk_force_trans_laws'
    {K : precategory_data} {L : functor_data K K}
    (θε : thunk_force_trans_data L)
    (hs : has_homsets K)
    : isaprop (thunk_force_trans_laws θε).
  Proof.
    repeat use isapropdirprod;
      repeat (use impred; intro);
      use hs.
  Qed.

  Lemma isaprop_thunk_force_trans_laws
    {K : category} {L : functor_data K K}
    (θε : thunk_force_trans_data L)
    : isaprop (thunk_force_trans_laws θε).
  Proof.
    apply isaprop_thunk_force_trans_laws'.
    apply homset_property.
  Qed.

  (** Full thunk-force structure. *)
  Definition thunk_force_trans_structure
    {K : precategory_data} (L : functor_data K K) : UU
    := ∑ θε : thunk_force_trans_data L, thunk_force_trans_laws θε.

  Coercion thunk_force_trans_structure_to_data
    {K : precategory_data} (L : functor_data K K)
    (θε : thunk_force_trans_structure L)
    : thunk_force_trans_data L
    := pr1 θε.
  Coercion thunk_force_trans_structure_to_laws
    {K : precategory_data} (L : functor_data K K)
    (θε : thunk_force_trans_structure L)
    : thunk_force_trans_laws θε
    := pr2 θε.

  Definition make_thunk_force_trans_structure
    {K : precategory_data} (L : functor_data K K)
    (θε : thunk_force_trans_data L)
    (H : thunk_force_trans_laws θε)
    : thunk_force_trans_structure L
    := θε,,H.

  Definition thunk_force_structure (K : precategory_data) : UU
    := ∑ L : functor K K, thunk_force_trans_structure L.

  Coercion thunk_force_structure_to_functor
    {K : precategory_data} (T : thunk_force_structure K)
    : functor K K
    := pr1 T.
  Coercion thunk_force_structure_to_trans_structure
    {K : precategory_data} (T : thunk_force_structure K)
    : thunk_force_trans_structure T
    := pr2 T.

  Definition make_thunk_force_structure
    (K : precategory_data)
    (L : functor K K)
    (θε : thunk_force_trans_structure L)
    : thunk_force_structure K
    := L,,θε.

  Definition is_thunkable₀
    {K : precategory_data} {L : functor K K}
    (θε : thunk_force_trans_data L)
    {a b : K} (f : a --> b)
    : UU
    := thunk₀ θε a · #L f = f · thunk₀ θε b.

  Definition comm_thunkable₀
    {K : precategory_data} {L : functor K K}
    (θε : thunk_force_trans_data L)
    {a b : K} (f : a --> b)
    (H : is_thunkable₀ θε f)
    : thunk₀ θε a · #L f = f · thunk₀ θε b
    := H.

  Definition is_thunkable₀_identity
    {K : precategory} {L : functor K K}
    (θε : thunk_force_trans_data L)
    (a : K)
    : is_thunkable₀ θε (identity a).
  Proof.
    red.
    now rewrite functor_id, id_right, id_left.
  Qed.

  Definition is_thunkable₀_compose
    {K : precategory} {L : functor K K}
    (θε : thunk_force_trans_data L)
    {a b c : K}
    (f : a --> b) (g : b --> c)
    (Hf : is_thunkable₀ θε f) (Hg : is_thunkable₀ θε g)
    : is_thunkable₀ θε (f · g).
  Proof.
    red.
    rewrite functor_comp, assoc.
    rewrite Hf, !assoc'.
    apply cancel_precomposition.
    apply Hg.
  Qed.

  (** Restatement of [thunk_force_coalg_comult]. *)
  Definition is_thunkable₀_thunk₀
    {K : precategory_data} {L : functor K K}
    (θε : thunk_force_trans_structure L)
    : ∏ a, is_thunkable₀ θε (thunk₀ θε a)
    := thunk_force_coalg_comult θε.

  (** Conversion to comonad and algebra. *)
  Definition thunk_force_trans_structure_to_disp_Comonad_data
    {K : category}
    {L : functor K K}
    (θε : thunk_force_trans_structure L)
    : disp_Comonad_data L
    := thunk_force_comult θε,, force₀ θε.

  Definition thunk_force_trans_structure_to_disp_Comonad_laws
    {K : category}
    {L : functor K K}
    (θε : thunk_force_trans_structure L)
    : disp_Comonad_laws (thunk_force_trans_structure_to_disp_Comonad_data θε).
  Proof.
    refine ((_,,_),,_); intro c; cbn.
    - exact (thunk_force_coalg_counit θε (L c)).
    - exact (thunk_force_triangle θε c).
    - exact (thunk_force_coalg_comult θε (L c)).
  Qed.

  Definition thunk_force_trans_structure_to_disp_Comonad
    {K : category}
    {L : functor K K}
    (θε : thunk_force_trans_structure L)
    : comonads_category_disp L
    := _,, thunk_force_trans_structure_to_disp_Comonad_laws θε.

  Definition thunk_force_structure_to_Comonad
    {K : category}
    (T : thunk_force_structure K)
    : Comonad K
    := _,, thunk_force_trans_structure_to_disp_Comonad T.

  Definition thunk_force_structure_to_Coalgebra_data
    {K : category}
    (T : thunk_force_structure K)
    (a : K)
    : Coalgebra_data (thunk_force_structure_to_Comonad T)
    := a,, thunk₀ T a.

  Lemma thunk_force_structure_to_Coalgebra_laws
    {K : category}
    (T : thunk_force_structure K)
    (a : K)
    : Coalgebra_laws _
        (thunk_force_structure_to_Coalgebra_data T a).
  Proof.
    split; cbn.
    - exact (thunk_force_coalg_counit T a).
    - exact (!thunk_force_coalg_comult T a).
  Qed.

  Definition thunk_force_structure_to_Coalgebra
    {K : category}
    (T : thunk_force_structure K)
    (a : K)
    : Coalgebra (thunk_force_structure_to_Comonad T)
    := _,, thunk_force_structure_to_Coalgebra_laws T a.

  (** Conversion from comonad and coalgebra.
      (This is strictly more data than [make_thunk_force_trans_laws],
      use that instead!) *)
  Definition thunk_force_trans_laws_from_comonad_coalg
    {K : category}
    (L : functor K K)
    (θε : thunk_force_trans_data L)
    (H1 : is_nat_trans L (L ∙₀ L) (thunk₀ θε ▻ L))
    (H2 : disp_Comonad_laws (make_nat_trans _ _ _ H1,, force₀ θε))
    (H3 : ∏ a : K, Coalgebra_laws (L,,_,,H2) (a,,thunk₀ θε a))
    : thunk_force_trans_laws θε.
  Proof.
    apply make_thunk_force_trans_laws.
    - intro c; exact (!pr2 (H3 c)).
    - intro c; exact (pr1 (H3 c)).
    - exact H1.
    - intro c; exact (pr21 H2 c).
  Qed.

  (** Thunk force category to monad. *)
  Definition thunkable₀_subcategory
    {K : category} (T : thunk_force_structure K)
    : sub_precategories K.
  Proof.
    simple refine ((_,,_),,_,,_).
    - use totalsubtype.
    - intros a b f.
      exists (is_thunkable₀ T f).
      use homset_property.
    - intros a _.
      apply is_thunkable₀_identity.
    - intros a b c f g Hf Hg.
      apply is_thunkable₀_compose; assumption.
  Defined.

  Definition thunk_force_thunking_functor
    {K : category} (T : thunk_force_structure K)
    : K ⟶ thunkable₀_subcategory T.
  Proof.
    use make_functor; [use make_functor_data|].
    - intro a; exact (T a,,tt).
    - intros a b f; refine (#T f,,_).
      exact (!thunk_force_comult_is_nat_trans T _ _ f).
    - abstract (
          use make_is_functor;
          [ intro a; apply carrier_eq; apply functor_id
          | intros a b c f g; apply carrier_eq; apply functor_comp ]).
  Defined.

  Definition thunk_force_inclusion_functor
    {K : category} (T : thunk_force_structure K)
    : thunkable₀_subcategory T ⟶ K
    := sub_precategory_inclusion _ _.

  Definition thunk_force_structure_adjunction_data
    {K : category} (T : thunk_force_structure K)
    : adjunction_data (thunkable₀_subcategory T) K.
  Proof.
    exists (thunk_force_inclusion_functor T).
    exists (thunk_force_thunking_functor T).
    split.
    - use make_nat_trans.
      + intro a.
        exists (thunk₀ T (pr1 a)).
        apply is_thunkable₀_thunk₀.
      + abstract (
            intros a b f;
            apply carrier_eq;
            exact (!pr2 f)).
    - exact (force₀ T).
  Defined.

  Lemma thunk_force_structure_form_adjunction
    {K : category} (T : thunk_force_structure K)
    : form_adjunction' (thunk_force_structure_adjunction_data T).
  Proof.
    apply make_form_adjunction.
    - intro a.
      exact (thunk_force_coalg_counit T (pr1 a)).
    - intro a; apply carrier_eq.
      exact (thunk_force_triangle T a).
  Qed.

  Lemma are_adjoints_thunk_force_inclusion_and_thunking
    {K : category} (T : thunk_force_structure K)
    : are_adjoints
        (thunk_force_inclusion_functor T)
        (thunk_force_thunking_functor T).
  Proof.
    exact (make_are_adjoints _ _ _ _
             (thunk_force_structure_form_adjunction T)).
  Defined.

  Lemma is_right_adjoint_thunking_functor
    {K : category} (T : thunk_force_structure K)
    : is_right_adjoint (thunk_force_thunking_functor T).
  Proof.
    exists (thunk_force_inclusion_functor T).
    exact (are_adjoints_thunk_force_inclusion_and_thunking T).
  Defined.

  Definition thunk_force_structure_adjunction
    {K : category} (T : thunk_force_structure K)
    : adjunction (thunkable₀_subcategory T) K
    := right_adjoint_to_adjunction
         (is_right_adjoint_thunking_functor T).

  Definition thunk_force_structure_to_Monad
    {K : category} (T : thunk_force_structure K)
    : Monad (thunkable₀_subcategory T)
    := Monad_from_adjunction (thunk_force_structure_adjunction T).

  Lemma is_univalent_implies_all_isos_thunkable₀
    {K : category} (T : thunk_force_structure K)
    (H : is_univalent K)
    {a b : K} (p : z_iso a b) : is_thunkable₀ T p.
  Proof.
    induction b, p using (rxgraph_edge_rect (G:=category_to_rxgraph K) H a).
    apply is_thunkable₀_identity.
  Qed.

End thunk_force_def.

Section thunk_force_duploid.
  Context {K : category} (T : thunk_force_structure K).

  Definition thunk_force_duploid
    := eilenberg_moore_duploid (thunk_force_structure_to_Monad T).
  Definition thunk_force_adjunction
    := left_adjoint_to_adjunction
         (is_left_adjoint_eilenberg_moore_free (thunk_force_structure_to_Monad T)).

  Definition thunk_force_duploid_incl_data
    : functor_data K thunk_force_duploid.
  Proof.
    use make_functor_data.
    - intro a; apply envelope_ob_of_positive, (a,,tt).
    - intros a b f.
      apply oblique_mor_from_positive; cbn.
      exists (thunk₀ T a · #T f); cbn.
      apply is_thunkable₀_compose.
      + apply is_thunkable₀_thunk₀.
      + apply pathsinv0, (thunk_force_comult_is_nat_trans T).
  Defined.

  Definition thunk_force_duploid_incl_is_functor
    : is_functor thunk_force_duploid_incl_data.
  Proof.
    use make_is_functor; red; intros;
        apply oblique_mor_positive_path, carrier_eq; cbn.
    - now rewrite functor_id, id_right.
    - rewrite !id_left, !functor_comp.
      rewrite !assoc'.
      do 2 apply cancel_precomposition.
      rewrite <- functor_comp.
      rewrite (nat_trans_ax (force₀ T)); cbn.
      rewrite functor_comp, assoc.
      apply pathsinv0, remove_id_left; [|reflexivity].
      rewrite <- functor_id, <- functor_comp.
      apply maponpaths.
      apply (thunk_force_coalg_counit T).
  Qed.

  Definition thunk_force_duploid_incl
    : K ⟶ thunk_force_duploid
    := make_functor _ thunk_force_duploid_incl_is_functor.

  Lemma is_equalizing_thunk_force_structure_to_Monad
    : is_monad_equalizing (thunk_force_structure_to_Monad T).
  Proof.
    intros a b f Hf'.
    induction f as [f Hf]; red in Hf; cbn in f, Hf.
    apply base_paths in Hf'; cbn in Hf'.
    assert (lemma : f · force₀ T (pr1 b) · thunk₀ T (pr1 b) = f). {
      rewrite assoc'.
      etrans; [apply cancel_precomposition, pathsinv0,
                (nat_trans_ax (force₀ T))|].
      fold (thunk₀ T).
      rewrite assoc.
      etrans; [apply cancel_postcomposition, Hf'|].
      rewrite assoc'.
      apply remove_id_right; [|reflexivity].
      apply (thunk_force_coalg_counit T).
    }
    use unique_exists.
    - refine (f · force₀ T (pr1 b),,_).
      cbn; red in Hf |- *.
      intermediate_path f.
      + rewrite functor_comp, assoc.
        rewrite Hf, <- Hf'.
        rewrite !assoc'.
        apply remove_id_right; [|reflexivity].
        rewrite <- functor_comp, <- functor_id.
        apply maponpaths.
        apply (thunk_force_coalg_counit T).
      + exact (!lemma).
    - apply carrier_eq; cbn.
      exact lemma.
    - intro g; apply homset_property.
    - intros g Hg.
      apply base_paths in Hg.
      apply carrier_eq; cbn in Hg |- *.
      rewrite <- Hg, assoc'.
      apply pathsinv0, remove_id_right; [|reflexivity].
      apply (thunk_force_coalg_counit T).
  Qed.

  Lemma is_univalent_thunk_force_duploid
    (HC : is_univalent (thunkable₀_subcategory T))
    : is_duploid_univalent thunk_force_duploid.
  Proof.
    apply is_univalent_eilenberg_moore_duploid.
    - exact HC.
    - exact is_equalizing_thunk_force_structure_to_Monad.
  Qed.

  Definition thunk_force_cat_from_kleisli_cat_data
    : functor_data
        (Kleisli_cat_monad (Monad_from_adjunction thunk_force_adjunction))
        K.
  Proof.
    use make_functor_data.
    - exact pr1.
    - intros a b f.
      cbn in b, f.
      exact (f · force₀ T b).
  Defined.

  Definition thunk_force_cat_from_kleisli_cat_is_functor
    : is_functor thunk_force_cat_from_kleisli_cat_data.
  Proof.
    use make_is_functor.
    - intro a; cbn.
      apply (thunk_force_coalg_counit T).
    - intros a b c f g; cbn.
      rewrite id_left, <- functor_comp, !assoc'.
      now rewrite (nat_trans_ax (force₀ T)).
  Defined.

  Definition thunk_force_cat_from_kleisli_cat
    : functor (Kleisli_cat_monad (Monad_from_adjunction thunk_force_adjunction)) K
    := make_functor _ thunk_force_cat_from_kleisli_cat_is_functor.

  Lemma fully_faithful_thunk_force_cat_from_kleisli_cat
    : fully_faithful thunk_force_cat_from_kleisli_cat.
  Proof.
    intros a b.
    cbn in a, b |- *.
    use isweq_iso.
    - intro g.
      refine (thunk₀ T a · #T g,,_).
      abstract (
          cbn; red;
          rewrite assoc', (thunk_force_comult_is_nat_trans T); cbn;
          rewrite functor_comp, !assoc;
          apply cancel_postcomposition;
          apply (thunk_force_coalg_comult T)).
    - abstract (
          intro f; apply carrier_eq; cbn;
          rewrite functor_comp, assoc;
          etrans; [apply cancel_postcomposition, (pr2 f)|];
          rewrite assoc';
          apply remove_id_right; [|reflexivity];
          apply (thunk_force_triangle T)).
    - abstract (
          intro g; cbn;
          rewrite assoc', (nat_trans_ax (force₀ T)), assoc;
          apply remove_id_left; [|reflexivity];
          apply (thunk_force_coalg_counit T)).
  Defined.

  Lemma isweq_on_objects_thunk_force_cat_from_kleisli_cat
    : isweq (functor_on_objects thunk_force_cat_from_kleisli_cat).
  Proof.
    apply isweqpr1; intro; exact iscontrunit.
  Defined.

  Definition is_catiso_thunk_force_cat_from_kleisli_cat
    : is_catiso thunk_force_cat_from_kleisli_cat
    := fully_faithful_thunk_force_cat_from_kleisli_cat,,
         isweq_on_objects_thunk_force_cat_from_kleisli_cat.

  Theorem thunk_force_duploid_positive_category_eq
    (HC : is_univalent (thunkable₀_subcategory T))
    : positive_category thunk_force_duploid = K.
  Proof.
    refine (!eq_kleisli_subcategory_envelope_duploid_positive
              _ (is_univalent_eilenberg_moore_cat _ HC) HC
              (is_negative_equalizing_eilenberg_moore_adjunction _)
              @ _).
    apply catiso_to_category_path.
    exact (_,,is_catiso_thunk_force_cat_from_kleisli_cat).
  Defined.

End thunk_force_duploid.

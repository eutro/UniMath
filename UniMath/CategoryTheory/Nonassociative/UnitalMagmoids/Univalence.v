(********************************************************************************

 Univalence of Unital Magmoids

 Author: B. Szilvasy
 January 2026

 In this file I develop the theory of [catiso]s on unital magmoids.  There is no
 statement of what it means for (just) a unital magmoid to be univalent.
 Instead, more structured objects such as Duploids and Categories have their own
 notion of univalence that translates to [catiso]s.

 Contents:
 1. Reflexive graph of unital magmoids and [catiso]s
 2. Definition of univalence for unital magmoids

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.RXGraph.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Functors.

Local Open Scope cat.
Local Open Scope rxgraph.

(** * 1. Reflexive graph of unital magmoids and [catiso]s *)

Section unital_magmoid_rxgraph.
  Definition precategory_ob_mor_rxgraph : univalent_rxgraph.
  Proof.
    use (@univalent_total_rxgraph UU_rxgraph).
    use make_univalent_disp_rxgraph.
    1: use make_disp_rxgraph'.
    - intro C.
      exact (∏ (_ _ : C), UU_rxgraph)%rxgraph_spec.
    - intros C D F Cm Dm. cbn in *.
      exact (∏ (a b : C), weq (Cm a b) (Dm (F a) (F b))).
    - intros C Cm a b. cbn in *.
      exact (idweq (Cm a b)).
    - intro C.
      exact (rxgraph_univalence _).
  Defined.

  Lemma vertex_precategory_ob_mor_rxgraph
    : (precategory_ob_mor_rxgraph : UU) = precategory_ob_mor.
  Proof. reflexivity. Defined.

  Lemma edge_precategory_ob_mor_rxgraph (C D : precategory_ob_mor_rxgraph)
    : (C ≈ D) ≃ ∑ (F : functor_data C D),
      (∏ (a b : ob C), isweq (functor_on_morphisms F (a:=a) (b:=b)))
        × (isweq (functor_on_objects F)).
  Proof.
    use weq_iso.
    - intros [Fweq Fweqonmor].
      cbn in Fweq, Fweqonmor.
      use tpair. {
        use make_functor_data.
        - exact (pr1weq Fweq).
        - intros a b; exact (pr1weq (Fweqonmor a b)).
      }
      apply make_dirprod.
      + intros a b; apply weqproperty.
      + apply weqproperty.
    - intros [F [Fweqonmor Fweq]].
      use tpair. {
        exact (make_weq _ Fweq).
      }
      intros a b.
      exact (make_weq _ (Fweqonmor a b)).
    - easy.
    - easy.
  Defined.

  Definition precategory_id_rxgraph : univalent_disp_rxgraph precategory_ob_mor_rxgraph.
  Proof.
    use make_univalent_disp_rxgraph.
    1: use make_disp_rxgraph'.
    - intro C.
      change precategory_ob_mor in C.
      exact (∏ a, Δ C⟦a, a⟧)%rxgraph_spec.
    - intros C D F Cid Did.
      change precategory_ob_mor in C, D.
      cbn in F.
      exact (∏ (a : C), pr2 F _ _ (Cid a) = Did (pr1 F a)).
    - intros C F a.
      apply idpath.
    - intro C.
      exact (rxgraph_univalence _).
  Defined.

  Definition precategory_comp_rxgraph : univalent_disp_rxgraph precategory_ob_mor_rxgraph.
  Proof.
    use make_univalent_disp_rxgraph.
    1: use make_disp_rxgraph'.
    - intro C.
      change precategory_ob_mor in C.
      exact (∏ a b c (f : C⟦a, b⟧) (g : C⟦b, c⟧), Δ C⟦a, c⟧)%rxgraph_spec.
    - intros C D F Ccomp Dcomp.
      change precategory_ob_mor in C, D.
      cbn in F, Ccomp, Dcomp.
      refine (∏ (a b c : C) (f : a --> b) (g : b --> c), _).
      exact (pr2 F _ _ (Ccomp _ _ _ f g) = Dcomp _ _ _ (pr2 F _ _ f) (pr2 F _ _ g)).
    - intros C F a b c f g.
      apply idpath.
    - intro C.
      exact (rxgraph_univalence _).
  Defined.

  Definition precategory_id_comp_rxgraph : univalent_disp_rxgraph precategory_ob_mor_rxgraph.
  Proof.
    use make_univalent_disp_rxgraph.
    1: use make_disp_rxgraph'.
    - intro C.
      exact (precategory_id_rxgraph⟦C⟧ × precategory_comp_rxgraph⟦C⟧)%rxgraph_spec.
    - intros C D p a b.
      cbn beta in *.
      exact (pr1 a ≈[p] pr1 b × pr2 a ≈[p] pr2 b).
    - intros C Cidcomp.
      use make_dirprod.
      + exact (disp_grefl C (pr1 Cidcomp)).
      + exact (disp_grefl C (pr2 Cidcomp)).
    - intro C.
      exact (rxgraph_univalence _).
  Defined.

  Definition precategory_data_rxgraph : univalent_rxgraph
    := univalent_total_rxgraph precategory_id_comp_rxgraph.

  Lemma vertex_precategory_data_rxgraph
    : (precategory_data_rxgraph : UU) = precategory_data.
  Proof. reflexivity. Defined.

  Lemma edge_precategory_data_rxgraph (C D : precategory_data_rxgraph)
    : (C ≈ D) ≃ catiso C D.
  Proof.
    use weq_iso.
    - intros [F HF].
      set (F' := pr1weq (edge_precategory_ob_mor_rxgraph (pr1 C) (pr1 D)) F).
      cbn in HF.
      use tpair. {
        use (make_functor (pr1 F')).
        exact HF.
      }
      exact (pr2 F').
    - intros [F HF].
      use tpair. {
        apply (invmap (edge_precategory_ob_mor_rxgraph (pr1 C) (pr1 D))).
        exists F.
        exact HF.
      }
      exact (pr2 F).
    - easy.
    - easy.
  Defined.

  Definition catiso_rxgraph : univalent_rxgraph.
  Proof.
    use make_univalent_rxgraph.
    1: use make_rxgraph'.
    - exact precategory_data.
    - intros C D.
      exact (catiso C D).
    - intros C.
      exact (identity_catiso C).
    - intros C D.
      use weqhomot.
      + use (weqcomp _ (edge_precategory_data_rxgraph C D)).
        apply (weq_id_to_edge precategory_data_rxgraph C D).
      + intro p; now induction p.
  Defined.

  Lemma weq_catiso_precategory_data_path' {A B : precategory_data}
    : catiso A B ≃ A = B.
  Proof.
    exact (weq_edge_to_id catiso_rxgraph A B).
  Defined.

  Corollary precategory_data_path_from_catiso {A B : precategory_data}
    : catiso A B -> A = B.
  Proof.
    exact (edge_to_id catiso_rxgraph A B).
  Defined.

  Definition catiso_with_homsets_rxgraph : univalent_rxgraph.
  Proof.
    simple refine ({ M : catiso_rxgraph ∇ make_hProp _ _ })%rxgraph_spec.
    change precategory_data in M.
    - exact (has_homsets M).
    - apply isaprop_has_homsets.
  Defined.

  Definition unital_magmoid_rxgraph0 : univalent_rxgraph.
  Proof.
    simple refine ({ M : catiso_with_homsets_rxgraph ∇ make_hProp _ _ })%rxgraph_spec.
    - exact (is_unital_premagmoid (pr1 M)).
    - apply isaprop_is_unital_premagmoid, (pr2 M).
  Defined.

  Definition unital_magmoid_rxgraph : univalent_rxgraph.
  Proof.
    use make_univalent_rxgraph.
    1: use make_rxgraph'.
    - exact unital_magmoid.
    - intros a b; exact (catiso a b).
    - intro a; exact (identity_catiso a).
    - use (rxgraph_univalent_from_iso_b' unital_magmoid_rxgraph0).
      1: apply rxgraph_univalence.
      use make_pregraph_iso; cbn.
      + use weq_iso.
        * intros [[M H1] H2]; exists (M,,H2); exact H1.
        * intros [[M H2] H1]; exists (M,,H1); exact H2.
        * easy.
        * easy.
      + intros a b; exact (idweq _).
  Defined.

  Definition category_to_rxgraph (C : category) : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact (ob C).
    - intros a b; exact (z_iso a b).
    - intros a; exact (identity_z_iso a).
  Defined.

  Remark category_rxgraph_univalent_eq (C : category)
    : is_univalent C = is_rxgraph_univalent (category_to_rxgraph C).
  Proof. reflexivity. Defined.

  Lemma transportf_is_univalent_over_catiso
    (C D : category) (F : catiso C D) (ua : is_univalent C)
    : is_univalent D.
  Proof.
    (* We could use the univalence axiom, but we don't need it. *)
    Succeed exact (transportf is_univalent (catiso_to_category_path F) ua).
    rewrite category_rxgraph_univalent_eq in ua |- *.
    apply (rxgraph_univalent_from_iso_f' _ ua).
    use make_pregraph_iso.
    - exact (catiso_ob_weq F).
    - cbn; intros a b.
      apply weq_ff_functor_on_z_iso.
      exact (pr12 F).
  Qed.

  Lemma transportb_is_univalent_over_catiso
    (C D : category) (F : catiso C D) (ua : is_univalent D)
    : is_univalent C.
  Proof.
    rewrite category_rxgraph_univalent_eq in ua |- *.
    apply (rxgraph_univalent_from_iso_b' _ ua).
    use make_pregraph_iso.
    - exact (catiso_ob_weq F).
    - cbn; intros a b.
      apply weq_ff_functor_on_z_iso.
      exact (pr12 F).
  Qed.

  Lemma weq_is_univalent_over_catiso
    (C D : category) (F : catiso C D)
    : is_univalent C ≃ is_univalent D.
  Proof.
    use weqimplimpl.
    - apply transportf_is_univalent_over_catiso, F.
    - apply transportb_is_univalent_over_catiso, F.
    - apply isaprop_is_univalent.
    - apply isaprop_is_univalent.
  Qed.

End unital_magmoid_rxgraph.

(** * 2. Definition of univalence for unital magmoids *)

Section unital_magmoid_univalence.

  Definition is_unital_magmoid_univalent (M : unital_magmoid) : UU
    := ∏ (a b : M), isweq (id_to_submm_iso _ a b : a = b -> lti_iso a b).

  Definition unital_magmoid_to_rxgraph (M : unital_magmoid) : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact (ob M).
    - exact lti_iso.
    - exact (submm_iso_identity _).
  Defined.

  Remark unital_magmoid_rxgraph_univalent_eq (M : unital_magmoid)
    : is_unital_magmoid_univalent M = is_rxgraph_univalent (unital_magmoid_to_rxgraph M).
  Proof. reflexivity. Defined.

  Definition isaprop_lti_iso_fiber_from_fully_faithful {M M' : unital_magmoid}
    (F : M ⟶ M') (Hff : fully_faithful F)
    (ua : is_unital_magmoid_univalent M)
    (a : M')
    : isaprop (∑ b, lti_iso (F b) a).
  Proof.
    use invproofirrelevance.
    intros H₁ H₂; induction H₁ as [b₁ e₁], H₂ as [b₂ e₂].
    pose (e := lti_iso_compose e₁ (submm_iso_inv _ e₂)).
    pose (e' := lti_iso_from_fully_faithful_functor_image F Hff e).
    assert (H := iscontr_uniqueness
                   (is_rxgraph_univalent_to_iscontr_edges_from
                      (unital_magmoid_to_rxgraph M) ua b₁)
                   (b₂,, e')).
    apply total2_paths_equiv in H;
      induction H as [H₁ H₂]; cbn in H₁, H₂.
    induction H₁; cbn in H₂.
    apply pair_path_in2.
    assert (He : e = submm_iso_identity _ _). {
      apply lti_iso_eq.
      refine (_ @ functor_id F b₂).
      do 2 apply base_paths in H₂; cbn in H₂.
      refine (_ @ maponpaths #F H₂).
      apply pathsinv0, (homotweqinvweq (weq_from_fully_faithful Hff _ _)).
    }
    clear e' H₂; subst e.
    do 2 apply base_paths in He.
    change (submm_iso_mor _ e₁ · submm_inverse_mor _ e₂ = identity _) in He.
    apply lti_iso_eq.
    rewrite <- (magmoid_id_right e₁), <- (magmoid_id_left e₂).
    rewrite <- (is_inverse_in_precat2 e₂).
    etrans; [apply assoc_thunkable; exact e₁|].
    apply cancel_postcomposition.
    exact He.
  Qed.

  Definition isincl_um_from_fully_faithful {M M' : unital_magmoid}
    (F : M ⟶ M')
    (Hff : fully_faithful F)
    (ua₁ : is_unital_magmoid_univalent M)
    (ua₂ : is_unital_magmoid_univalent M')
    : isincl (functor_on_objects F).
  Proof.
    intro a.
    apply (isofhlevelweqf 1 (X:=∑ b, lti_iso (F b) a)).
    - apply weqfibtototal; intro b.
      apply invweq, (_,, ua₂ (F b) a).
    - apply (isaprop_lti_iso_fiber_from_fully_faithful _ Hff ua₁).
  Qed.

  Definition is_lti_essentially_surjective {M M' : unital_magmoid}
    (F : functor_data M M') : hProp
    := ∀ (a : M'), ∃ (b : M), lti_iso (F b) a.

  Definition issurjective_from_lti_eso {M M' : unital_magmoid}
    (F : M ⟶ M')
    (Heso : is_lti_essentially_surjective F)
    (ua : is_unital_magmoid_univalent M')
    : issurjective (functor_on_objects F).
  Proof.
    intro a.
    refine (hinhfun _ (Heso a)).
    intro H; induction H as [b e].
    exists b.
    exact (invmap (_,, ua (F b) a) e).
  Defined.

  Definition isweq_on_objects_from_weak_um_equiv
    {M M' : unital_magmoid}
    (F : M ⟶ M')
    (Hff : fully_faithful F)
    (Heso : is_lti_essentially_surjective F)
    (ua₁ : is_unital_magmoid_univalent M)
    (ua₂ : is_unital_magmoid_univalent M')
    : isweq (functor_on_objects F).
  Proof.
    apply isweqinclandsurj.
    - exact (isincl_um_from_fully_faithful _ Hff ua₁ ua₂).
    - exact (issurjective_from_lti_eso _ Heso ua₂).
  Defined.

  Definition is_catiso_from_weak_um_equiv
    {M M' : unital_magmoid}
    (F : M ⟶ M')
    (Hff : fully_faithful F)
    (Heso : is_lti_essentially_surjective F)
    (ua₁ : is_unital_magmoid_univalent M)
    (ua₂ : is_unital_magmoid_univalent M')
    : is_catiso F.
  Proof.
    split.
    - exact Hff.
    - now apply isweq_on_objects_from_weak_um_equiv.
  Defined.

End unital_magmoid_univalence.

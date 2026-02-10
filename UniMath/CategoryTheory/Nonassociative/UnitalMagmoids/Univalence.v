(********************************************************************************

 Univalence of Unital Magmoids

 Author: B. Szilvasy
 January 2026

 In this file I develop the theory of [catiso]s on unital magmoids.  There is no
 statement of what it means for (just) a unital magmoid to be univalent.
 Instead, more structured objects such as Duploids and Categories have their own
 notion of univalence that translates to [catiso]s.

 Contents:
 TODO

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.RXGraph.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.

Local Open Scope cat.
Local Open Scope rxgraph.

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
  - use (rxgraph_univalent_from_iso_b unital_magmoid_rxgraph0).
    1: apply rxgraph_univalence.
    use make_rxgraph_iso; [use make_pregraph_iso|]; cbn.
    + use weq_iso.
      * intros [[M H1] H2]; exists (M,,H2); exact H1.
      * intros [[M H2] H1]; exists (M,,H1); exact H2.
      * easy.
      * easy.
    + intros a b; exact (idweq _).
    + now intros a.
Defined.

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

Definition precategory_ob_mor_rxgraph : rxgraph.
Proof.
  use (@total_rxgraph UU_rxgraph).
  use make_disp_rxgraph'.
  - intro ob; exact (ob -> ob -> UU).
  - intros C D F Cm Dm; cbn in *.
    exact (∏ (a b : C), weq (Cm a b) (Dm (F a) (F b))).
  - intros C Cm a b. cbn in *.
    apply idweq.
Defined.

Lemma is_univalent_precategory_ob_mor_rxgraph
  : is_rxgraph_univalent precategory_ob_mor_rxgraph.
Proof.
  apply is_univalent_total_rxgraph.
  1: apply is_univalent_UU_rxgraph.
  intros C Cm Cm'.
  cbn in C, Cm, Cm'.
  set (mor_rxgraph :=
         product_rxgraph
           (λ (_ : C),
             product_rxgraph (λ (_ : C),
                 UU_rxgraph))).
  change (isweq (@id_to_edge mor_rxgraph Cm Cm')).
  do 2 (apply is_univalent_product_rxgraph; intro).
  apply is_univalent_UU_rxgraph.
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

Definition precategory_id_rxgraph : disp_rxgraph precategory_ob_mor_rxgraph.
Proof.
  use make_disp_rxgraph'.
  - intro C.
    change precategory_ob_mor in C.
    exact (∏ (a : C), C⟦a, a⟧).
  - intros C D F Cid Did.
    change precategory_ob_mor in C, D.
    cbn in F.
    exact (∏ (a : C), pr2 F _ _ (Cid a) = Did (pr1 F a)).
  - intros C F a.
    apply idpath.
Defined.

Lemma is_univalent_precategory_id_rxgraph : is_disp_rxgraph_univalent precategory_id_rxgraph.
Proof.
  intros C.
  change precategory_ob_mor in C.
  intros Cid Cid'.
  set (id_rxgraph :=
         product_rxgraph
           (λ a : C, discrete_rxgraph (C⟦a, a⟧))).
  change (isweq (@id_to_edge id_rxgraph Cid Cid')).
  apply is_univalent_product_rxgraph; intro.
  apply is_univalent_discrete_rxgraph.
Defined.

Definition precategory_comp_rxgraph : disp_rxgraph precategory_ob_mor_rxgraph.
Proof.
  use make_disp_rxgraph'.
  - intro C.
    change precategory_ob_mor in C.
    exact (∏ (a b c : C) (f : a --> b) (g : b --> c), a --> c).
  - intros C D F Ccomp Dcomp.
    change precategory_ob_mor in C, D.
    cbn in F, Ccomp, Dcomp.
    refine (∏ (a b c : C) (f : a --> b) (g : b --> c), _).
    exact (pr2 F _ _ (Ccomp _ _ _ f g) = Dcomp _ _ _ (pr2 F _ _ f) (pr2 F _ _ g)).
  - intros C F a b c f g.
    apply idpath.
Defined.

Lemma is_univalent_precategory_comp_rxgraph : is_disp_rxgraph_univalent precategory_comp_rxgraph.
Proof.
  intro C.
  change precategory_ob_mor in C.
  intros Ccomp Ccomp'.
  cbn in Ccomp, Ccomp'.
  set (comp_rxgraph :=
         product_rxgraph (λ (a : C),
         product_rxgraph (λ (b : C),
         product_rxgraph (λ (c : C),
         product_rxgraph (λ (f : C⟦a, b⟧),
         product_rxgraph (λ (g : C⟦b, c⟧),
         discrete_rxgraph (C⟦a, c⟧))))))).
  change (isweq (@id_to_edge comp_rxgraph Ccomp Ccomp')).
  do 5 (apply is_univalent_product_rxgraph; intro).
  apply is_univalent_discrete_rxgraph.
Defined.

Definition precategory_id_comp_rxgraph : disp_rxgraph precategory_ob_mor_rxgraph.
Proof.
  use make_disp_rxgraph'.
  - intro C.
    exact (dirprod_rxgraph
             (disp_rxgraph_fib precategory_id_rxgraph C)
             (disp_rxgraph_fib precategory_comp_rxgraph C)).
  - intros C D p a b.
    cbn beta in *.
    exact (pr1 a ≈[p] pr1 b × pr2 a ≈[p] pr2 b).
  - intros C Cidcomp.
    use make_dirprod.
    + exact (disp_grefl C (pr1 Cidcomp)).
    + exact (disp_grefl C (pr2 Cidcomp)).
Defined.

Lemma is_univalent_precategory_id_comp_rxgraph : is_disp_rxgraph_univalent precategory_id_comp_rxgraph.
Proof.
  intro C.
  set (id_mor_rxgraph :=
         dirprod_rxgraph
           (disp_rxgraph_fib precategory_id_rxgraph C)
           (disp_rxgraph_fib precategory_comp_rxgraph C)).
  change (is_rxgraph_univalent id_mor_rxgraph).
  apply is_univalent_dirprod_rxgraph.
  - apply is_univalent_precategory_id_rxgraph.
  - apply is_univalent_precategory_comp_rxgraph.
Defined.

Definition precategory_data_rxgraph : rxgraph
  := total_rxgraph precategory_id_comp_rxgraph.

Lemma is_univalent_precategory_data_rxgraph : is_rxgraph_univalent precategory_data_rxgraph.
Proof.
  apply is_univalent_total_rxgraph.
  - apply is_univalent_precategory_ob_mor_rxgraph.
  - apply is_univalent_precategory_id_comp_rxgraph.
Defined.

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

Definition catiso_rxgraph : rxgraph.
Proof.
  use make_rxgraph'.
  - exact precategory_data.
  - intros C D.
    exact (catiso C D).
  - intros C.
    exact (identity_catiso C).
Defined.

Lemma is_univalent_catiso_rxgraph : is_rxgraph_univalent catiso_rxgraph.
Proof.
  intros C D.
  use weqhomot.
  - use (weqcomp _ (edge_precategory_data_rxgraph C D)).
    apply (make_weq _ (is_univalent_precategory_data_rxgraph C D)).
  - intro p; now induction p.
Defined.

Lemma weq_catiso_precategory_data_path' {A B : precategory_data}
  : catiso A B ≃ A = B.
Proof.
  apply invweq.
  exact (make_weq _ (is_univalent_catiso_rxgraph A B)).
Defined.

Corollary precategory_data_path_from_catiso {A B : precategory_data}
  : catiso A B -> A = B.
Proof. exact (pr1weq weq_catiso_precategory_data_path'). Defined.

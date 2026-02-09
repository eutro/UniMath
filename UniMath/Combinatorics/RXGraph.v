(********************************************************************************

 Reflexive Graphs

 Author: B. Szilvasy
 February 2026

 Contents:
 TODO

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Graph.
Require Import UniMath.Combinatorics.FLists.

Declare Scope rxgraph.
Delimit Scope rxgraph with rxgraph.
Local Open Scope rxgraph.

Notation "a '≈' b" := (edge _ a b) (at level 50) : rxgraph.

Section rxgraph_defs.
  Definition has_refl (G : pregraph) : UU
    := ∏ a : vertex G, a ≈ a.

  Definition rxgraph := total2 has_refl.
  Coercion rxgraph_to_pregraph (G : rxgraph) : pregraph := pr1 G.
  Coercion rxgraph_to_UU (G : rxgraph) : UU := vertex G.
  Definition grefl {G : rxgraph} : ∏ a : G, a ≈ a := pr2 G.

  Definition make_rxgraph (G : pregraph)
    (refl : has_refl G) : rxgraph := G,,refl.

  Definition make_rxgraph'
    (A : UU)
    (edge : A -> A -> UU)
    (refl : ∏ a : A, edge a a)
    : rxgraph := make_rxgraph (make_pregraph A edge) refl.

  Definition id_to_edge {G : rxgraph} {a b : G} (p : a = b) : a ≈ b.
  Proof. induction p. apply grefl. Defined.

  Definition is_rxgraph_univalent (G : rxgraph) : UU
    := ∏ a b, isweq (@id_to_edge G a b).

  Lemma isaprop_is_rxgraph_univalent (G : rxgraph)
    : isaprop (is_rxgraph_univalent G).
  Proof.
    do 2 (apply impred; intro).
    apply isapropisweq.
  Qed.

  Definition edges_from {G : pregraph} (a : vertex G) : UU
    := ∑ (b : vertex G), a ≈ b.

  Lemma is_rxgraph_univalent_from_iscontr_edges_from (G : rxgraph)
    (H : ∏ (a : G), iscontr (edges_from a))
    : is_rxgraph_univalent G.
  Proof.
    intros a b.
    apply isweqtotaltofib; clear b.
    apply isweqcontrcontr.
    - apply iscontr_paths_from.
    - apply H.
  Defined.

  Lemma rxgraph_edges_from_inhabited {G : rxgraph} (a : G) : edges_from a.
  Proof. exists a; apply grefl. Defined.

  Lemma is_rxgraph_univalent_from_isaprop_edges_from (G : rxgraph)
    (H : ∏ (a : G), isaprop (edges_from a))
    : is_rxgraph_univalent G.
  Proof.
    apply is_rxgraph_univalent_from_iscontr_edges_from.
    intro a.
    apply iscontraprop1; [|apply rxgraph_edges_from_inhabited].
    apply H.
  Defined.

  Lemma is_rxgraph_univalent_to_iscontr_edges_from (G : rxgraph)
    (H : is_rxgraph_univalent G)
    : ∏ (a : G), iscontr (edges_from a).
  Proof.
    intro a.
    use (iscontrweqf (X:=paths_from a)); [|apply iscontr_paths_from].
    refine (make_weq _ (isweqfibtototal _ _ _)).
    intro b.
    apply (make_weq _ (H a b)).
  Defined.

End rxgraph_defs.

Section disprxgraph_defs.
  Definition disp_pregraph (B : pregraph) : UU
    := ∑ (E : vertex B -> UU),
      ∏ (a b : vertex B) (e : edge B a b),
      E a -> E b -> UU.

  Definition make_disp_pregraph {B : pregraph}
    (E : vertex B -> UU)
    (edge : ∏ (a b : vertex B) (e : edge B a b),
        E a -> E b -> UU)
    : disp_pregraph B
    := E,,edge.

  Definition disp_vertex {B : pregraph} (E : disp_pregraph B)
    : vertex B -> UU := pr1 E.
  Coercion disp_vertex : disp_pregraph >-> Funclass.
  Definition disp_edge {B : pregraph} (E : disp_pregraph B)
    : ∏ {a b : vertex B} (e : edge B a b),
      E a -> E b -> UU
    := pr2 E.

  Local Notation "aa '≈[' e ']' bb" := (disp_edge _ e aa bb) (at level 50, bb at next level) : rxgraph.

  Definition total_pregraph {B : pregraph} (E : disp_pregraph B) : pregraph.
  Proof.
    use make_pregraph.
    - exact (∑ (x : vertex B), E x).
    - intros [x aa] [y bb].
      exact (∑ (e : x ≈ y), aa ≈[e] bb).
  Defined.

  Context {B : rxgraph}.

  Definition has_disp_refl (E : disp_pregraph B) : UU
    := ∏ (x : B) (aa : E x), aa ≈[grefl x] aa.

  Definition disp_rxgraph := total2 has_disp_refl.
  Coercion disp_rxgraph_to_disp_pregraph (E : disp_rxgraph)
    : disp_pregraph B := pr1 E.
  Definition disp_grefl {E : disp_rxgraph}
    : ∏ (x : B) (aa : E x), aa ≈[grefl x] aa
    := pr2 E.

  Definition make_disp_rxgraph (E : disp_pregraph B)
    (refl : has_disp_refl E) : disp_rxgraph := E,,refl.

  Definition make_disp_rxgraph'
    (E : B -> UU)
    (edge : ∏ (a b : B) (e : edge B a b),
        E a -> E b -> UU)
    (refl : has_disp_refl (make_disp_pregraph E edge))
    : disp_rxgraph
    := make_disp_rxgraph _ refl.

  Definition disp_pregraph_fib (E : disp_pregraph B)
    (x : B) : pregraph.
  Proof.
    use make_pregraph.
    - exact (E x).
    - intros aa bb.
      exact (aa ≈[grefl x] bb).
  Defined.

  Definition disp_rxgraph_fib (E : disp_rxgraph)
    (x : B) : rxgraph.
  Proof.
    use (make_rxgraph (disp_pregraph_fib E x)).
    intro aa.
    exact (disp_grefl x aa).
  Defined.

  Definition total_rxgraph (E : disp_rxgraph) : rxgraph.
  Proof.
    use (make_rxgraph (total_pregraph E)).
    intros [x aa].
    exists (grefl x).
    exact (disp_grefl x aa).
  Defined.

  Definition is_disp_rxgraph_univalent (E : disp_rxgraph) : UU
    := ∏ (a : B), is_rxgraph_univalent (disp_rxgraph_fib E a).

  Lemma isaprop_is_disp_rxgraph_univalent (E : disp_rxgraph)
    : isaprop (is_disp_rxgraph_univalent E).
  Proof.
    apply impred; intro.
    apply isaprop_is_rxgraph_univalent.
  Qed.

End disprxgraph_defs.
Arguments disp_rxgraph : clear implicits.

Notation "aa '≈[' e ']' bb" := (disp_edge _ e aa bb) (at level 50, bb at next level) : rxgraph.

Section univalence_lemmas.
  Lemma weq_total2_over_contr {B : UU} (E : B -> UU) (ic : iscontr B)
    : total2 E ≃ E (iscontrpr1 ic).
  Proof.
    intermediate_weq (∑ (_ : unit), E (iscontrpr1 ic)).
    2: apply weqtotal2overunit.
    apply weqtotal2.
    1: apply weqcontrtounit, ic.
    intro x.
    apply (weqsecovercontr (λ x, E x ≃ E (iscontrpr1 ic)) ic).
    apply idweq.
  Defined.

  Theorem is_univalent_total_rxgraph {B : rxgraph} (E : disp_rxgraph B)
    (HB : is_rxgraph_univalent B)
    (HE : is_disp_rxgraph_univalent E)
    : is_rxgraph_univalent (total_rxgraph E).
  Proof.
    apply is_rxgraph_univalent_from_iscontr_edges_from.
    intros [x aa].
    use (isofhlevelweqb 0 (Y:=(edges_from (G:=disp_rxgraph_fib E x) aa))).
    - unfold edges_from.
      intermediate_weq (∑ (φ : edges_from x) (u : E (pr1 φ)), aa ≈[pr2 φ] u). {
        use weq_iso.
        1: intros [y [p pp]]; exists (_,,p); exact (_,,pp).
        1: intros [[y p] [u pp]]; exists (y,,u); exact (p,,pp).
        all: easy.
      }
      apply (weq_total2_over_contr (λ φ : edges_from x, ∑ u : E (pr1 φ), aa ≈[ pr2 φ] u)
               (is_rxgraph_univalent_to_iscontr_edges_from _ HB x)).
    - apply is_rxgraph_univalent_to_iscontr_edges_from, HE.
  Defined.

  Definition discrete_rxgraph (A : UU) : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact A.
    - intros a b.
      exact (a = b).
    - intros a.
      exact (idpath a).
  Defined.

  Lemma is_univalent_discrete_rxgraph (A : UU)
    : is_rxgraph_univalent (discrete_rxgraph A).
  Proof.
    intros a b.
    use isweqhomot.
    - apply idfun.
    - intro p; now induction p.
    - apply idisweq.
  Defined.

  Definition product_rxgraph {B : UU} (E : B -> rxgraph) : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact (∏ x, E x).
    - intros f g.
      exact (∏ x, f x ≈ g x).
    - intros f x.
      exact (grefl (f x)).
  Defined.

  Lemma weq_total2_sec_sec_total2 {B : UU} (E : B -> UU)
    (P : ∏ (x : B) (b : E x), UU)
    : (∑ b : ∏ x : B, E x, ∏ x : B, P x (b x))
        ≃ (∏ x : B, ∑ b : (E x), P x b).
  Proof.
    use weq_iso.
    - intros [g h] x; exact (_,,h x).
    - intros g; use tpair; intro x.
      + exact (pr1 (g x)).
      + exact (pr2 (g x)).
    - easy.
    - intros g.
      apply funextsec; intro x.
      reflexivity.
  Defined.

  Definition is_univalent_product_rxgraph {B : UU} (E : B -> rxgraph)
    (H : ∏ x, is_rxgraph_univalent (E x))
    : is_rxgraph_univalent (product_rxgraph E).
  Proof.
    use is_rxgraph_univalent_from_iscontr_edges_from.
    intro f.
    apply (isofhlevelweqb 0 (Y:= ∏ x, edges_from (f x))).
    - unfold edges_from; cbn.
      apply (weq_total2_sec_sec_total2
               (λ x, vertex (E x))
               (λ x b, edge (E x) (f x) b)).
    - apply impred; intro.
      apply is_rxgraph_univalent_to_iscontr_edges_from, H.
  Defined.

  Definition codiscrete_rxgraph (A : UU) : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact A.
    - intros _ _.
      exact unit.
    - intros a.
      exact tt.
  Defined.

  Lemma is_univalent_codiscrete_rxgraph (A : UU)
    (H : isaprop A)
    : is_rxgraph_univalent (codiscrete_rxgraph A).
  Proof.
    intros a b.
    use isweqhomot.
    - intro p; exact tt.
    - intro p; now induction p.
    - apply isweqcontrtounit, H.
  Qed.

  Definition forgetful_rxgraph (B : rxgraph) (P : B -> UU) : rxgraph.
  Proof.
    refine (@total_rxgraph B _).
    use make_disp_rxgraph; [use make_disp_pregraph|].
    - intro x; exact (P x).
    - intros a b e aa bb; exact unit.
    - intros a aa; exact tt.
  Defined.

  Lemma is_univalent_forgetful_rxgraph (B : rxgraph) (P : B -> UU)
    (HB : is_rxgraph_univalent B)
    (HP : isPredicate P)
    : is_rxgraph_univalent (forgetful_rxgraph B P).
  Proof.
    apply (is_univalent_total_rxgraph _ HB).
    intros a b e.
    use isweqhomot.
    - apply (@id_to_edge (codiscrete_rxgraph (P a))).
    - intros p; now induction p.
    - apply is_univalent_codiscrete_rxgraph, HP.
  Defined.

  Definition UU_rxgraph : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact UU.
    - intros a b; exact (weq a b).
    - intros a; exact (idweq a).
  Defined.

  Lemma is_univalent_UU_rxgraph : is_rxgraph_univalent UU_rxgraph.
  Proof.
    intros a b.
    use isweqhomot.
    - exact (@eqweqmap a b).
    - intro p; now induction p.
    - exact (univalenceAxiom a b).
  Defined.

  Definition dirprod_rxgraph (A B : rxgraph) : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact (A × B).
    - intros a b.
      exact (pr1 a ≈ pr1 b × pr2 a ≈ pr2 b).
    - intro a.
      exact (grefl (pr1 a),,grefl (pr2 a)).
  Defined.

  Lemma is_univalent_dirprod_rxgraph (A B : rxgraph)
    (HA : is_rxgraph_univalent A)
    (HB : is_rxgraph_univalent B)
    : is_rxgraph_univalent (dirprod_rxgraph A B).
  Proof.
    intros aa bb.
    use weqhomot.
    - apply (weqcomp pathsdirprodweq).
      apply weqdirprodf.
      + apply (make_weq _ (HA _ _)).
      + apply (make_weq _ (HB _ _)).
    - intro p; now induction p.
  Defined.

End univalence_lemmas.

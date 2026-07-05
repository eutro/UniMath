(********************************************************************************

 Reflexive Graphs

 Author: B. Szilvasy
 February 2026

 Contents:
 1. Definition of a reflexive graph
 1.1. Data
 1.2. Univalence
 1.2. Fundamental Theorem of Identity Types
 2. Definition of a displayed reflexive graph
 2.1. Displayed and total graphs
 2.2. Displayed and total reflexive graphs
 2.3. Univalence
 3. Uses of univalence
 4. Examples of univalent reflexive graphs
 5. Reflexive graph syntax with [G%rxgraph_spec]

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Graph.

Declare Scope rxgraph.
Delimit Scope rxgraph with rxgraph.
Local Open Scope rxgraph.

Notation "a '≈' b" := (edge _ a b) (at level 50) : rxgraph.

(** ** Definition of a Reflexive Graph *)

Section rxgraph_defs.
  (** *** Data *)

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

  Definition id_to_edge (G : rxgraph) (a b : G) (p : a = b) : a ≈ b.
  Proof. induction p. apply grefl. Defined.

  (** *** Univalence *)

  Definition is_rxgraph_univalent (G : rxgraph) : UU
    := ∏ a b, isweq (id_to_edge G a b).

  Definition weq_id_to_edge {G : rxgraph}
    (H : is_rxgraph_univalent G)
    (a b : G) : a = b ≃ a ≈ b
    := make_weq _ (H a b).

  Definition weq_edge_to_id {G : rxgraph}
    (H : is_rxgraph_univalent G)
    (a b : G) : a ≈ b ≃ a = b
    := invweq (weq_id_to_edge H a b).

  Definition edge_to_id {G : rxgraph}
    (H : is_rxgraph_univalent G)
    (a b : G) : a ≈ b -> a = b
    := invmap (weq_id_to_edge H a b).

  Lemma edge_to_id_grefl {G : rxgraph}
    (H : is_rxgraph_univalent G) (a : G)
    : idpath a = edge_to_id H a a (grefl a).
  Proof.
    apply pathsweq1.
    reflexivity.
  Defined.

  Lemma isaprop_is_rxgraph_univalent (G : rxgraph)
    : isaprop (is_rxgraph_univalent G).
  Proof.
    do 2 (apply impred; intro).
    apply isapropisweq.
  Qed.

  Definition univalent_rxgraph := total2 is_rxgraph_univalent.
  Definition make_univalent_rxgraph
    (G : rxgraph) (H : is_rxgraph_univalent G)
    : univalent_rxgraph := G,,H.
  Coercion univalent_rxgraph_to_rxgraph (G : univalent_rxgraph) : rxgraph := pr1 G.
  Coercion rxgraph_univalence (G : univalent_rxgraph) : is_rxgraph_univalent G := pr2 G.

  Definition edges_from {G : pregraph} (a : vertex G) : UU := ∑ (b : vertex G), a ≈ b.
  Definition edges_to {G : pregraph} (a : vertex G) : UU := ∑ (b : vertex G), b ≈ a.

  Lemma edges_from_grefl {G : rxgraph} (a : G) : edges_from a.
  Proof. exists a; apply grefl. Defined.
  Lemma edges_to_grefl {G : rxgraph} (a : G) : edges_to a.
  Proof. exists a; apply grefl. Defined.

  (** *** Fundamental Theorem of Identity Types

This is a variant of that from Egbert Rijke's "Introduction to Homotopy Type
Theory", (DOI:10.1017/9781108933568, arXiv:2212.11082).

Let [G] be a reflexive graph. The following are equivalent.
1. [G] is univalent.
2. Every [edges_from a] (or [edges_to a]) for [a : G] is a proposition.
3. Every [edges_from a] (or [edges_to a]) for [a : G] is contractible with centre
   [edges_*_grefl a].
   *)

  (** 3 -> 1 *)
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

  (** 2 -> 1 *)
  Lemma is_rxgraph_univalent_from_isaprop_edges_from (G : rxgraph)
    (H : ∏ (a : G), isaprop (edges_from a))
    : is_rxgraph_univalent G.
  Proof.
    apply is_rxgraph_univalent_from_iscontr_edges_from.
    intro a.
    apply iscontraprop1; [|apply edges_from_grefl].
    apply H.
  Defined.

  (** 1 -> 2 *)
  Lemma is_rxgraph_univalent_to_isaprop_edges_from (G : rxgraph)
    (H : is_rxgraph_univalent G)
    : ∏ (a : G), isaprop (edges_from a).
  Proof.
    intro a.
    apply (isofhlevelweqb 1 (Y:=paths_from a)).
    - refine (make_weq _ (isweqfibtototal _ _ _)).
      intro b.
      apply weq_edge_to_id, H.
    - apply isapropifcontr, iscontr_paths_from.
  Qed. (* [isaprop] should not be used transparently *)

  (** 1 -> 3 *)
  Lemma is_rxgraph_univalent_to_iscontr_edges_from (G : rxgraph)
    (H : is_rxgraph_univalent G)
    : ∏ (a : G), iscontr (edges_from a).
  Proof.
    intro a.
    apply iscontraprop1; [|apply edges_from_grefl].
    apply is_rxgraph_univalent_to_isaprop_edges_from, H.
  Defined.

  (** 3 ([edges_to]) -> 3 ([edges_from]) *)
  Lemma isaprop_edges_to_implies_isaprop_edges_from (G : rxgraph)
    (H : ∏ (a : G), isaprop (edges_to a))
    : ∏ (a : G), isaprop (edges_from a).
  Proof.
    intro a; apply invproofirrelevance.
    intros [b₁ e₁] [b₂ e₂].
    assert (p : edges_to_grefl _ = a,,e₁); [apply H|].
    apply total2_paths_equiv in p.
    induction p as [p q]; cbn in *.
    induction p; cbn in q.
    induction q.
    assert (p : edges_to_grefl _ = b₁,,e₂); [apply H|].
    apply total2_paths_equiv in p.
    induction p as [p q]; cbn in *.
    induction p; cbn in q.
    induction q.
    reflexivity.
  Qed.

  (** 3 ([edges_from]) -> 3 ([edges_to]) *)
  Lemma isaprop_edges_from_implies_isaprop_edges_to (G : rxgraph)
    (H : ∏ (a : G), isaprop (edges_from a))
    : ∏ (a : G), isaprop (edges_to a).
  Proof.
    intro a; apply invproofirrelevance.
    intros [b₁ e₁] [b₂ e₂].
    assert (p : edges_from_grefl _ = a,,e₁); [apply H|].
    apply total2_paths_equiv in p.
    induction p as [p q]; cbn in *.
    induction p; cbn in q.
    induction q.
    assert (p : edges_from_grefl _ = b₁,,e₂); [apply H|].
    apply total2_paths_equiv in p.
    induction p as [p q]; cbn in *.
    induction p; cbn in q.
    induction q.
    reflexivity.
  Qed.

  (** 2 -> 1 *)
  Lemma is_rxgraph_univalent_from_isaprop_edges_to (G : rxgraph)
    (H : ∏ (a : G), isaprop (edges_to a))
    : is_rxgraph_univalent G.
  Proof.
    use is_rxgraph_univalent_from_isaprop_edges_from.
    exact (isaprop_edges_to_implies_isaprop_edges_from _ H).
  Defined.

  (** 3 -> 1 *)
  Lemma is_rxgraph_univalent_from_iscontr_edges_to (G : rxgraph)
    (H : ∏ (a : G), iscontr (edges_to a))
    : is_rxgraph_univalent G.
  Proof.
    use is_rxgraph_univalent_from_isaprop_edges_to.
    intro a; apply isapropifcontr, H.
  Defined.

  (** 1 -> 2 *)
  Lemma is_rxgraph_univalent_to_isaprop_edges_to (G : rxgraph)
    (H : is_rxgraph_univalent G)
    : ∏ (a : G), isaprop (edges_to a).
  Proof.
    use isaprop_edges_from_implies_isaprop_edges_to.
    use is_rxgraph_univalent_to_isaprop_edges_from.
    exact H.
  Qed.

  (** 1 -> 3 *)
  Lemma is_rxgraph_univalent_to_iscontr_edges_to (G : rxgraph)
    (H : is_rxgraph_univalent G)
    : ∏ (a : G), iscontr (edges_to a).
  Proof.
    intro a; apply iscontraprop1.
    - apply is_rxgraph_univalent_to_isaprop_edges_to, H.
    - apply edges_to_grefl.
  Defined.

End rxgraph_defs.

(** ** Definition of a displayed reflexive graph *)

Section disprxgraph_defs.
  (** *** Displayed and total graphs *)

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

  (** *** Displayed and total reflexive graphs *)

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

  (** *** Univalence *)

  Definition is_disp_rxgraph_univalent (E : disp_rxgraph) : UU
    := ∏ (a : B), is_rxgraph_univalent (disp_rxgraph_fib E a).

  Lemma isaprop_is_disp_rxgraph_univalent (E : disp_rxgraph)
    : isaprop (is_disp_rxgraph_univalent E).
  Proof.
    apply impred; intro.
    apply isaprop_is_rxgraph_univalent.
  Qed.

  Definition univalent_disp_rxgraph := total2 is_disp_rxgraph_univalent.
  Coercion univalent_disp_rxgraph_to_disp_rxgraph (E : univalent_disp_rxgraph) : disp_rxgraph := pr1 E.
  Coercion disp_rxgraph_univalence (E : univalent_disp_rxgraph) : is_disp_rxgraph_univalent E := pr2 E.
  Definition make_univalent_disp_rxgraph
    (E : disp_rxgraph) (H : is_disp_rxgraph_univalent E)
    : univalent_disp_rxgraph := E,,H.

  Definition disp_rxgraph_fib' (E : univalent_disp_rxgraph)
    (x : B) : univalent_rxgraph.
  Proof.
    exact (make_univalent_rxgraph _ (disp_rxgraph_univalence E x)).
  Defined.

End disprxgraph_defs.
Arguments disp_rxgraph : clear implicits.
Arguments univalent_disp_rxgraph : clear implicits.

Notation "aa '≈[' e ']' bb" := (disp_edge _ e aa bb) (at level 50, bb at next level) : rxgraph.

(** ** Uses of univalence *)

Section univalence_uses.

  (** Biased induction on [a ≈ b] handling [grefl a : a ≈ a]. *)

  Definition edges_from_eq_grefl {G : rxgraph}
    (H : is_rxgraph_univalent G)
    (a : G) (φ : edges_from a)
    : edges_from_grefl a = φ.
  Proof.
    apply proofirrelevance.
    apply is_rxgraph_univalent_to_isaprop_edges_from, H.
  Qed.

  Definition edges_from_eq_grefl_eq_refl {G : rxgraph}
    (H : is_rxgraph_univalent G)
    (a : G)
    : edges_from_eq_grefl H a (edges_from_grefl a) = idpath _.
  Proof.
    apply proofirrelevancecontr.
    apply is_rxgraph_univalent_to_isaprop_edges_from, H.
  Qed.

  Definition rxgraph_edges_from_rect {G : rxgraph}
    (H : is_rxgraph_univalent G)
    (a : G) (P : edges_from a -> UU)
    (refl : P (edges_from_grefl a))
    : ∏ (φ : edges_from a), P φ.
  Proof.
    intro φ.
    exact (transportf (λ φ, P φ)
             (edges_from_eq_grefl H a φ)
             refl).
  Defined.

  Definition rxgraph_edges_from_rect_grefl {G : rxgraph}
    (H : is_rxgraph_univalent G)
    (a : G) (P : edges_from a -> UU)
    (refl : P (edges_from_grefl a))
    : rxgraph_edges_from_rect H a P refl (edges_from_grefl a) = refl.
  Proof.
    exact (transportb (λ p, transportf P p refl = refl)
             (edges_from_eq_grefl_eq_refl H a)
             (idpath _)).
  Defined.

  Definition rxgraph_edges_from_rect' {G : univalent_rxgraph}
    : ∏ (a : G) (P : edges_from a -> UU)
        (refl : P (edges_from_grefl a))
        (φ : edges_from a), P φ
    := rxgraph_edges_from_rect G.

  Definition rxgraph_edge_rect {G : rxgraph}
    (H : is_rxgraph_univalent G)
    (a : G) (P : ∏ (b : G), a ≈ b -> UU)
    (refl : P a (grefl a))
    : ∏ (b : G) (p : a ≈ b), P b p.
  Proof.
    intros b p.
    exact (rxgraph_edges_from_rect H a
             (λ φ, P (pr1 φ) (pr2 φ))
             refl (b,,p)).
  Defined.

  Lemma rxgraph_edge_rect_grefl {G : rxgraph}
    (H : is_rxgraph_univalent G)
    (a : G) (P : ∏ (b : G), a ≈ b -> UU)
    (refl : P a (grefl a))
    : rxgraph_edge_rect H a P refl a (grefl a) = refl.
  Proof. use rxgraph_edges_from_rect_grefl. Defined.

  Definition rxgraph_edge_rect' {G : univalent_rxgraph}
    : ∏ (a : G) (P : ∏ (b : G), a ≈ b -> UU)
        (refl : P a (grefl a))
        (b : G) (p : a ≈ b), P b p
    := rxgraph_edge_rect G.

  (** *** Inverting edges *)

  Definition rxgraph_edge_inv {G : rxgraph} (H : is_rxgraph_univalent G) {a b : G}
    (e : a ≈ b) : b ≈ a.
  Proof.
    induction b, e using (rxgraph_edge_rect H a).
    apply grefl.
  Defined.

  Definition rxgraph_edge_inv_refl {G : rxgraph} (H : is_rxgraph_univalent G)
    (a : G) : rxgraph_edge_inv H (grefl a) = grefl a.
  Proof. use rxgraph_edge_rect_grefl. Defined.

  Definition rxgraph_edge_inv_inv {G : rxgraph} (H : is_rxgraph_univalent G)
    {a b : G} (e : a ≈ b)
    : rxgraph_edge_inv H (rxgraph_edge_inv H e) = e.
  Proof.
    induction b, e using (rxgraph_edge_rect H a).
    etrans; [apply maponpaths, rxgraph_edge_inv_refl|].
    apply rxgraph_edge_inv_refl.
  Defined.

End univalence_uses.

(** ** Examples of univalent reflexive graphs *)

Section constructions.
  (** The total reflexive graph of a univalent displayed reflexive graph over a
  univalent base is univalent. *)

  Theorem is_univalent_total_rxgraph {B : rxgraph} (E : disp_rxgraph B)
    (HB : is_rxgraph_univalent B)
    (HE : is_disp_rxgraph_univalent E)
    : is_rxgraph_univalent (total_rxgraph E).
  Proof.
    intros aa bb.
    use weqhomot.
    - eapply weqcomp; [apply total2_paths_equiv|].
      use weqbandf; cbn.
      + apply (weq_id_to_edge HB).
      + intro e.
        induction aa as [x aa], bb as [y bb]; cbn in e.
        induction e.
        exact (make_weq _ (HE x aa bb)).
    - intro p; now induction p.
  Defined.

  Definition univalent_total_rxgraph
    {B : univalent_rxgraph}
    (E : univalent_disp_rxgraph B)
    : univalent_rxgraph
    := make_univalent_rxgraph _ (is_univalent_total_rxgraph E B E).

  (** Every type [A] has a univalent reflexive graph [ΔA] whose edges are
  identifications. *)

  Definition discrete_rxgraph0 (A : UU) : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact A.
    - intros a b.
      exact (a = b).
    - intros a.
      exact (idpath a).
  Defined.

  Lemma is_univalent_discrete_rxgraph (A : UU)
    : is_rxgraph_univalent (discrete_rxgraph0 A).
  Proof.
    intros a b.
    use isweqhomot.
    - apply idfun.
    - intro p; now induction p.
    - apply idisweq.
  Defined.

  Definition discrete_rxgraph (A : UU) : univalent_rxgraph
    := make_univalent_rxgraph _ (is_univalent_discrete_rxgraph A).

  (** A family of reflexive graphs [x : B ⊢ E[x]] gives rise to a univalent
  reflexive graph whose vertices are [∏ x, E[x]]. *)

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

  Definition product_rxgraph' {B : UU} (E : B -> univalent_rxgraph) : univalent_rxgraph
    := make_univalent_rxgraph _ (is_univalent_product_rxgraph E (λ x, E x)).

  (** Every type [A] gives rise to a reflexive graph whose vertices are [A] and
  edges are the unit. This is univalent iff [A] is a proposition. *)

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

  Lemma isaprop_from_is_univalent_codiscrete_rxgraph (A : UU)
    (H : is_rxgraph_univalent (codiscrete_rxgraph A))
    : isaprop A.
  Proof.
    apply invproofirrelevance.
    intros a b.
    exact (edge_to_id H a b tt).
  Qed.

  Definition codiscrete_rxgraph' (A : UU) (H : isaprop A) : univalent_rxgraph
    := make_univalent_rxgraph _ (is_univalent_codiscrete_rxgraph A H).

  Definition prop_rxgraph (A : hProp) : univalent_rxgraph
    := codiscrete_rxgraph' A (propproperty A).

  (** Given a predicate [x : B ⊢ P[x]] over the vertices of a reflexive graph [B], the
   forgetful reflexive graph [{ x : B ∇ P x }] has the vertices of [B] satisfying [P],
   and the same edges as [B]. *)

  Definition forgetful_rxgraph0 (B : rxgraph) (P : B -> UU) : rxgraph.
  Proof.
    refine (@total_rxgraph B _).
    use make_disp_rxgraph; [use make_disp_pregraph|].
    - intro x; exact (P x).
    - intros a b e aa bb; exact unit.
    - intros a aa; exact tt.
  Defined.

  Lemma is_univalent_forgetful_rxgraph0 (B : rxgraph) (P : B -> UU)
    (HB : is_rxgraph_univalent B)
    (HP : isPredicate P)
    : is_rxgraph_univalent (forgetful_rxgraph0 B P).
  Proof.
    apply (is_univalent_total_rxgraph _ HB).
    intro a.
    exact (rxgraph_univalence
             (codiscrete_rxgraph' (P a) (HP a))).
  Defined.

  Definition forgetful_rxgraph (B : rxgraph) (P : B -> UU) : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact (total2 P).
    - intros a b; exact (pr1 a ≈ pr1 b).
    - intros a; exact (grefl (pr1 a)).
  Defined.

  Definition is_univalent_forgetful_rxgraph (B : rxgraph) (P : B -> UU)
    (HB : is_rxgraph_univalent B)
    (HP : isPredicate P)
    : is_rxgraph_univalent (forgetful_rxgraph B P).
  Proof.
    intros a b.
    use weqhomot.
    - eapply weqcomp; [apply total2_paths_equiv|].
      eapply weqcomp.
      2: apply (total2_contr (λ _, unit)); intro; apply iscontrunit.
      apply weqbandf.
      + apply (weq_id_to_edge HB).
      + intro e.
        apply weqcontrtounit, HP.
    - intro p; now induction p.
  Defined.

  Definition forgetful_rxgraph' (B : univalent_rxgraph) (P : B -> hProp) : univalent_rxgraph.
  Proof.
    refine (make_univalent_rxgraph _ (is_univalent_forgetful_rxgraph B (λ x, P x) _ _)).
    - apply rxgraph_univalence.
    - intro x; apply propproperty.
  Defined.

  (** The reflexive graph [UU_rxgraph] has types as vertices, and edges
  [weq]s. Univalence of [UU_rxgraph] is the univalence axiom. *)

  Definition UU_rxgraph0 : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact UU.
    - intros a b; exact (weq a b).
    - intros a; exact (idweq a).
  Defined.

  Definition UU_rxgraph : univalent_rxgraph
    := make_univalent_rxgraph UU_rxgraph0 univalenceAxiom.

  Definition pregraph_rxgraph : univalent_rxgraph.
  Proof.
    use (@univalent_total_rxgraph UU_rxgraph).
    use make_univalent_disp_rxgraph.
    1: use make_disp_rxgraph'.
    - intro N.
      exact (product_rxgraph (λ _ : N,
                   product_rxgraph (λ _ : N,
                         UU_rxgraph))).
    - intros N M p aa bb.
      cbn in p.
      exact (∏ (a b : N), aa a b ≃ bb (p a) (p b)).
    - intros N aa.
      exact (λ (a b : N), idweq (aa a b)).
    - intro N.
      exact (rxgraph_univalence
               (product_rxgraph' (λ _ : N,
                      product_rxgraph' (λ _ : N,
                            UU_rxgraph)))).
  Defined.

  (** The reflexive graph of graphs. *)

  Definition pregraph_iso (G G' : pregraph)
    := (* edge pregraph_rxgraph G G' *)
    ∑ (e : vertex G ≃ vertex G'), ∏ a b, edge G a b ≃ edge G' (e a) (e b).
  Coercion pregraph_iso_vertex_weq {G G' : pregraph} (f : pregraph_iso G G')
    : vertex G ≃ vertex G' := pr1 f.
  Definition edge_weq {G G' : pregraph} (f : pregraph_iso G G')
    : ∏ {a b : vertex G}, edge G a b ≃ edge G' (f a) (f b)
    := pr2 f.

  Definition make_pregraph_iso {G G' : pregraph}
    (f : vertex G ≃ vertex G')
    (e : ∏ (a b : vertex G), edge G a b ≃ edge G' (f a) (f b))
    : pregraph_iso G G' := f,,e.

  (** The reflexive graph of reflexive graphs. *)

  Definition has_refl_rxgraph : univalent_disp_rxgraph pregraph_rxgraph.
  Proof.
    use make_univalent_disp_rxgraph.
    1: use make_disp_rxgraph'.
    - exact has_refl.
    - intros G G' e Gid G'id.
      change (pregraph_iso G G') in e.
      exact (∏ (a : vertex G), edge_weq e (Gid a) = G'id (e a)).
    - intros G Gid.
      exact (homotrefl Gid).
    - intro G.
      exact (rxgraph_univalence
               (product_rxgraph' (λ (a : vertex G),
                    discrete_rxgraph (edge G a a)))).
  Defined.

  Definition rxgraph_rxgraph : univalent_rxgraph
    := univalent_total_rxgraph has_refl_rxgraph.

  (** Univalence of isomorphic reflexive graphs *)

  Definition rxgraph_iso (G G' : rxgraph)
    := (* edge rxgraph_rxgraph G G' *)
    ∑ (e : pregraph_iso G G'), ∏ (a : vertex G), edge_weq e (grefl a) = grefl (e a).
  Coercion rxgraph_iso_to_pregraph_iso {G G' : rxgraph} (f : rxgraph_iso G G')
    : pregraph_iso G G' := pr1 f.
  Definition rxgraph_iso_grefl {G G' : rxgraph} (f : rxgraph_iso G G')
    : ∏ (a : G), edge_weq f (grefl a) = grefl (f a) := pr2 f.

  Goal ∏ G G', edge rxgraph_rxgraph G G' = rxgraph_iso G G'. easy. Qed.

  Definition make_rxgraph_iso {G G' : rxgraph}
    (f : pregraph_iso G G')
    (H : ∏ (a : G), edge_weq f (grefl a) = grefl (f a))
    : rxgraph_iso G G' := f,,H.

  Definition pregraph_iso_inv {G G' : pregraph}
    (f : pregraph_iso G G')
    : pregraph_iso G' G.
  Proof.
    use make_pregraph_iso.
    - exact (invweq f).
    - intros a b.
      use invweq.
      intermediate_weq (f (invweq f a) ≈ f (invweq f b)).
      1: exact (edge_weq f).
      intermediate_weq (a ≈ f (invweq f b)).
      1: exact (make_weq _ (isweqtransportf (λ a', a' ≈ _) (homotweqinvweq f a))).
      exact (make_weq _ (isweqtransportf (λ b', _ ≈ b') (homotweqinvweq f b))).
  Defined.

  Definition rxgraph_iso_inv {G G' : rxgraph}
    (f : rxgraph_iso G G')
    : rxgraph_iso G' G.
  Proof.
    use (make_rxgraph_iso (pregraph_iso_inv f)).
    intro a.
    use pathsinv0; use pathsweq1.
    induction (homotweqinvweq f a).
    cbn.
    use (rxgraph_iso_grefl f).
  Defined.

  Definition pregraph_iso_to_edges_from_iso {G G' : pregraph}
    (f : pregraph_iso G G')
    : ∏ a, edges_from a ≃ edges_from (f a).
  Proof.
    intro a.
    use weqbandf.
    - exact f.
    - intro b; exact (edge_weq f).
  Defined.

  Definition rxgraph_univalent_from_iso_b'
    {G : rxgraph} (G' : rxgraph)
    (H : is_rxgraph_univalent G')
    (e : pregraph_iso G G')
    : is_rxgraph_univalent G.
  Proof.
    use is_rxgraph_univalent_from_isaprop_edges_from; intro a.
    use (isofhlevelweqb 1 (Y:=edges_from (e a))).
    2: use (is_rxgraph_univalent_to_isaprop_edges_from _ H).
    exact (pregraph_iso_to_edges_from_iso e a).
  Qed.

  Definition rxgraph_univalent_from_iso_f'
    (G : rxgraph) {G' : rxgraph}
    (H : is_rxgraph_univalent G)
    (e : pregraph_iso G G')
    : is_rxgraph_univalent G'.
  Proof.
    use is_rxgraph_univalent_from_isaprop_edges_from; intro a.
    use (isofhlevelweqf 1 (X:=edges_from (invweq e a))).
    2: use (is_rxgraph_univalent_to_isaprop_edges_from _ H).
    use invweq.
    exact (pregraph_iso_to_edges_from_iso (pregraph_iso_inv e) a).
  Qed.

  Definition rxgraph_univalent_from_iso_b
    {G : rxgraph} (G' : rxgraph)
    (H : is_rxgraph_univalent G')
    (e : rxgraph_iso G G')
    : is_rxgraph_univalent G.
  Proof.
    Succeed now induction G', e using (rxgraph_edge_rect rxgraph_rxgraph G).
    exact (rxgraph_univalent_from_iso_b' G' H e).
  Defined.

  Definition rxgraph_univalent_from_iso_f
    (G : rxgraph) {G' : rxgraph}
    (H : is_rxgraph_univalent G)
    (e : rxgraph_iso G G')
    : is_rxgraph_univalent G'.
  Proof.
    Succeed now induction G', e using (rxgraph_edge_rect rxgraph_rxgraph G).
    exact (rxgraph_univalent_from_iso_f' G H e).
  Defined.

  (** Direct product reflexive graph [A × B]. *)

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

  Definition dirprod_rxgraph' (A B : univalent_rxgraph) : univalent_rxgraph
    := make_univalent_rxgraph _ (is_univalent_dirprod_rxgraph _ _ A B).

  (** Opposite reflexive graph [G^opp]. *)

  Definition opp_rxgraph (A : rxgraph) : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact A.
    - intros a b.
      exact (b ≈ a).
    - intro a.
      exact (grefl a).
  Defined.

  Lemma opp_opp_rxgraph (A : rxgraph) : opp_rxgraph (opp_rxgraph A) = A.
  Proof. reflexivity. Defined.

  Lemma is_univalent_opp_rxgraph (A : rxgraph)
    (HA : is_rxgraph_univalent A)
    : is_rxgraph_univalent (opp_rxgraph A).
  Proof.
    apply is_rxgraph_univalent_from_isaprop_edges_from.
    change (∏ a : A, isaprop (edges_to a)).
    apply is_rxgraph_univalent_to_isaprop_edges_to.
    exact HA.
  Defined.

  Definition opp_rxgraph' (A : univalent_rxgraph) : univalent_rxgraph
    := make_univalent_rxgraph _ (is_univalent_opp_rxgraph _ A).

End constructions.

(** Reflexive graph syntax with [G%rxgraph_spec] *)

Declare Scope rxgraph_spec.
Delimit Scope rxgraph_spec with rxgraph_spec.

Notation "'∏' x .. y , G" :=
  (product_rxgraph' (λ x, .. (product_rxgraph' (λ y, G)) ..)) : rxgraph_spec.
(* type in Emacs using agda-input with \prod *)
Notation "'∏0' x .. y , G" :=
  (product_rxgraph (λ x, .. (product_rxgraph (λ y, G)) ..))
    (at level 200, x binder, y binder, right associativity) : rxgraph_spec.
(* type in Emacs using agda-input with \prod 0 *)
Notation "'Δ' T" := (discrete_rxgraph T) (at level 200) : rxgraph_spec.
(* type in Emacs using agda-input with \Delta *)
Notation "'∇' T" := (prop_rxgraph T) (at level 200) : rxgraph_spec.
(* type in Emacs using agda-input with \nabla *)
Notation "'∇0' T" := (codiscrete_rxgraph T) (at level 200) : rxgraph_spec.
(* type in Emacs using agda-input with \nabla 0 *)
Notation "A × B" := (dirprod_rxgraph' A B) : rxgraph_spec.
(* type in Emacs using agda-input with \times *)
Notation "A '×0' B" := (dirprod_rxgraph A B)
    (at level 75) : rxgraph_spec.
(* type in Emacs using agda-input with \times *)
Notation "G ⟦ x ⟧" := (disp_rxgraph_fib' G x) : rxgraph_spec.
(* type in Emacs using agda-input with \[ and \] *)
Notation "G '0⟦' x ⟧" := (disp_rxgraph_fib G x)
    (at level 49) : rxgraph_spec.
(* type in Emacs using agda-input with \[ and \] *)

Notation "{ x ∇ G }" :=
  (forgetful_rxgraph' _ (λ x, G))
    (x binder) : rxgraph_spec.
(* type in Emacs using agda-input with { .. \nabla .. } *)
Notation "{ x ∇0 G }" :=
  (forgetful_rxgraph _ (λ x, G))
    (x binder) : rxgraph_spec.
(* type in Emacs using agda-input with { .. \nabla 0 .. } *)

Notation "x '^op'" := (opp_rxgraph' x) : rxgraph_spec.
Notation "x '^op0'" := (opp_rxgraph x) : rxgraph_spec.

(********************************************************************************

 Univalence of Duploids

 Author: B. Szilvasy
 January 2026

 We define what it means for a duploid to be univalent both as a single-sorted
 duploid ([is_duploid_univalent]), and as a split duploid
 ([is_split_duploid_univalent]). We show that the former makes shifts a
 property, and show that identifications of unital magmoids correspond to weak
 equivalences.

 Contents:
 1. Definition of univalence for Duploids
 2. Consequences of univalence
 3. External univalence
 4. Characterizations of univalence
 5. Split duploids and univalence

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.RXGraph.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.TwoSorted.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Isos.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

(** ** 1. Definition of univalence for Duploids *)
Section univalence_def.
  Definition is_duploid_univalent (M : unital_magmoid)
    := ∏ (a b : M), isweq (λ (p : a = b), id_to_lt_iso p).

  Definition lt_iso_to_id {M : unital_magmoid}
    (ua : is_duploid_univalent M) {a b : M}
    : lt_iso a b -> a = b
    := invmap (make_weq _ (ua a b)).

  Lemma id_to_lt_iso_after_lt_iso_to_id {M : unital_magmoid}
    (ua : is_duploid_univalent M) (a b : M) (f : lt_iso a b)
    : id_to_lt_iso (lt_iso_to_id ua f) = f.
  Proof. exact (homotweqinvweq (make_weq _ (ua a b)) f). Qed.

  Lemma lt_iso_to_id_after_id_to_lt_iso {M : unital_magmoid}
    (ua : is_duploid_univalent M) (a b : M) (p : a = b)
    : lt_iso_to_id ua (id_to_lt_iso p) = p.
  Proof. exact (homotinvweqweq (make_weq _ (ua a b)) p). Qed.

  Lemma id_to_lt_iso_postcompose {M : unital_magmoid} (a b b' : M)
    (p : b = b') (f : a --> b)
    : f · id_to_lt_iso p = transportf (λ b, a --> b) p f.
  Proof. induction p; apply magmoid_id_right. Qed.

  Lemma id_to_lt_iso_precompose {M : unital_magmoid} (a a' b : M)
    (p : a = a') (f : a --> b)
    : id_to_lt_iso (!p) · f = transportf (λ a, a --> b) p f.
  Proof. induction p; apply magmoid_id_left. Qed.

  Definition id_to_lt_iso_mor {M : unital_magmoid} {a b : M}
    (p : a = b) : lt_iso_mor (id_to_lt_iso p) = idtomor _ _ p.
  Proof. now induction p. Qed.

  Lemma id_to_lt_iso_inv {M : unital_magmoid} (a a' : M)
    (p : a = a') : id_to_lt_iso (!p) = lt_iso_inv (id_to_lt_iso p).
  Proof.
    apply lt_iso_eq.
    now induction p.
  Qed.

  Lemma lt_iso_to_id_precompose {M : unital_magmoid}
    (ua : is_duploid_univalent M) {a a' b : M}
    (p : lt_iso a a') (f : a --> b)
    : transportf (λ a, a --> b) (lt_iso_to_id ua p) f = lt_iso_inverse p · f.
  Proof.
    rewrite <- id_to_lt_iso_precompose, id_to_lt_iso_inv.
    now rewrite id_to_lt_iso_after_lt_iso_to_id.
  Qed.

  Lemma lt_iso_to_id_postcompose {M : unital_magmoid}
    (ua : is_duploid_univalent M) {a b b' : M}
    (p : lt_iso b b') (f : a --> b)
    : transportf (λ b, a --> b) (lt_iso_to_id ua p) f = f · p.
  Proof.
    rewrite <- id_to_lt_iso_postcompose.
    now rewrite id_to_lt_iso_after_lt_iso_to_id.
  Qed.

  Definition is_split_duploid_univalent (D : split_preduploid)
    := is_univalent D⁺ᶜₜ × is_univalent D⁻ᶜₗ.

End univalence_def.

(** ** 2. Consequences of univalence *)
Section univalence_consequences.
  Lemma isaprop_is_duploid_univalent (M : unital_magmoid)
    : isaprop (is_duploid_univalent M).
  Proof. do 2 (apply impred; intro); apply isapropisweq. Qed.

  (** Polarity shifts become properties in a univalent duploid. *)

  Lemma isaprop_has_negative_shifts (M : unital_magmoid)
    (ua : is_duploid_univalent M)
    : isaprop (has_negative_shifts M).
  Proof.
    apply isaproptotal2; [intro; apply isaprop_negative_shift_axioms|].
    intros U1 U2 H1 H2.
    use negative_shift_data_eq.
    - intro a.
      apply (lt_iso_to_id ua).
      apply (upshift_unique_up_to_lt_iso M (U1,,H1) (U2,,H2) a).
    - intro a; cbn.
      etrans; [apply lt_iso_to_id_precompose|].
      apply (force_unique_up_to_lt_iso M (U2,,H2) (U1,,H1) a).
  Qed.

  Lemma isaprop_has_positive_shifts (M : unital_magmoid)
    (ua : is_duploid_univalent M)
    : isaprop (has_positive_shifts M).
  Proof.
    apply isaproptotal2; [intro; apply isaprop_positive_shift_axioms|].
    intros U1 U2 H1 H2.
    use positive_shift_data_eq.
    - intro a.
      apply (lt_iso_to_id ua).
      apply (downshift_unique_up_to_lt_iso M (U1,,H1) (U2,,H2) a).
    - intro a; cbn.
      etrans; [apply lt_iso_to_id_postcompose|].
      apply (wrap_unique_up_to_lt_iso M (U2,,H2) (U1,,H1) a).
  Qed.

  Lemma isaprop_has_polarity_shifts (M : unital_magmoid) (ua : is_duploid_univalent M)
    : isaprop (has_polarity_shifts M).
  Proof.
    apply isapropdirprod.
    - apply isaprop_has_negative_shifts, ua.
    - apply isaprop_has_positive_shifts, ua.
  Qed.
End univalence_consequences.

(** ** 3. External univalence *)
Section equivalences.
  Lemma preduploid_rxgraph : univalent_rxgraph.
  Proof.
    simple refine ({ M : unital_magmoid_rxgraph ∇ make_hProp _ _ })%rxgraph_spec.
    change unital_magmoid in M.
    - exact (has_polarities M).
    - apply isaprop_has_polarities.
  Defined.

  Lemma univalent_preduploid_rxgraph : univalent_rxgraph.
  Proof.
    simple refine ({ M : preduploid_rxgraph ∇ make_hProp _ _ })%rxgraph_spec.
    change preduploid in M.
    - exact (is_duploid_univalent M).
    - apply isaprop_is_duploid_univalent.
  Defined.

  Lemma univalent_duploid_rxgraph0 : univalent_rxgraph.
  Proof.
    simple refine ({ D : univalent_preduploid_rxgraph ∇ _ })%rxgraph_spec.
    induction D as [D ua].
    change preduploid in D.
    use make_hProp.
    - exact (has_polarity_shifts D).
    - apply isaprop_has_polarity_shifts, ua.
  Defined.

  Definition univalent_duploid :=
    ∑ (D : duploid), is_duploid_univalent D.
  Coercion univalent_duploid_to_duploid (D : univalent_duploid) : duploid := pr1 D.
  Definition duploid_univalence (D : univalent_duploid) : is_duploid_univalent D := pr2 D.

  Lemma univalent_duploid_rxgraph1 : univalent_rxgraph.
  Proof.
    use make_univalent_rxgraph.
    1: use make_rxgraph'.
    - exact univalent_duploid.
    - intros a b; exact (catiso a b).
    - intros a; exact (identity_catiso a).
    - use (rxgraph_univalent_from_iso_b' univalent_duploid_rxgraph0).
      1: apply rxgraph_univalence.
      use make_pregraph_iso; cbn.
      + use weq_iso.
        * intros [[M H1] H2]; exists (M,,H2); exact H1.
        * intros [[M H2] H1]; exists (M,,H1); exact H2.
        * easy.
        * easy.
      + intros a b; exact (idweq _).
  Defined.

  Lemma isweq_on_objects_from_equivalence (D D' : preduploid)
    (ua : is_duploid_univalent D) (ua' : is_duploid_univalent D')
    (F : duploid_equivalence D D')
    : isweq (functor_on_objects F).
  Proof.
    use isweq_iso.
    - exact (functor_on_objects (duploid_equivalence_inverse F)).
    - intro a; apply ua.
      exact (lt_surjective_inverse_ob_iso _ (duploid_equivalence_inverse F) a).
    - intro a; apply ua'.
      exact (lt_surjective_inverse_ob_iso _ F a).
  Defined.

  Lemma is_catiso_from_is_duploid_equivalence (D D' : preduploid)
    (ua : is_duploid_univalent D) (ua' : is_duploid_univalent D')
    (F : D ⟶ D') (HF : is_duploid_equivalence F)
    : is_catiso F.
  Proof.
    split.
    - exact HF.
    - exact (isweq_on_objects_from_equivalence _ _ ua ua' (F,,HF)).
  Defined.

  Lemma is_duploid_equivalence_from_is_catiso (D D' : preduploid)
    (F : D ⟶ D') (HF : is_catiso F)
    : is_duploid_equivalence F.
  Proof.
    split.
    - exact (pr1 HF).
    - intro a.
      exists (invmap (catiso_ob_weq (F,,HF)) a).
      set (p := homotweqinvweq (catiso_ob_weq (F,,HF)) a).
      cbn in p.
      rewrite p.
      apply lt_iso_identity.
  Defined.

  Lemma isaprop_split_lt_essentially_surjective (D D' : preduploid)
    (ua' : is_duploid_univalent D')
    (F : D ⟶ D') (H : isweq (functor_on_objects F))
    : isaprop (split_lt_essentially_surjective F).
  Proof.
    apply impred; intro x.
    apply (isofhlevelweqb 1 (Y:=(paths_to x))).
    2: apply isapropifcontr, iscontr_paths_to.
    use weqbandf.
    - use (make_weq _ H).
    - intro y; cbn.
      apply invweq, (make_weq _ (ua' (F y) x)).
  Qed.

  Lemma isaprop_is_duploid_equivalence (D D' : preduploid)
    (ua : is_duploid_univalent D) (ua' : is_duploid_univalent D')
    (F : D ⟶ D')
    : isaprop (is_duploid_equivalence F).
  Proof.
    apply isaprop_assume_it_is; intro HF.
    apply isapropdirprod.
    - apply isaprop_fully_faithful.
    - assert (H : isweq (functor_on_objects F)).
      1: refine (isweq_on_objects_from_equivalence _ _ _ _ (F,,HF)); assumption.
      apply isaprop_split_lt_essentially_surjective; assumption.
  Qed.

  Lemma weq_duploid_equivalence_catiso (D D' : preduploid)
    (ua : is_duploid_univalent D) (ua' : is_duploid_univalent D')
    : duploid_equivalence D D' ≃ catiso D D'.
  Proof.
    use weqbandf.
    1: apply (idweq _).
    intro F.
    use weqimplimpl.
    - apply is_catiso_from_is_duploid_equivalence; assumption.
    - apply is_duploid_equivalence_from_is_catiso.
    - apply isaprop_is_duploid_equivalence; assumption.
    - apply isaprop_is_catiso.
  Defined.

  Lemma univalent_duploid_rxgraph : univalent_rxgraph.
  Proof.
    use make_univalent_rxgraph.
    1: use make_rxgraph'.
    - exact univalent_duploid.
    - intros a b; exact (duploid_equivalence a b).
    - intros a; exact (duploid_equivalence_identity a).
    - use (rxgraph_univalent_from_iso_b' univalent_duploid_rxgraph1).
      1: apply rxgraph_univalence.
      use make_pregraph_iso; cbn.
      + exact (idweq _).
      + intros a b.
        use (weq_duploid_equivalence_catiso a b);
          apply duploid_univalence.
  Defined.

  Hypothesis (D D' : univalent_duploid).

  (** Two univalent duploids are identical if their objects are *)
  Lemma duploid_eq_from_univalent : (D : precategory_data) = D' -> D = D'.
  Proof.
    intro H1.
    apply subtypePath'; [|apply isaprop_is_duploid_univalent].
    apply subtypePath'; [|apply isaprop_has_polarity_shifts, duploid_univalence].
    apply subtypePath'; [|apply isaprop_has_polarities].
    apply subtypePath'; [|apply isaprop_has_homsets].
    apply subtypePath'; [|apply isaprop_is_unital_premagmoid, unital_magmoid_has_homsets].
    apply H1.
  Defined.

  Lemma duploid_eq_weq_duploid_equivalence : duploid_equivalence D D' ≃ D = D'.
  Proof.
    exact (weq_edge_to_id univalent_duploid_rxgraph _ _).
  Defined.

End equivalences.

(** ** 4. Characterizations of univalence *)
Section characterizations.
  Definition duploid_to_rxgraph (D : preduploid) : rxgraph.
  Proof.
    use make_rxgraph'.
    - exact (ob D).
    - intros a b; exact (lt_iso a b).
    - intros a; exact (lt_iso_identity a).
  Defined.

  Remark duploid_rxgraph_univalent_eq (D : preduploid)
    : is_duploid_univalent D = is_rxgraph_univalent (duploid_to_rxgraph D).
  Proof. reflexivity. Defined.

  Definition iso_duploid_rxgraph_unital_magmoid_rxgraph (D : preduploid)
    : rxgraph_iso (unital_magmoid_to_rxgraph D) (duploid_to_rxgraph D).
  Proof.
    use make_rxgraph_iso; [use make_pregraph_iso|].
    - exact (idweq D).
    - apply weq_lti_iso_to_lt_iso_in_preduploid.
    - intro a; now apply lt_iso_eq.
  Defined.

  Corollary unital_magmoid_univalent_iff_duploid_univalent (D : preduploid)
    : is_unital_magmoid_univalent D ≃ is_duploid_univalent D.
  Proof.
    change (is_rxgraph_univalent (unital_magmoid_to_rxgraph D)
            ≃ is_rxgraph_univalent (duploid_to_rxgraph D)).
    apply weqimplimpl.
    - exact (λ H, rxgraph_univalent_from_iso_f _ H (iso_duploid_rxgraph_unital_magmoid_rxgraph D)).
    - exact (λ H, rxgraph_univalent_from_iso_b _ H (iso_duploid_rxgraph_unital_magmoid_rxgraph D)).
    - apply isaprop_is_rxgraph_univalent.
    - apply isaprop_is_rxgraph_univalent.
  Qed.

  Lemma weak_duploid_equivalence_to_split {D D' : preduploid}
    (ua : is_duploid_univalent D)
    (F : D ⟶ D') (H : is_weak_duploid_equivalence F)
    : split_lt_essentially_surjective F.
  Proof.
    intro b.
    refine (squash_to_prop (is_weak_duploid_equivalence_to_lt_essentially_surjective _ H b) _ (idfun _)).
    apply invproofirrelevance; intros Ha₁ Ha₂.
    induction Ha₁ as [a₁ Ha₁], Ha₂ as [a₂ Ha₂].
    assert (Ha : ∑ p, lt_iso_compose Ha₁ (lt_iso_inv Ha₂) = p); [eexists; reflexivity|].
    induction Ha as [Ha Ha_eq].
    apply (maponpaths (lt_iso_from_fully_faithful_functor_image _ H)) in Ha_eq.
    induction a₂, (lt_iso_from_fully_faithful_functor_image _ H Ha)
                    using (@rxgraph_edge_rect (duploid_to_rxgraph D) ua a₁).
    apply maponpaths.
    apply subtypePath'; [|apply isaprop_is_lt_iso].
    apply (cancel_lt_iso_right (lt_iso_inv Ha₂)).
    etrans; [|apply pathsinv0, lt_iso_is_inverse].
    apply base_paths in Ha_eq; cbn in Ha_eq.
    apply (maponpaths #F) in Ha_eq.
    refine (_ @ Ha_eq @ functor_id F _).
    apply pathsinv0.
    use homotweqinvweq.
  Qed.

  Lemma weak_duploid_equivalence_to_duploid_equivalence {D D' : preduploid}
    (ua : is_duploid_univalent D)
    (F : D ⟶ D') (H : is_weak_duploid_equivalence F)
    : is_duploid_equivalence F.
  Proof.
    use make_is_duploid_equivalence.
    - exact H.
    - now apply weak_duploid_equivalence_to_split.
  Qed.

  Context (D : preduploid).
  (** The following are equivalent:
      1. [D] is a univalent duploid
      2. [linear_and_thunkable_category D] is a univalent category
      3. [positive_thunkable_category D] and [negative_linear_category D] are both univalent categories *)

  (** 1 -> 2 *)
  Lemma duploid_to_linear_and_thunkable_category_rxgraph_iso
    : rxgraph_iso (category_to_rxgraph (D ₗₜ)) (duploid_to_rxgraph D).
  Proof.
    use make_rxgraph_iso; [use make_pregraph_iso|].
    - apply idweq.
    - intros a b; apply invweq, weq_z_iso_lt_iso.
    - intro a; cbn.
      apply subtypePath'; [|apply isaprop_is_lt_iso].
      reflexivity.
  Defined.

  Lemma is_duploid_univalent_to_is_univalent_linear_and_thunkable_category
    (H : is_duploid_univalent D) : is_univalent (linear_and_thunkable_category D).
  Proof.
    refine (rxgraph_univalent_from_iso_b _ _
              duploid_to_linear_and_thunkable_category_rxgraph_iso).
    exact H.
  Qed.

  (** 2 -> 1 *)
  Lemma is_duploid_univalent_from_is_univalent_linear_and_thunkable_category
    (H : is_univalent (D ₗₜ)) : is_duploid_univalent D.
  Proof.
    refine (rxgraph_univalent_from_iso_f _ _
              duploid_to_linear_and_thunkable_category_rxgraph_iso).
    exact H.
  Qed.

  (** 2 -> 3.a *)
  Lemma is_univalent_linear_and_thunkable_to_is_univalent_positive_thunkable_category
    (H : is_univalent (D ₗₜ)) : is_univalent (D ⁺ₜ).
  Proof.
    intros a b.
    use weqhomot.
    - induction a as [a Ha], b as [b Hb].
      intermediate_weq (a = b); [apply path_sigma_hprop, propproperty|].
      intermediate_weq (z_iso (C:=linear_and_thunkable_category D) a b);
        [exact (make_weq _ (H a b))|].
      apply invweq.
      apply (weq_ff_functor_on_z_iso
               (fully_faithful_positive_thunkable_category_to_linear_and_thunkable_category D)).
    - intro p.
      apply z_iso_eq.
      do 2 apply carrier_eq.
      now induction p.
  Qed.

  (** 2 -> 3.b *)
  Lemma is_univalent_linear_and_thunkable_to_is_univalent_negative_linear_category
    (H : is_univalent (D ₗₜ)) : is_univalent (D ⁻ₗ).
  Proof.
    intros a b.
    use weqhomot.
    - induction a as [a Ha], b as [b Hb].
      intermediate_weq (a = b); [apply path_sigma_hprop, propproperty|].
      intermediate_weq (z_iso (C:=linear_and_thunkable_category D) a b);
        [exact (make_weq _ (H a b))|].
      apply invweq.
      apply (weq_ff_functor_on_z_iso
               (fully_faithful_negative_linear_category_to_linear_and_thunkable_category D)).
    - intro p.
      apply z_iso_eq.
      do 2 apply carrier_eq.
      now induction p.
  Qed.

  (* 3 -> 2 *)
  Lemma is_univalent_linear_and_thunkable_from_positive_thunkable_and_negative_linear_categories
    (Hpositive : is_univalent (D⁺ₜ))
    (Hnegative : is_univalent (D⁻ₗ))
    : is_univalent (D ₗₜ).
  Proof.
    apply (is_rxgraph_univalent_from_isaprop_edges_from (category_to_rxgraph (D ₗₜ))).
    intro a.
    isaprop_goal Hprop; [apply isapropisaprop|].
    refine (squash_to_prop (polarity_of D a) Hprop (λ Ha, _)).
    induction Ha as [Ha | Ha].
    1: set (C := D⁻ₗ).                           2: set (C := D⁺ₜ).
    1: set (HC := Hnegative).                    2: set (HC := Hpositive).
    1: set (is_p := @is_negative D).             2: set (is_p := @is_positive D).
    all: set (a' := a,,Ha : C).
    all: use (isofhlevelweqb 1 (Y:=edges_from (a' : category_to_rxgraph C)));
      [|exact (is_rxgraph_univalent_to_isaprop_edges_from (category_to_rxgraph C) HC _)].
    all: eapply weqcomp; [|apply weqtotal2asstol].
    all: use weqbandf; [exact (idweq D)|]; intro b; cbn in b |- *.
    all: intermediate_weq (∑ _ : z_iso a b, is_p b).
    1,3:   apply invweq, weqpr1; intro e.
    1,2:   apply iscontraprop1.
    1:     apply isaprop_is_negative.            2: apply isaprop_is_positive.
    1:     refine (is_negative_of_lt_iso _ Ha).  2: refine (is_positive_of_lt_iso _ Ha).
    1,2:   apply weq_z_iso_lt_iso, e.
    all: eapply weqcomp; [apply weqdirprodcomm|].
    all: use weqbandf; [exact (idweq _)|]; intro Hb; cbn.
    all: apply invweq.
    1: apply (weq_ff_functor_on_z_iso (fully_faithful_negative_linear_category_to_linear_and_thunkable_category D)).
    1: apply (weq_ff_functor_on_z_iso (fully_faithful_positive_thunkable_category_to_linear_and_thunkable_category D)).
  Qed.

  (* 3 -> 1 *)
  Lemma is_duploid_univalent_from_positive_thunkable_and_negative_linear_categories
    (Hpositive : is_univalent (D⁺ₜ))
    (Hnegative : is_univalent (D⁻ₗ))
    : is_duploid_univalent D.
  Proof.
    apply is_duploid_univalent_from_is_univalent_linear_and_thunkable_category.
    apply is_univalent_linear_and_thunkable_from_positive_thunkable_and_negative_linear_categories.
    all: assumption.
  Qed.

End characterizations.

(** *** 5. Split duploids and univalence *)
Section split_duploids.
  (** Any univalent preduploid is a univalent split duploid with
      the polarity mapping from [LEM]. *)
  Lemma is_duploid_univalent_to_is_split_duploid_univalent_from_LEM (D : preduploid)
    (H : is_duploid_univalent D)
    (lem : LEM)
    : is_split_duploid_univalent (make_split_preduploid D (polarity_mapping_from_LEM D lem)).
  Proof.
    set (D':=make_split_preduploid D (polarity_mapping_from_LEM D lem)).
    apply is_duploid_univalent_to_is_univalent_linear_and_thunkable_category in H.
    split; rewrite category_rxgraph_univalent_eq;
      apply is_rxgraph_univalent_from_isaprop_edges_from; intros [a Ha].
    - pose (H' := is_univalent_linear_and_thunkable_to_is_univalent_positive_thunkable_category D H).
      rewrite category_rxgraph_univalent_eq in H'.
      change (positive_ob D) in a; cbn in Ha.
      refine (isofhlevelweqf 1 _ (is_rxgraph_univalent_to_isaprop_edges_from _ H' a)).
      intermediate_weq (∑ (b : ∑ (b : D⁺ₜ), z_iso (C:=D⁺ₜ) a b),
                         polarity_mapping_from_LEM D lem (pr11 b) = ⊕). {
        apply invweq, total2_contr.
        intros [b Hb]; cbn in Hb |- *.
        apply (invweq (weq_z_iso_lt_iso_positive a b)) in Hb.
        apply iscontraprop1; [apply isasetbool|].
        apply polarity_mapping_from_LEM_iff_not_negative.
        apply polarity_mapping_from_LEM_iff_not_negative in Ha.
        intro Hnegative; apply Ha.
        exact (is_negative_of_lt_iso (lt_iso_inv Hb) Hnegative).
      }
      intermediate_weq (∑ (b : D'⁺ᶜₜ), z_iso (C:=D⁺ₜ) a (pr1 b)). {
        use weq_iso.
        - intros [[b i] Hb]; exact ((b,, Hb),, i).
        - intros [[b Hb] i]; exact ((b,, i),, Hb).
        - easy.
        - easy.
      }
      apply weqfibtototal; intro b.
      apply invweq.
      use weqbandf; [apply weqtotalsubtype|]; intro f.
      use weqbandf; [apply weqtotalsubtype|]; intro g.
      use weqdirprodf; apply subtypeInjectivity; intro; apply propproperty.
    - pose (H' := is_univalent_linear_and_thunkable_to_is_univalent_negative_linear_category D H).
      rewrite category_rxgraph_univalent_eq in H'.
      change (negative_ob D) in a; cbn in Ha.
      refine (isofhlevelweqf 1 _ (is_rxgraph_univalent_to_isaprop_edges_from _ H' a)).
      intermediate_weq (∑ (b : ∑ (b : D⁻ₗ), z_iso (C:=D⁻ₗ) a b),
                         polarity_mapping_from_LEM D lem (pr11 b) = ⊖). {
        apply invweq, total2_contr.
        intros [b Hb]; cbn in Hb |- *.
        apply (invweq (weq_z_iso_lt_iso_negative a b)) in Hb.
        apply iscontraprop1; [apply isasetbool|].
        apply polarity_mapping_from_LEM_iff_negative.
        apply polarity_mapping_from_LEM_iff_negative in Ha.
        exact (is_negative_of_lt_iso Hb Ha).
      }
      intermediate_weq (∑ (b : D'⁻ᶜₗ), z_iso (C:=D⁻ₗ) a (pr1 b)). {
        use weq_iso.
        - intros [[b i] Hb]; exact ((b,, Hb),, i).
        - intros [[b Hb] i]; exact ((b,, i),, Hb).
        - easy.
        - easy.
      }
      apply weqfibtototal; intro b.
      apply invweq.
      use weqbandf; [apply weqtotalsubtype|]; intro f.
      use weqbandf; [apply weqtotalsubtype|]; intro g.
      use weqdirprodf; apply subtypeInjectivity; intro; apply propproperty.
  Qed.

  Lemma neg_is_duploid_univalent_if_split (D : split_duploid)
    (a : D) (Hpositive : is_positive a) (Hnegative : is_negative a)
    : ¬is_duploid_univalent D.
  Proof.
    intro ua.
    enough (Heq : (⇑a : D) = ⇓a). {
      apply (maponpaths (@chosen_polarity_of D)) in Heq.
      apply nopathsfalsetotrue.
      refine (_ @ Heq @ _).
      - apply pathsinv0, chosen_polarity_of_upshift.
      - apply chosen_polarity_of_downshift.
    }
    use (lt_iso_to_id ua).
    apply (lt_iso_compose (b:=a)).
    - apply (lt_iso_upshift_of_negative a Hnegative).
    - apply (lt_iso_downshift_of_positive a Hpositive).
  Qed.

End split_duploids.

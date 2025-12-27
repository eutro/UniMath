(** * Duploids *)
(** ** Contents
- Definitions of [semi,pre]duploids
- Lemmas about duploids
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.

(** * Duploids *)
Section duploids.

Declare Scope duploid.
Delimit Scope duploid with duploid.
Local Open Scope duploid.

Definition is_quasiduploid (C : precategory_data) : UU
  := ((∏ (a b : C) (f : a --> b), identity a · f = f)
      ×
      (∏ (a b : C) (f : a --> b), f · identity b = f)).

Lemma isaprop_is_quasiduploid (C : precategory_data)
  : has_homsets C -> isaprop (is_quasiduploid C).
Proof.
  intro H.
  apply isapropdirprod.
  - do 3 (apply impred; intro). apply H.
  - do 3 (apply impred; intro). apply H.
Qed.

Definition make_is_quasiduploid {C : precategory_data}
  (H1 : ∏ (a b : C) (f : a --> b), identity a · f = f)
  (H2 : ∏ (a b : C) (f : a --> b), f · identity b = f)
  : is_quasiduploid C
  := H1,,H2.

Definition quasiduploid : UU
  := ∑ C : precategory_data, has_homsets C × is_quasiduploid C.

Definition make_quasiduploid (C : precategory_data)
  (H1 : has_homsets C)
  (H2 : is_quasiduploid C) : quasiduploid
  := C,,(H1,,H2).

Definition precategory_data_from_quasiduploid (C : quasiduploid) : precategory_data := pr1 C.
Coercion precategory_data_from_quasiduploid : quasiduploid >-> precategory_data.

Definition duploid_id_left (C : quasiduploid) :
   ∏ (a b : C) (f : a --> b),
    identity a · f = f := pr122 C.

Definition duploid_id_right (C : quasiduploid) :
   ∏ (a b : C) (f : a --> b),
    f · identity b = f := pr222 C.

Arguments duploid_id_left [C a b] f.
Arguments duploid_id_right [C a b] f.

Coercion duploid_homsets (C : quasiduploid) : has_homsets C := pr12 C.

Definition is_linear {C : precategory_data} {a b : C} (f : a --> b) : UU
  := ∏ (c d : C) (g : c --> a) (h : d --> c),
    (h · g) · f = h · (g · f).
Definition is_thunkable {C : precategory_data} {a b : C} (f : b --> a) : UU
  := ∏ (c d : C) (g : a --> c) (h : c --> d),
    f · (g · h) = (f · g) · h.

Lemma assoc_linear {C : precategory_data} {a b c d : C}
  (f : a --> b) (H : is_linear f) (g : c --> a) (h : d --> c)
  : h · (g · f) = (h · g) · f.
Proof. apply (!H _ _ _ _). Defined.
Lemma assoc'_linear {C : precategory_data} {a b c d : C}
  (f : a --> b) (H : is_linear f) (g : c --> a) (h : d --> c)
  : (h · g) · f = h · (g · f).
Proof. apply (H _ _ _ _). Defined.

Lemma assoc_thunkable {C : precategory_data} {a b c d : C}
  (f : b --> a) (H : is_thunkable f) (g : a --> c) (h : c --> d)
  : f · (g · h) = (f · g) · h.
Proof. apply H. Defined.
Lemma assoc'_thunkable {C : precategory_data} {a b c d : C}
  (f : b --> a) (H : is_thunkable f) (g : a --> c) (h : c --> d)
  : (f · g) · h = f · (g · h).
Proof. apply (!H _ _ _ _). Defined.

Lemma isaprop_is_linear' {C : precategory_data} {a b : C} (f : a --> b)
  : has_homsets C -> isaprop (is_linear f).
Proof. intro H. do 4 (apply impred; intro). apply H. Qed.
Lemma isaprop_is_thunkable' {C : precategory_data} {a b : C} (f : a --> b)
  : has_homsets C -> isaprop (is_thunkable f).
Proof. intro H. do 4 (apply impred; intro). apply H. Qed.

Lemma isaprop_is_linear {C : quasiduploid} {a b : C} (f : a --> b) : isaprop (is_linear f).
Proof. apply isaprop_is_linear', C. Qed.
Lemma isaprop_is_thunkable {C : quasiduploid} {a b : C} (f : a --> b) : isaprop (is_thunkable f).
Proof. apply isaprop_is_thunkable', C. Qed.

Lemma is_thunkable_identity {C : quasiduploid} (a : C) : is_thunkable (identity a).
Proof. intros b c g h. do 2 rewrite duploid_id_left. apply idpath. Qed.
Lemma is_linear_identity {C : quasiduploid} (a : C) : is_linear (identity a).
Proof. intros b c g h. do 2 rewrite duploid_id_right. apply idpath. Qed.

Lemma is_thunkable_compose {C : precategory_data} {a b c : C} (f : a --> b) (g : b --> c)
  : is_thunkable f -> is_thunkable g -> is_thunkable (f · g).
Proof. intros Hf Hg d e h k. now rewrite <- Hf, <- Hf, Hg, Hf. Qed.
Lemma is_linear_compose {C : precategory_data} {a b c : C} (f : a --> b) (g : b --> c)
  : is_linear f -> is_linear g -> is_linear (f · g).
Proof. intros Hf Hg d e h k. now rewrite <- Hg, <- Hg, Hf, Hg. Qed.

Lemma linear_inverse_unique {C : quasiduploid} {a b : C}
  (f : a --> b) (g g' : b --> a)
  (H1 : is_inverse_in_precat f g)
  (H1' : is_inverse_in_precat f g')
  (H2 : is_linear g) : g = g'.
Proof.
  destruct H1 as [eta eps].
  destruct H1' as [eta' eps'].
  intermediate_path (identity b · g).
    now rewrite duploid_id_left.
  now rewrite <- eps', H2, eta, duploid_id_right.
Qed.

Lemma thunkable_inverse_unique {C : quasiduploid} {a b : C}
  (f : a --> b) (g g' : b --> a)
  (H1 : is_inverse_in_precat f g)
  (H1' : is_inverse_in_precat f g')
  (H2 : is_thunkable g) : g = g'.
Proof.
  destruct H1 as [eta eps].
  destruct H1' as [eta' eps'].
  intermediate_path (g · identity a).
    now rewrite duploid_id_right.
  now rewrite <- eta', H2, eps, duploid_id_left.
Qed.

Lemma is_thunkable_precategory (C : precategory) (a b : C) (f : a --> b) : is_thunkable f.
Proof. intros c d g h. apply assoc. Defined.
Lemma is_linear_precategory (C : precategory) (a b : C) (f : a --> b) : is_linear f.
Proof. intros c d g h. apply assoc'. Defined.

Definition is_positive {C : precategory_data} (a : C) : UU
  := ∏ (b : C) (f : a --> b), is_linear f.
Definition is_negative {C : precategory_data} (a : C) : UU
  := ∏ (b : C) (f : a <-- b), is_thunkable f.

Lemma isaprop_is_positive' {C : precategory_data} (a : C)
  : has_homsets C -> isaprop (is_positive a).
Proof. intros H. do 2 (apply impred; intro). apply isaprop_is_linear', H. Qed.
Lemma isaprop_is_negative' {C : precategory_data} (a : C)
  : has_homsets C -> isaprop (is_negative a).
Proof. intros H. do 2 (apply impred; intro). apply isaprop_is_thunkable', H. Qed.

Lemma isaprop_is_positive {C : quasiduploid} (a : C) : isaprop (is_positive a).
Proof. apply isaprop_is_positive', C. Qed.
Lemma isaprop_is_negative {C : quasiduploid} (a : C) : isaprop (is_negative a).
Proof. apply isaprop_is_negative', C. Qed.

Definition positive_objects (C : quasiduploid) : hsubtype C
  := (λ a : C, make_hProp (is_positive a) (isaprop_is_positive a)).
Definition negative_objects (C : quasiduploid) : hsubtype C
  := (λ a : C, make_hProp (is_negative a) (isaprop_is_negative a)).
Definition thunkable_mors (C : quasiduploid) (a b : C) : hsubtype (a --> b)
  := (λ f : a --> b, make_hProp (is_thunkable f) (isaprop_is_thunkable f)).
Definition linear_mors (C : quasiduploid) (a b : C) : hsubtype (a --> b)
  := (λ f : a --> b, make_hProp (is_linear f) (isaprop_is_linear f)).

Definition positive_object (C : quasiduploid) : UU := carrier (positive_objects C).
Identity Coercion Id_positive_object : positive_object >-> carrier.
Coercion object_of_positive_object {C : quasiduploid} (a : positive_object C) : C := pr1 a.
Coercion is_positive_of_positive_object {C : quasiduploid} (a : positive_object C) : is_positive a := pr2 a.
Definition negative_object (C : quasiduploid) : UU := carrier (negative_objects C).
Identity Coercion Id_negative_object : negative_object >-> carrier.
Coercion object_of_negative_object {C : quasiduploid} (a : negative_object C) : C := pr1 a.
Coercion is_negative_of_negative_object {C : quasiduploid} (a : negative_object C) : is_negative a := pr2 a.

Definition is_linear_of_positive {C : precategory_data} {a b : C} (f : a --> b)
  : is_positive a -> is_linear f := λ H, H _ f.
Definition is_linear_of_positive' {C : quasiduploid} {a : positive_object C} {b : C} (f : pr1 a --> b)
  : is_linear f := is_linear_of_positive f a.
Definition is_thunkable_of_negative {C : precategory_data} {a b : C} (f : a --> b)
  : is_negative b -> is_thunkable f := λ H, H _ f.
Definition is_thunkable_of_negative' {C : quasiduploid} {a : C} {b : negative_object C} (f : a --> pr1 b)
  : is_thunkable f := is_thunkable_of_negative f b.

Lemma assoc_positive {C : precategory_data} {a b d : C}
  (c : C) (H : is_positive c) (f : a --> b) (g : b --> c) (h : c --> d)
  : f · (g · h) = (f · g) · h.
Proof. apply assoc_linear, is_linear_of_positive, H. Defined.
Lemma assoc'_positive {C : precategory_data} {a b d : C}
  (c : C) (H : is_positive c) (f : a --> b) (g : b --> c) (h : c --> d)
  : (f · g) · h = f · (g · h).
Proof. apply assoc'_linear, is_linear_of_positive, H. Defined.

Lemma assoc_negative {C : precategory_data} {a c d : C}
  (b : C) (H : is_negative b) (f : a --> b) (g : b --> c) (h : c --> d)
  : f · (g · h) = (f · g) · h.
Proof. apply assoc_thunkable, is_thunkable_of_negative, H. Defined.
Lemma assoc'_negative {C : precategory_data} {a c d : C}
  (b : C) (H : is_negative b) (f : a --> b) (g : b --> c) (h : c --> d)
  : (f · g) · h = f · (g · h).
Proof. apply assoc'_thunkable, is_thunkable_of_negative, H. Defined.

Definition duploid_compose {C : quasiduploid} {a b c : C}
  (f : a --> b) (g : b --> c) : a --> c := f · g.
Definition positive_compose {C : quasiduploid} {a : C} {b : positive_object C} {c : C}
  (f : a --> b) (g : b --> c) : a --> c := f · g.
Definition negative_compose {C : quasiduploid} {a : C} {b : negative_object C} {c : C}
  (f : a --> b) (g : b --> c) : a --> c := f · g.

Notation "f ⊙ g" := (duploid_compose f g) (at level 40, no associativity) : duploid.
Notation "f ⊛ g" := (positive_compose f g) (at level 40, no associativity) : duploid.
Notation "f ⊖ g" := (negative_compose f g) (at level 40, no associativity) : duploid.

Lemma duploid_compose_of {C : quasiduploid} {a b c : C}
  (f : a --> b) (g : b --> c) : f · g = f ⊙ g.
Proof. apply idpath. Defined.
Lemma positive_compose_of {C : quasiduploid} {a b c : C}
  (H : is_positive b) (f : a --> b) (g : b --> c)
  : f ⊙ g = positive_compose (b:=b,,H) f g.
Proof. apply idpath. Defined.
Lemma negative_compose_of {C : quasiduploid} {a b c : C}
  (H : is_negative b) (f : a --> b) (g : b --> c)
  : f ⊙ g = negative_compose (b:=b,,H) f g.
Proof. apply idpath. Defined.

Ltac duploid_compose := repeat rewrite duploid_compose_of.
Ltac duploid_compose_positive H := repeat rewrite (positive_compose_of H).
Ltac duploid_compose_negative H := repeat rewrite (negative_compose_of H).

(** ** The category of all objects and thunkable maps. *)
Definition thunkable_category (C : quasiduploid) : category.
Proof.
  use makecategory.
  - exact C.
  - intros a b. exact (thunkable_mors C a b).
  - intros a b. apply isofhlevel_hsubtype, C.
  - intros a. apply (make_carrier _ (identity a)), is_thunkable_identity.
  - intros a b c f g. apply (make_carrier _ (pr1 f · pr1 g)), is_thunkable_compose.
    apply f. apply g.
  - intros a b f. apply carrier_eq, duploid_id_left.
  - intros a b f. apply carrier_eq, duploid_id_right.
  - intros a b c d f g h. apply carrier_eq, (pr2 f _).
  - intros a b c d f g h. apply carrier_eq, (!pr2 f _ _ _ _).
Defined.

(** ** The category of all objects and linear maps. *)
Definition linear_category (C : quasiduploid) : category.
Proof.
  use makecategory.
  - exact C.
  - intros a b. exact (linear_mors C a b).
  - intros a b. apply isofhlevel_hsubtype, duploid_homsets.
  - intros a. apply (make_carrier _ (identity a)), is_linear_identity.
  - intros a b c f g. apply (make_carrier _ (pr1 f · pr1 g)), is_linear_compose.
    apply f. apply g.
  - intros a b f. apply carrier_eq, duploid_id_left.
  - intros a b f. apply carrier_eq, duploid_id_right.
  - intros a b c d f g h. apply carrier_eq, (!pr2 h _ _ _ _).
  - intros a b c d f g h. apply carrier_eq, (pr2 h _).
Defined.

(** ** The category of positive objects and linear maps. *)
Definition positive_category (C : quasiduploid) : category
  := full_sub_category (linear_category C) (λ a, positive_objects C a).
(** ** The category of negative objects and thunkable maps. *)
Definition negative_category (C : quasiduploid) : category
  := full_sub_category (thunkable_category C) (λ a, negative_objects C a).
(** ** The category of positive objects and thunkable maps. *)
Definition positive_thunkable_category (C : quasiduploid) : category
  := full_sub_category (thunkable_category C) (λ a, positive_objects C a).
(** ** The category of negative objects and linear maps. *)
Definition negative_linear_category (C : quasiduploid) : category
  := full_sub_category (linear_category C) (λ a, negative_objects C a).

(* Morphisms between positive objects are always linear. *)
Definition embed_positive_mor (C : quasiduploid)
  (a b : positive_objects C) (f : C⟦pr1 a, pr1 b⟧) : positive_category C⟦a, b⟧
  := (f,,is_linear_of_positive' f),,tt.
Lemma weq_embed_positive_mor (C : quasiduploid)
  (a b : positive_objects C) : isweq (embed_positive_mor C a b).
Proof.
  apply (isweq_iso _ (λ f, pr11 f)).
  - exact idpath.
  - intro f. now do 2 apply carrier_eq.
Defined.

(* Morphisms between negative objects are always thunkable. *)
Definition embed_negative_mor (C : quasiduploid)
  (a b : negative_objects C) (f : C⟦pr1 a, pr1 b⟧) : negative_category C⟦a, b⟧
  := (f,,is_thunkable_of_negative' f),,tt.
Lemma weq_embed_negative_mor (C : quasiduploid)
  (a b : negative_objects C) : isweq (embed_negative_mor C a b).
Proof.
  apply (isweq_iso _ (λ f, pr11 f)).
  - exact idpath.
  - intro f. now do 2 apply carrier_eq.
Defined.

Definition is_polarized (C : quasiduploid) : UU
  := ∏ a : C, ∥ is_positive a ⨿ is_negative a ∥.

Lemma isaprop_is_polarized (C : quasiduploid) : isaprop (is_polarized C).
Proof. apply impred; intro. apply isapropishinh. Qed.

Definition preduploid : UU := ∑ C : quasiduploid, is_polarized C.
Definition make_preduploid {C : quasiduploid}
  (H : is_polarized C) : preduploid := C,,H.

Definition quasiduploid_from_preduploid (C : preduploid) : quasiduploid := pr1 C.
Coercion quasiduploid_from_preduploid : preduploid >-> quasiduploid.

Definition preduploid_polarity {C : preduploid} (a : C)
  : ∥ is_positive a ⨿ is_negative a ∥
  := pr2 C a.

Definition duploid_force_data (C : quasiduploid) : UU :=
  ∏ (a : C), ∑ upa : C, upa --> a.
Definition duploid_wrap_data (C : quasiduploid) : UU :=
  ∏ (a : C), ∑ downa : C, a --> downa.

Definition make_duploid_force_data {C : quasiduploid}
  (upshift : C -> C) (force : ∏ (a : C), upshift a --> a)
  : duploid_force_data C :=
  λ a, upshift a,,force a.
Definition make_duploid_wrap_data {C : quasiduploid}
  (downshift : C -> C) (wrap : ∏ (a : C), a --> downshift a)
  : duploid_wrap_data C :=
  λ a, downshift a,,wrap a.

Definition upshift' {C : quasiduploid} (D : duploid_force_data C) (a : C) : C := pr1 (D a).
Definition downshift' {C : quasiduploid} (D : duploid_wrap_data C) (a : C) : C := pr1 (D a).
Definition force' {C : quasiduploid} (D : duploid_force_data C) (a : C)
  : upshift' D a --> a := pr2 (D a).
Definition wrap' {C : quasiduploid} (D : duploid_wrap_data C) (a : C)
  : a --> downshift' D a := pr2 (D a).

Definition duploid_force_axioms {C : quasiduploid} (D : duploid_force_data C) : UU
  := ∏ (a : C), is_linear (force' D a) ×
    ∑ (delay : a --> upshift' D a),
    is_inverse_in_precat (force' D a) delay ×
      is_negative (upshift' D a).

Definition make_duploid_force_axioms {C : quasiduploid} {D : duploid_force_data C}
  (H1 : ∏ a : C, is_negative (upshift' D a))
  (H2 : ∏ a : C, is_linear (force' D a))
  (delay : ∏ a : C, a --> upshift' D a)
  (H3 : ∏ a : C, is_inverse_in_precat (force' D a) (delay a))
  : duploid_force_axioms D
  := λ a, H2 a ,, delay a ,, H3 a ,, H1 a.

Lemma isaprop_duploid_force_axioms {C : quasiduploid} (D : duploid_force_data C)
  : isaprop (duploid_force_axioms D).
Proof.
  apply impred; intro a.
  apply isofhleveldirprod.
  - apply isaprop_is_linear.
  - apply invproofirrelevance.
    intros thunk1 thunk2.
    induction thunk1 as [thunk1 H1].
    induction thunk2 as [thunk2 H2].
    assert (H : thunk1 = thunk2). {
      apply (thunkable_inverse_unique (force' D a) _ _ (pr1 H1) (pr1 H2)).
      apply is_thunkable_of_negative, (pr2 H1).
    }
    induction H.
    apply maponpaths, proofirrelevance, isofhleveldirprod.
    + apply isofhleveldirprod, C. apply C.
    + apply isaprop_is_negative.
Qed.

Definition duploid_wrap_axioms {C : quasiduploid} (D : duploid_wrap_data C) : UU
  := ∏ (a : C), is_thunkable (wrap' D a)×
    ∑ (unwrap : downshift' D a --> a),
    is_inverse_in_precat (wrap' D a) unwrap ×
      is_positive (downshift' D a).

Definition make_duploid_wrap_axioms {C : quasiduploid} {D : duploid_wrap_data C}
  (H1 : ∏ a : C, is_positive (downshift' D a))
  (H2 : ∏ a : C, is_thunkable (wrap' D a))
  (wrap : ∏ a : C, downshift' D a --> a)
  (H3 : ∏ a : C, is_inverse_in_precat (wrap' D a) (wrap a))
  : duploid_wrap_axioms D
  := λ a, H2 a ,, wrap a ,, H3 a ,, H1 a.

Lemma isaprop_duploid_wrap_axioms {C : quasiduploid} (D : duploid_wrap_data C)
  : isaprop (duploid_wrap_axioms D).
Proof.
  apply impred; intro a.
  apply isofhleveldirprod.
  - apply isaprop_is_thunkable.
  - apply invproofirrelevance.
    intros thunk1 thunk2.
    induction thunk1 as [thunk1 H1].
    induction thunk2 as [thunk2 H2].
    assert (H : thunk1 = thunk2). {
      apply (linear_inverse_unique (wrap' D a) _ _ (pr1 H1) (pr1 H2)).
      apply is_linear_of_positive, (pr2 H1).
    }
    induction H.
    apply maponpaths, proofirrelevance, isofhleveldirprod.
    + apply isofhleveldirprod, C. apply C.
    + apply isaprop_is_positive.
Qed.

Definition duploid_data (C : quasiduploid) : UU
  := duploid_force_data C × duploid_wrap_data C.
Coercion duploid_data_force {C : quasiduploid} (D : duploid_data C) : duploid_force_data C := pr1 D.
Coercion duploid_data_wrap {C : quasiduploid} (D : duploid_data C) : duploid_wrap_data C := pr2 D.

Definition make_duploid_data {C : quasiduploid}
  (F : duploid_force_data C)
  (W : duploid_wrap_data C)
  : duploid_data C
  := F,,W.

Definition duploid_axioms {C : quasiduploid} (D : duploid_data C) : UU
  := duploid_force_axioms D × duploid_wrap_axioms D.

Definition make_duploid_axioms {C : quasiduploid} {D : duploid_data C}
  (F : duploid_force_axioms D)
  (W : duploid_wrap_axioms D)
  : duploid_axioms D
  := F,,W.

Definition isaprop_duploid_axioms {C : quasiduploid} (D : duploid_data C)
  : isaprop (duploid_axioms D).
Proof.
  apply isofhleveldirprod.
  apply isaprop_duploid_force_axioms.
  apply isaprop_duploid_wrap_axioms.
Qed.

Definition duploid : UU :=
  ∑ (C : preduploid),
    ∑ (D : duploid_data C),
    duploid_axioms D.
Coercion preduploid_of_duploid (C : duploid) : preduploid := pr1 C.
Coercion duploid_data_of_duploid (C : duploid) : duploid_data C := pr12 C.

Definition duploid_axioms_of_duploid (C : duploid) : duploid_axioms C := pr22 C.

Definition upshift {C : duploid} (a : C) : negative_object C.
Proof. exists (upshift' C a). exact (pr222 (pr1 (duploid_axioms_of_duploid C) a)). Defined.
Definition downshift {C : duploid} (a : C) : positive_object C.
Proof. exists (downshift' C a). exact (pr222 (pr2 (duploid_axioms_of_duploid C) a)). Defined.

Notation "'⇑' a" := (upshift a) (at level 40) : duploid.
Notation "'⇓' a" := (downshift a) (at level 40) : duploid.

Definition force {C : duploid} (a : C) : ⇑a --> a := force' C a.
Definition wrap {C : duploid} (a : C) : a --> ⇓a := wrap' C a.

Definition delay {C : duploid} (a : C) : a --> ⇑a
  := pr12 (pr1 (duploid_axioms_of_duploid C) a).
Definition unwrap {C : duploid} (a : C) : ⇓a --> a
  := pr12 (pr2 (duploid_axioms_of_duploid C) a).

Definition is_negative_upshift {C : duploid} (a : C) : is_negative (⇑a) := ⇑a.
Definition is_linear_force {C : duploid} (a : C) : is_linear (force a)
  := pr1 (pr1 (duploid_axioms_of_duploid C) a).
Definition is_inverse_force_thunk {C : duploid} (a : C) : is_inverse_in_precat (force a) (delay a)
  := pr122 (pr1 (duploid_axioms_of_duploid C) a).

Definition force_delay_id {C : duploid} (a : C) : force a · delay a = identity (⇑a)
  := pr1 (is_inverse_force_thunk a).
Definition delay_force_id {C : duploid} (a : C) : delay a · force a = identity a
  := pr2 (is_inverse_force_thunk a).

Definition is_positive_downshift {C : duploid} (a : C) : is_positive (⇓a)
  := pr222 (pr2 (duploid_axioms_of_duploid C) a).
Definition is_thunkable_wrap {C : duploid} (a : C) : is_thunkable (wrap a)
  := pr1 (pr2 (duploid_axioms_of_duploid C) a).
Definition is_inverse_wrap_unwrap {C : duploid} (a : C) : is_inverse_in_precat (wrap a) (unwrap a)
  := pr122 (pr2 (duploid_axioms_of_duploid C) a).

Definition wrap_unwrap_id {C : duploid} (a : C) : wrap a · unwrap a = identity a
  := pr1 (is_inverse_wrap_unwrap a).
Definition unwrap_wrap_id {C : duploid} (a : C) : unwrap a · wrap a = identity (⇓a)
  := pr2 (is_inverse_wrap_unwrap a).

Lemma is_linear_unwrap {C : duploid} (a : C) : is_linear (unwrap a).
Proof. apply is_linear_of_positive, is_positive_downshift. Qed.
Lemma is_thunkable_delay {C : duploid} (a : C) : is_thunkable (delay a).
Proof. apply is_thunkable_of_negative, is_negative_upshift. Qed.

Section lemmas.

Context {C : duploid}.

Lemma delay_force_right {a b : C} (f : a --> b) : (f · delay b) · force b = f.
Proof.
  rewrite (assoc'_linear _ (is_linear_force _)), delay_force_id.
  apply duploid_id_right.
Qed.

Lemma wrap_unwrap_left {a b : C} (f : a --> b) : wrap a · (unwrap a · f) = f.
Proof.
  rewrite (assoc_thunkable _ (is_thunkable_wrap _)), wrap_unwrap_id.
  apply duploid_id_left.
Qed.

Ltac decide_polarity a H :=
  use (factor_through_squash _ _ (preduploid_polarity a)); [ idtac | intro H ].

Lemma is_thunkable_of_delay_wrap {a b : C} (f : a --> b)
  : f · (delay b · wrap (⇑b)) = (f · delay b) · wrap (⇑b) ->
    is_thunkable f.
Proof.
  duploid_compose.
  duploid_compose_negative (is_negative_upshift b).
  intros Hf.
  decide_polarity b Hb. apply isaprop_is_thunkable.
  induction Hb as [Hb | Hb].
  2: apply is_thunkable_of_negative, Hb.
  assert (H' : ∏ (d : C) (h : ⇑b --> d), f ⊙ (delay b ⊙ h) = (f ⊙ delay b) ⊙ h). {
    intros d h.
    duploid_compose_positive Hb.
    intermediate_path ((f · (delay b · wrap (⇑b))) · (unwrap (⇑b) · h)). {
      admit.
    }
    rewrite Hf.
    rewrite (assoc'_negative _ (is_negative_upshift _)).
    now rewrite wrap_unwrap_left.
  }
  intros c d g h.
  decide_polarity c Hc. apply duploid_homsets.
  induction Hc as [Hc | Hc].
  1: apply assoc_positive, Hc.
  intermediate_path (f · (delay b · (force b · g) · h)). {
    rewrite (assoc_thunkable (delay b) (is_thunkable_delay _)).
    now rewrite delay_force_id, duploid_id_left.
  }
  rewrite (assoc'_negative (⇑b) (is_negative_upshift _)).
  rewrite H'.
  rewrite (assoc_negative (⇑b) (is_negative_upshift _)).
  rewrite <- H'.
  rewrite (assoc_negative (⇑b) (is_negative_upshift _)).
  now rewrite delay_force_id, duploid_id_left.
Admitted.

Lemma is_linear_of_force_unwrap {a b : C} (f : b --> a)
  : (force (⇓b) · unwrap b) · f = force (⇓b) · (unwrap b) · f ->
    is_linear f.
Proof. admit. Admitted.

End lemmas.

Section adjunction.

Context {C₁ C₂ : category} (θ : adjunction C₂ C₁).
Let F : functor C₂ C₁ := left_functor θ.
Let G : functor C₁ C₂ := right_functor θ.
Let H : are_adjoints F G := θ.
Let η : nat_trans (functor_identity C₂) (F ∙ G) := adjunit H.
Let ε : nat_trans (G ∙ F) (functor_identity C₁) := adjcounit H.

Let obs := C₁ ⨿ C₂.

Definition duploid_of_adjunction_neg (a : obs) : C₁.
Proof. induction a as [n | p]. exact n. exact (F p). Defined.
Definition duploid_of_adjunction_pos (a : obs) : C₂.
Proof. induction a as [n | p]. exact (G n). exact p. Defined.

Notation "a '⁻'" := (duploid_of_adjunction_neg a) : duploid.
Notation "a '⁺'" := (duploid_of_adjunction_pos a) : duploid.

Let mor (a b : obs) := C₁⟦F (a⁺), b⁻⟧.

Let ob_mor : precategory_ob_mor
  := make_precategory_ob_mor obs mor.

Let identity_oblique (a : ob_mor)
  : a --> a.
Proof.
  induction a.
  + apply (φ_adj_inv H), identity.
  + apply identity.
Defined.

Let compose_oblique (a b c : ob_mor)
  (f : a --> b) (g : b --> c)
  : a --> c.
Proof.
  induction b.
  + exact (φ_adj_inv H (φ_adj H f · φ_adj H g)).
  + exact (f · g).
Defined.

Let precat_data : precategory_data
    := make_precategory_data ob_mor identity_oblique compose_oblique.

Let is_quasi : is_quasiduploid precat_data.
Proof.
  use make_is_quasiduploid; simpl.
  - intros a b f.
    unfold compose, identity.
    induction a; simpl.
    + rewrite φ_adj_after_φ_adj_inv, id_left.
      apply φ_adj_inv_after_φ_adj.
    + apply id_left.
  - intros a b f.
    unfold compose, identity.
    induction b; simpl.
    + rewrite φ_adj_after_φ_adj_inv, id_right.
      apply φ_adj_inv_after_φ_adj.
    + apply id_right.
Qed.

Let quasi : quasiduploid.
Proof.
  use (make_quasiduploid precat_data).
  - intros a b; simpl. apply C₁.
  - apply is_quasi.
Defined.

Lemma is_negative_of_adj_left (a : C₁) : is_negative (C:=quasi) (inl a).
Proof.
  intros b f c d g h.
  induction c as [m | q]; unfold compose; simpl.
  + do 2 rewrite φ_adj_after_φ_adj_inv.
    now rewrite assoc.
  + rewrite φ_adj_natural_postcomp, assoc.
    now rewrite φ_adj_inv_natural_postcomp.
Qed.

Lemma is_positive_of_adj_right (a : C₂) : is_positive (C:=quasi) (inr a).
Proof.
  intros b f c d g h.
  induction c as [m | q]; unfold compose; simpl.
  + rewrite φ_adj_natural_postcomp, assoc.
    now rewrite φ_adj_inv_natural_postcomp.
  + apply assoc'.
Qed.

Let polarized : is_polarized quasi.
Proof.
  intro a.
  apply hinhpr.
  induction a as [n | p].
  - right; apply is_negative_of_adj_left.
  - left; apply is_positive_of_adj_right.
Qed.

Definition preduploid_of_adjunction : preduploid
  := make_preduploid polarized.

Definition duploid_data_of_adjunction : duploid_data preduploid_of_adjunction.
Proof.
  apply make_duploid_data.
  - use make_duploid_force_data;
      intro a; induction a as [n | p].
    + exact (inl n).
    + exact (inl (F p)).
    + apply identity.
    + apply (φ_adj_inv H), identity.
  - use make_duploid_wrap_data;
      intro a; induction a as [n | p].
    + exact (inr (G n)).
    + exact (inr p).
    + simpl. apply identity.
    + apply identity.
Defined.

Definition duploid_axioms_of_adjunction : duploid_axioms duploid_data_of_adjunction.
Proof.
  apply make_duploid_axioms.
  - use make_duploid_force_axioms; intro a; induction a as [n | p].
    + apply is_negative_of_adj_left.
    + apply is_negative_of_adj_left.
    + apply (is_linear_identity (C:=quasi) (inl n)).
    + unfold force', upshift'; simpl.
      intros b c f g.
      induction b as [m | q].
      1: now rewrite (assoc'_negative _ (is_negative_of_adj_left _)).
      unfold compose; simpl.
      rewrite φ_adj_after_φ_adj_inv.
      now do 2 rewrite id_right, φ_adj_inv_after_φ_adj.
    + apply identity.
    + apply (identity (F p)).
    + unfold force', upshift'; simpl; split; unfold identity, compose; simpl;
        now rewrite φ_adj_after_φ_adj_inv, id_left.
    + unfold force', upshift'; simpl; split; unfold identity, compose; simpl.
      * now rewrite id_right.
      * now rewrite φ_adj_after_φ_adj_inv, id_right,
          φ_adj_inv_after_φ_adj.
  - use make_duploid_wrap_axioms; intro a; induction a as [n | p].
    + apply is_positive_of_adj_right.
    + apply is_positive_of_adj_right.
    + unfold wrap', downshift'; simpl.
      intros b c f g.
      induction b as [m | q].
      2: now rewrite (assoc'_positive _ (is_positive_of_adj_right _)).
      unfold compose; simpl.
      now do 2 rewrite id_left.
    + apply (is_thunkable_identity (C:=quasi) (inr p)).
    + apply (φ_adj_inv H), identity.
    + apply (identity (F p)).
    + unfold wrap', downshift'; simpl; split; unfold identity, compose; simpl.
      * now rewrite id_left.
      * now rewrite φ_adj_after_φ_adj_inv, id_left,
          φ_adj_inv_after_φ_adj.
    + unfold wrap', downshift'; simpl; split; unfold identity, compose; simpl;
        now rewrite id_left.
Qed.

End adjunction.

End duploids.

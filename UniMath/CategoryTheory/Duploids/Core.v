(** * Duploids *)
(** ** Contents
- Definitions of [quasi,pre]duploids
- Lemmas about duploids
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.Profunctors.Transformation.

Local Open Scope cat.

Declare Scope duploid.
Delimit Scope duploid with duploid.
Local Open Scope duploid.

(** * Duploids *)
Section duploids.

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

Definition thunkable_mor {C : quasiduploid} (a b : C) : UU := carrier (thunkable_mors C a b).
Identity Coercion Id_thunkable_mor : thunkable_mor >-> carrier.
Coercion mor_of_thunkable_mor {C : quasiduploid} (a b : C) (f : thunkable_mor a b) : a --> b := pr1 f.
Coercion is_thunkable_of_thunkable_mor {C : quasiduploid} (a b : C) (f : thunkable_mor a b) : is_thunkable f := pr2 f.
Definition linear_mor {C : quasiduploid} (a b : C) : UU := carrier (linear_mors C a b).
Identity Coercion Id_linear_mor : linear_mor >-> carrier.
Coercion mor_of_linear_mor {C : quasiduploid} (a b : C) (f : linear_mor a b) : a --> b := pr1 f.
Coercion is_linear_of_linear_mor {C : quasiduploid} (a b : C) (f : linear_mor a b) : is_linear f := pr2 f.

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

Notation "f ⊙ g" :=
  (compose (C:=precategory_data_from_quasiduploid _) f g)
    (at level 40, no associativity) : duploid.
Notation "f ⊛ g" :=
  (compose (b:=object_of_positive_object _) f g)
    (at level 40, no associativity) : duploid.
Notation "f ⊖ g" :=
  (compose (b:=object_of_negative_object _) f g)
    (at level 40, no associativity) : duploid.

Lemma negative_object_of {C : quasiduploid} (a : C) (H : is_negative a)
  : a = object_of_negative_object (a,,H).
Proof. apply idpath. Defined.
Lemma positive_object_of {C : quasiduploid} (a : C) (H : is_positive a)
  : a = object_of_positive_object (a,,H).
Proof. apply idpath. Defined.

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

(* Inclusion functors for the above. *)
Definition positive_category_to_linear_category {C : quasiduploid}
  : functor (positive_category C) (linear_category C)
  := sub_precategory_inclusion _ _.
Definition negative_category_to_thunkable_category {C : quasiduploid}
  : functor (negative_category C) (thunkable_category C)
  := sub_precategory_inclusion _ _.

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

Definition duploid_homset {C : quasiduploid} (a b : C) : hSet :=
  make_hSet (a --> b) (duploid_homsets _ a b).
Definition duploid_fhomset {C : quasiduploid} {a b c d : C}
  (f : a --> b) (g : c --> d)
  (h : b --> c)
  : a --> d := f · h · g.

Lemma duploid_fhomset_id {C : quasiduploid} {a b : C} (h : a --> b)
  : duploid_fhomset (identity a) (identity b) h = h.
Proof.
  unfold duploid_fhomset.
  now rewrite duploid_id_left, duploid_id_right.
Qed.

Lemma duploid_fhomset_comp {C : quasiduploid} {a b c d u v : C}
  (f : a --> b) (g : c --> d)
  (h : u --> a) (k : d --> v)
  (y : b --> c)
  (Hf : is_thunkable f) (Hg : is_linear g)
  (Hh : is_thunkable h) (Hk : is_linear k)
  : duploid_fhomset (h · f) (g · k) y =
      duploid_fhomset h k (duploid_fhomset f g y).
Proof.
  unfold duploid_fhomset.
  rewrite (assoc_linear _ Hk).
  rewrite (assoc_linear _ Hg).
  now rewrite (assoc'_thunkable _ Hh).
Qed.

Definition duploid_fhomset_data (C : quasiduploid)
  : functor_data
      (category_binproduct
               ((thunkable_category C)^op)
               (linear_category C))
      HSET_univalent_category.
Proof.
  use make_functor_data.
  - intro ab. apply (duploid_homset (pr1 ab) (pr2 ab)).
  - intros ab cd fg h. apply (duploid_fhomset (pr11 fg) (pr12 fg) h).
Defined.

Lemma duploid_fhomset_is_functor (C : quasiduploid)
  : is_functor (duploid_fhomset_data C).
Proof.
  use make_is_functor.
  - intro ab.
    use funextfun; intro fg.
    apply duploid_fhomset_id.
  - intros bc ad uv fg hk.
    use funextfun; intro y.
    apply duploid_fhomset_comp.
    + apply is_thunkable_of_thunkable_mor.
    + apply is_linear_of_linear_mor.
    + apply is_thunkable_of_thunkable_mor.
    + apply is_linear_of_linear_mor.
Qed.

Definition duploid_homset_functor (C : quasiduploid)
  : linear_category C ↛ thunkable_category C
  := make_functor _ (duploid_fhomset_is_functor C).

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
  ∑ upshift : C -> C, ∏ a : C, upshift a --> a.
Definition duploid_wrap_data (C : quasiduploid) : UU :=
  ∑ downshift : C -> C, ∏ a : C, a --> downshift a.

Definition make_duploid_force_data {C : quasiduploid}
  (upshift : C -> C) (force : ∏ (a : C), upshift a --> a)
  : duploid_force_data C :=
  upshift,,force.
Definition make_duploid_wrap_data {C : quasiduploid}
  (downshift : C -> C) (wrap : ∏ (a : C), a --> downshift a)
  : duploid_wrap_data C :=
  downshift,,wrap.

Definition upshift' {C : quasiduploid} (D : duploid_force_data C) : C -> C := pr1 D.
Definition downshift' {C : quasiduploid} (D : duploid_wrap_data C) : C -> C := pr1 D.
Definition force' {C : quasiduploid} (D : duploid_force_data C) (a : C)
  : upshift' D a --> a := pr2 D a.
Definition wrap' {C : quasiduploid} (D : duploid_wrap_data C) (a : C)
  : a --> downshift' D a := pr2 D a.

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

Definition make_duploid {C : preduploid}
  (D : duploid_data C)
  (H : duploid_axioms D)
  : duploid
  := C,,D,,H.

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

Lemma is_precategory_of_quasiduploid (C : quasiduploid)
  (H : ∏ (a b c d : C) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h)
  : is_precategory C.
Proof.
  use make_is_precategory_one_assoc.
  - intros. apply duploid_id_left.
  - intros. apply duploid_id_right.
  - intros. apply H.
Qed.

Definition make_category_of_quasiduploid (C : quasiduploid) (H : is_precategory C) : category.
Proof.
  use make_category.
  - exact (make_precategory C H).
  - intros a b. apply duploid_homsets.
Qed.

Section lemmas.

Context {C : duploid}.

Lemma delay_force_right {a b : C} (f : a --> b) : (f · delay b) · force b = f.
Proof.
  rewrite (assoc'_linear _ (is_linear_force _)), delay_force_id.
  apply duploid_id_right.
Qed.

Lemma delay_force_left {a b : C} (f : a --> b) : delay a · (force a · f) = f.
Proof.
  rewrite (assoc_negative _ (⇑a)), delay_force_id.
  apply duploid_id_left.
Qed.

Lemma wrap_unwrap_left {a b : C} (f : a --> b) : wrap a · (unwrap a · f) = f.
Proof.
  rewrite (assoc_thunkable _ (is_thunkable_wrap _)), wrap_unwrap_id.
  apply duploid_id_left.
Qed.

Lemma wrap_unwrap_right {a b : C} (f : a --> b) : (f · wrap b) · unwrap b = f.
Proof.
  rewrite (assoc'_positive _ (⇓b)), wrap_unwrap_id.
  apply duploid_id_right.
Qed.

Lemma delay_force_interpose {a b c : C} (f : a --> b) (g : b --> c)
  : (f ⊙ delay b) ⊖ (force b ⊙ g) = f ⊙ g.
Proof. now rewrite (assoc_negative _ (⇑b)), delay_force_right. Qed.

Lemma wrap_unwrap_interpose {a b c : C} (f : a --> b) (g : b --> c)
  : (f ⊙ wrap b) ⊛ (unwrap b ⊙ g) = f ⊙ g.
Proof. now rewrite (assoc'_positive _ (⇓b)), wrap_unwrap_left. Qed.

Lemma is_thunkable_of_delay_wrap {a b : C} (f : a --> b)
  : f ⊙ (delay b ⊖ wrap (⇑b)) = (f ⊙ delay b) ⊖ wrap (⇑b) ->
    is_thunkable f.
Proof.
  intros Hf.
  assert (H' : ∏ (d : C) (h : ⇑b --> d), f ⊙ (delay b ⊖ h) = (f ⊙ delay b) ⊖ h). {
    intros d h.
    rewrite <- (wrap_unwrap_interpose (delay b) h).
    rewrite (assoc_positive _ (⇓⇑b)), Hf.
    rewrite (assoc'_negative _ (⇑b)).
    now rewrite wrap_unwrap_left.
  }
  intros c d g h.
  intermediate_path (f · (delay b · (force b · g) · h)).
    now rewrite delay_force_left.
  rewrite (assoc'_negative _ (⇑b)), H'.
  rewrite (assoc_negative _ (⇑b)), <- H'.
  now rewrite delay_force_left.
Qed.

Lemma is_linear_of_force_unwrap {a b : C} (f : b --> a)
  : (force (⇓b) · unwrap b) · f = force (⇓b) · (unwrap b · f) ->
    is_linear f.
Proof.
  intros Hf.
  assert (H' : ∏ (d : C) (h : d --> ⇓b), (h · unwrap b) · f = h · (unwrap b · f)). {
    intros d h.
    rewrite <- (delay_force_interpose h (unwrap b)).
    rewrite (assoc'_negative _ (⇑⇓b)), Hf.
    rewrite (assoc_positive _ (⇓b)).
    now rewrite delay_force_right.
  }
  intros c d g h.
  intermediate_path ((h · ((g · wrap b) · unwrap b)) · f).
    now rewrite wrap_unwrap_right.
  rewrite (assoc_positive _ (⇓b)), H'.
  rewrite (assoc'_positive _ (⇓b)), <- H'.
  now rewrite wrap_unwrap_right.
Qed.

End lemmas.

Section adjunction.

Context {C₁ C₂ : category} (θ : adjunction C₂ C₁).
Let F : functor C₂ C₁ := left_functor θ.
Let G : functor C₁ C₂ := right_functor θ.
Let H : are_adjoints F G := θ.
Let η : nat_trans (functor_identity C₂) (F ∙ G) := unit_from_are_adjoints H.
Let ε : nat_trans (G ∙ F) (functor_identity C₁) := counit_from_are_adjoints H.

Definition oblique_ob := C₁ ⨿ C₂.

Definition oblique_negativise (a : oblique_ob) : C₁.
Proof. induction a as [n | p]. exact n. exact (F p). Defined.
Definition oblique_positivise (a : oblique_ob) : C₂.
Proof. induction a as [n | p]. exact (G n). exact p. Defined.

Notation "a '⁻'" := (oblique_negativise a) : duploid.
Notation "a '⁺'" := (oblique_positivise a) : duploid.

Definition oblique_mor (a b : oblique_ob) := C₁⟦F (a⁺), b⁻⟧.

Lemma isaset_oblique_mor (a b : oblique_ob) : isaset (oblique_mor a b).
Proof. apply C₁. Qed.

Definition oblique_identity (a : oblique_ob) : oblique_mor a a.
Proof.
  induction a.
  + apply (φ_adj_inv H), identity.
  + apply identity.
Defined.

Definition oblique_compose {a b c : oblique_ob}
  (f : oblique_mor a b) (g : oblique_mor b c)
  : oblique_mor a c.
Proof.
  induction b.
  + exact (φ_adj_inv H (φ_adj H f · φ_adj H g)).
  + exact (f · g).
Defined.

Lemma oblique_left_id {a b : oblique_ob} (f : oblique_mor a b) :
  oblique_compose (oblique_identity a) f = f.
Proof.
  induction a; simpl.
  + rewrite φ_adj_after_φ_adj_inv, id_left.
    apply φ_adj_inv_after_φ_adj.
  + apply id_left.
Qed.

Lemma oblique_right_id {a b : oblique_ob} (f : oblique_mor a b) :
  oblique_compose f (oblique_identity b) = f.
Proof.
  induction b; simpl.
  + rewrite φ_adj_after_φ_adj_inv, id_right.
    apply φ_adj_inv_after_φ_adj.
  + apply id_right.
Qed.

Definition oblique_quasiduploid : quasiduploid.
Proof.
  use make_quasiduploid.
  - use make_precategory_data.
    + exact (make_precategory_ob_mor oblique_ob oblique_mor).
    + exact oblique_identity.
    + intros a b c f g. exact (oblique_compose f g).
  - intros a b. apply isaset_oblique_mor.
  - use make_is_quasiduploid.
    + intros a b f. apply oblique_left_id.
    + intros a b f. apply oblique_right_id.
Defined.

Definition oblique_negative (a : C₁) : oblique_quasiduploid := inl a.
Definition oblique_positive (a : C₂) : oblique_quasiduploid := inr a.

Lemma is_negative_of_adj_left (a : C₁) : is_negative (oblique_negative a).
Proof.
  intros b f c d g h.
  induction c as [m | q]; unfold compose; simpl.
  + do 2 rewrite φ_adj_after_φ_adj_inv.
    now rewrite assoc.
  + rewrite φ_adj_natural_postcomp, assoc.
    now rewrite φ_adj_inv_natural_postcomp.
Qed.

Lemma is_positive_of_adj_right (a : C₂) : is_positive (oblique_positive a).
Proof.
  intros b f c d g h.
  induction c as [m | q]; unfold compose; simpl.
  + rewrite φ_adj_natural_postcomp, assoc.
    now rewrite φ_adj_inv_natural_postcomp.
  + apply assoc'.
Qed.

Lemma is_polarized_oblique_quasiduploid : is_polarized oblique_quasiduploid.
Proof.
  intro a.
  apply hinhpr.
  induction a as [n | p].
  - right; apply is_negative_of_adj_left.
  - left; apply is_positive_of_adj_right.
Qed.

Definition oblique_preduploid : preduploid :=
  make_preduploid is_polarized_oblique_quasiduploid.

Definition oblique_upshift (a : oblique_preduploid) : oblique_preduploid.
Proof.
  induction a as [n | p]; apply oblique_negative.
  - exact n.
  - exact (F p).
Defined.

Definition oblique_force (a : oblique_preduploid) : oblique_upshift a --> a.
Proof.
  induction a as [n | p].
  + apply identity.
  + apply (φ_adj_inv H), identity.
Defined.

Definition oblique_delay (a : oblique_preduploid) : a --> oblique_upshift a.
Proof.
  induction a as [n | p].
  + apply identity.
  + apply (identity (F p)).
Defined.

Definition oblique_downshift (a : oblique_preduploid) : oblique_preduploid.
Proof.
  induction a as [n | p]; apply oblique_positive.
  + exact (G n).
  + exact p.
Defined.

Definition oblique_wrap (a : oblique_preduploid) : a --> oblique_downshift a.
Proof.
  induction a as [n | p].
  + apply (identity (F (G n))).
  + apply identity.
Defined.

Definition oblique_unwrap (a : oblique_preduploid) : oblique_downshift a --> a.
Proof.
  induction a as [n | p].
  + apply (φ_adj_inv H), identity.
  + apply identity.
Defined.

Lemma is_negative_oblique_upshift (a : oblique_preduploid)
  : is_negative (oblique_upshift a).
Proof. induction a; apply is_negative_of_adj_left. Qed.

Lemma is_positive_oblique_downshift (a : oblique_preduploid)
  : is_positive (oblique_downshift a).
Proof. induction a; apply is_positive_of_adj_right. Qed.

Lemma is_linear_oblique_force (a : oblique_preduploid)
  : is_linear (oblique_force a).
Proof.
  induction a as [n | p].
  1: apply is_linear_identity.
  intros b c f g.
  induction b as [m | q].
  1: now rewrite (assoc'_negative _ (is_negative_of_adj_left _)).
  unfold compose; simpl.
  rewrite φ_adj_after_φ_adj_inv.
  now do 2 rewrite id_right, φ_adj_inv_after_φ_adj.
Qed.

Definition is_thunkable_oblique_wrap (a : oblique_preduploid)
  : is_thunkable (oblique_wrap a).
Proof.
  induction a as [n | p].
  2: apply is_thunkable_identity.
  intros b c f g.
  induction b as [m | q].
  2: now rewrite (assoc'_positive _ (is_positive_of_adj_right _)).
  unfold compose; simpl.
  now do 2 rewrite id_left.
Qed.

Lemma is_linear_oblique_delay (a : oblique_preduploid)
  : is_linear (oblique_delay a).
Proof.
  induction a as [n | p].
  2: apply is_linear_of_positive, is_positive_of_adj_right.
  intros b c f g.
  induction b as [m | q].
  1: apply assoc'_negative, is_negative_of_adj_left.
  cbn.
  rewrite φ_adj_natural_postcomp.
  rewrite φ_adj_after_φ_adj_inv.
  do 2 rewrite id_right.
  rewrite φ_adj_inv_natural_postcomp.
  now do 2 rewrite φ_adj_inv_after_φ_adj.
Qed.

Lemma is_thunkable_oblique_unwrap (a : oblique_preduploid)
  : is_thunkable (oblique_unwrap a).
Proof.
  induction a as [n | p].
  1: apply is_thunkable_of_negative, is_negative_of_adj_left.
  intros b c f g.
  induction b as [m | q].
  2: apply assoc_positive, is_positive_of_adj_right.
  cbn.
  now do 2 rewrite id_left.
Qed.

Definition is_inverse_in_precat_oblique_force_delay (a : oblique_preduploid)
  : is_inverse_in_precat (oblique_force a) (oblique_delay a).
Proof.
  induction a as [n | p]; simpl; split; unfold identity, compose; simpl;
    fold (identity (C:=C₂)); fold (identity (C:=C₁)).
  - now rewrite φ_adj_after_φ_adj_inv, id_left.
  - now rewrite φ_adj_after_φ_adj_inv, id_left.
  - now rewrite id_right.
  - now rewrite φ_adj_after_φ_adj_inv, id_right, φ_adj_inv_after_φ_adj.
Qed.

Definition is_inverse_in_precat_oblique_wrap_unwrap (a : oblique_preduploid)
  : is_inverse_in_precat (oblique_wrap a) (oblique_unwrap a).
Proof.
  induction a as [n | p]; simpl; split; unfold identity, compose; simpl;
    fold (identity (C:=C₂)); fold (identity (C:=C₁)).
  - now rewrite id_left.
  - now rewrite φ_adj_after_φ_adj_inv, id_left, φ_adj_inv_after_φ_adj.
  - apply id_left.
  - apply id_left.
Qed.

Definition oblique_duploid_data : duploid_data oblique_preduploid.
Proof.
  apply make_duploid_data.
  - exact (make_duploid_force_data oblique_upshift oblique_force).
  - exact (make_duploid_wrap_data oblique_downshift oblique_wrap).
Defined.

Definition oblique_duploid_axioms : duploid_axioms oblique_duploid_data.
Proof.
  apply make_duploid_axioms.
  - use make_duploid_force_axioms.
    + apply is_negative_oblique_upshift.
    + apply is_linear_oblique_force.
    + apply oblique_delay.
    + apply is_inverse_in_precat_oblique_force_delay.
  - use make_duploid_wrap_axioms.
    + apply is_positive_oblique_downshift.
    + apply is_thunkable_oblique_wrap.
    + apply oblique_unwrap.
    + apply is_inverse_in_precat_oblique_wrap_unwrap.
Defined.

(* The oblique duploid is the duploid arising from an adjunction,
   where objects are objects in either category, and morphisms
   are the morphisms C₁⟦F a⁺, b⁻⟧ (equivalently C₂⟦a⁻, G b⁺⟧). *)
Definition oblique_duploid : duploid
  := make_duploid oblique_duploid_data oblique_duploid_axioms.

Lemma is_linear_of_oblique_counit_precompose {n : C₁} {a : oblique_duploid}
  (f : oblique_negative n --> a)
  : #(G ∙ F) (ε n) · f = ε ((G ∙ F) n) · f ->
    is_linear f.
Proof.
  intro Hf.
  apply (is_linear_of_force_unwrap (C:=oblique_duploid)).
  unfold force, unwrap, compose; simpl.
  rewrite φ_adj_natural_postcomp, φ_adj_inv_natural_precomp.
  do 2 rewrite φ_adj_after_φ_adj_inv, id_left, φ_adj_inv_after_φ_adj.
  unfold φ_adj_inv; fold ε.
  do 2 rewrite functor_id, id_left.
  exact Hf.
Qed.

Lemma is_thunkable_of_oblique_unit_postcompose {a : oblique_duploid} {p : C₂}
  (f : a --> oblique_positive p)
  : φ_adj H f · #(F ∙ G) (η p) = φ_adj H f · η ((F ∙ G) p) ->
    is_thunkable f.
Proof.
  intro Hf.
  apply (is_thunkable_of_delay_wrap (C:=oblique_duploid)).
  eenough (H' : φ_adj_inv H (φ_adj H _) = φ_adj_inv H (φ_adj H _)). {
    do 2 rewrite φ_adj_inv_after_φ_adj in H'.
    exact H'.
  }
  apply maponpaths.
  unfold delay, wrap, compose; simpl.
  do 2 rewrite φ_adj_natural_postcomp, φ_adj_inv_natural_precomp.
  rewrite φ_adj_inv_after_φ_adj, functor_id.
  do 2 rewrite id_right.
  rewrite functor_comp, functor_id, φ_adj_natural_precomp.
  do 2 rewrite φ_adj_identity. fold η.
  exact Hf.
Qed.

Corollary is_precategory_of_oblique_idempotent_adjunction
  (H1 : post_whisker ε (G ∙ F) = pre_whisker (G ∙ F) ε)
  : is_precategory oblique_duploid.
Proof.
  use is_precategory_of_quasiduploid.
  intros a b c d f g h.
  apply assoc_linear.
  induction c as [n | p].
  2: apply is_linear_of_positive, is_positive_of_adj_right.
  apply is_linear_of_oblique_counit_precompose.
  intermediate_path (post_whisker ε (G ∙ F) n · h).
    apply idpath.
  now rewrite H1.
Qed.

End adjunction.

Section functors.

Context {C : duploid}.

(* Guillame claims that upshiftf takes linear morphisms to linear morphisms, and
   dually for downshiftf. This is hard to believe in general, and so upshiftf is
   only a functor [linear_category C → negative_category C], rather than
   [linear_category C → negative_linear_category C]; and dually for
   downshiftf. This should suffice for the main results, however. *)

Definition upshiftf {a b : C} (f : a --> b) : ⇑a --> ⇑b := (force a · f) · delay b.
Definition downshiftf {a b : C} (f : a --> b) : ⇓a --> ⇓b := unwrap a · (f · wrap b).

Notation "'#⇑' f" := (upshiftf f) (at level 40) : duploid.
Notation "'#⇓' f" := (downshiftf f) (at level 40) : duploid.

Lemma upshiftf_id {a : C} : #⇑identity a = identity (⇑a).
Proof. unfold upshiftf. now rewrite duploid_id_right, force_delay_id. Qed.
Lemma downshiftf_id {a : C} : #⇓identity a = identity (⇓a).
Proof. unfold downshiftf. now rewrite duploid_id_left, unwrap_wrap_id. Qed.

Lemma upshiftf_comp {a b c : C} (f : linear_mor a b) (g : linear_mor b c)
  : #⇑(f · g) = (#⇑f) · (#⇑g).
Proof.
  unfold upshiftf.
  rewrite (assoc_negative _ (⇑b)).
  do 2 rewrite (assoc_linear _ g).
  now rewrite delay_force_right.
Qed.

Lemma downshiftf_comp {a b c : C} (f : thunkable_mor a b) (g : thunkable_mor b c)
  : #⇓(f · g) = (#⇓f) · (#⇓g).
Proof.
  unfold downshiftf.
  rewrite (assoc'_positive _ (⇓b)).
  do 2 rewrite (assoc'_thunkable _ f).
  now rewrite wrap_unwrap_left.
Qed.

Definition upshift_functor :
  functor (linear_category C) (negative_category C).
Proof.
  use make_functor.
  - use make_functor_data.
    + exact upshift.
    + intros a b f.
      apply embed_negative_mor, (#⇑pr1 f).
  - use make_is_functor.
    + intros a. apply carrier_eq, carrier_eq, upshiftf_id.
    + intros a b c f g. apply carrier_eq, carrier_eq, upshiftf_comp.
Defined.

Definition downshift_functor :
  functor (thunkable_category C) (positive_category C).
Proof.
  use make_functor.
  - use make_functor_data.
    + exact downshift.
    + intros a b f.
      apply embed_positive_mor, (#⇓pr1 f).
  - use make_is_functor.
    + intros a. apply carrier_eq, carrier_eq, downshiftf_id.
    + intros a b c f g. apply carrier_eq, carrier_eq, downshiftf_comp.
Defined.

Definition included_upshift_functor
  : functor (linear_category C) (thunkable_category C)
  := upshift_functor ∙ negative_category_to_thunkable_category.
Definition included_downshift_functor
  : functor (thunkable_category C) (linear_category C)
  := downshift_functor ∙ positive_category_to_linear_category.

(* The functor [thunkable_category C⟦∙, I⇑∙⟧]. *)
Definition duploid_upshifted_homset_functor
  : linear_category C ↛ thunkable_category C.
Proof.
  eapply functor_composite.
  2: eapply homSet_functor.
  apply pair_functor.
  1: apply functor_identity.
  apply included_upshift_functor.
Defined.

(* The functor [linear_category C⟦I⇓∙, ∙⟧]. *)
Definition duploid_downshifted_homset_functor
  : linear_category C ↛ thunkable_category C.
Proof.
  eapply functor_composite.
  2: eapply homSet_functor.
  apply pair_functor.
  2: apply functor_identity.
  apply functor_opp, included_downshift_functor.
Defined.

(* thunkable_category C⟦∙, I⇑∙⟧ ≃ C⟦∙, ∙⟧ *)
Definition duploid_mor_to_thunkable_mor (a b : C)
  (f : C⟦a, b⟧) : thunkable_category C⟦a, ⇑b⟧.
Proof.
  exists (f · delay b).
  apply (is_thunkable_of_negative _ (⇑_)).
Defined.

Definition thunkable_mor_to_duploid_mor (a b : C)
  (f : thunkable_category C⟦a, ⇑b⟧) : C⟦a, b⟧.
Proof.
  exact (pr1 f · force b).
Defined.

Lemma is_inverse_duploid_mor_to_from_thunkable_mor (a b : C)
  (f : C⟦a, b⟧)
  : thunkable_mor_to_duploid_mor _ _ (duploid_mor_to_thunkable_mor _ _ f) = f.
Proof. apply delay_force_right. Qed.

Lemma is_inverse_duploid_mor_from_to_thunkable_mor (a b : C)
  (f : thunkable_category C⟦a, ⇑b⟧)
  : duploid_mor_to_thunkable_mor _ _ (thunkable_mor_to_duploid_mor _ _ f) = f.
Proof.
  apply carrier_eq.
  intermediate_path (pr1 f · (force b · delay b)).
  1: apply (assoc'_thunkable _ (pr2 f)).
  now rewrite force_delay_id, duploid_id_right.
Qed.

Lemma isweq_duploid_mor_to_thunkable_mor (a b : C)
  : isweq (duploid_mor_to_thunkable_mor a b).
Proof.
  use isweq_iso.
  - apply thunkable_mor_to_duploid_mor.
  - apply is_inverse_duploid_mor_to_from_thunkable_mor.
  - apply is_inverse_duploid_mor_from_to_thunkable_mor.
Qed.

Lemma isweq_thunkable_mor_to_duploid_mor (a b : C)
  : isweq (thunkable_mor_to_duploid_mor a b).
Proof.
  use isweq_iso.
  - apply duploid_mor_to_thunkable_mor.
  - apply is_inverse_duploid_mor_from_to_thunkable_mor.
  - apply is_inverse_duploid_mor_to_from_thunkable_mor.
Qed.

Definition weq_duploid_mor_thunkable_mor (a b : C)
  : C⟦a, b⟧ ≃ thunkable_category C⟦a, ⇑b⟧
  := make_weq _ (isweq_duploid_mor_to_thunkable_mor a b).
Definition weq_thunkable_mor_duploid_mor (a b : C)
  : thunkable_category C⟦a, ⇑b⟧ ≃ C⟦a, b⟧
  := make_weq _ (isweq_thunkable_mor_to_duploid_mor a b).

Definition duploid_mor_to_linear_mor (a b : C)
  (f : C⟦a, b⟧) : linear_category C⟦⇓a, b⟧.
Proof.
  exists (unwrap a · f).
  apply (is_linear_of_positive _ (⇓_)).
Defined.

Definition linear_mor_to_duploid_mor (a b : C)
  (f : linear_category C⟦⇓a, b⟧) : C⟦a, b⟧.
Proof.
  exact (wrap a · pr1 f).
Defined.

Lemma is_inverse_duploid_mor_to_from_linear_mor (a b : C)
  (f : C⟦a, b⟧)
  : linear_mor_to_duploid_mor _ _ (duploid_mor_to_linear_mor _ _ f) = f.
Proof. apply wrap_unwrap_left. Qed.

Lemma is_inverse_duploid_mor_from_to_linear_mor (a b : C)
  (f : linear_category C⟦⇓a, b⟧)
  : duploid_mor_to_linear_mor _ _ (linear_mor_to_duploid_mor _ _ f) = f.
Proof.
  apply carrier_eq.
  intermediate_path ((unwrap a · wrap a) · pr1 f).
  1: apply (assoc_linear _ (pr2 f)).
  now rewrite unwrap_wrap_id, duploid_id_left.
Qed.

Lemma isweq_duploid_mor_to_linear_mor (a b : C)
  : isweq (duploid_mor_to_linear_mor a b).
Proof.
  use isweq_iso.
  - apply linear_mor_to_duploid_mor.
  - apply is_inverse_duploid_mor_to_from_linear_mor.
  - apply is_inverse_duploid_mor_from_to_linear_mor.
Qed.

Lemma isweq_linear_mor_to_duploid_mor (a b : C)
  : isweq (linear_mor_to_duploid_mor a b).
Proof.
  use isweq_iso.
  - apply duploid_mor_to_linear_mor.
  - apply is_inverse_duploid_mor_from_to_linear_mor.
  - apply is_inverse_duploid_mor_to_from_linear_mor.
Qed.

Definition weq_duploid_mor_linear_mor (a b : C)
  : C⟦a, b⟧ ≃ linear_category C⟦⇓a, b⟧
  := make_weq _ (isweq_duploid_mor_to_linear_mor a b).
Definition weq_linear_mor_duploid_mor (a b : C)
  : linear_category C⟦⇓a, b⟧ ≃ C⟦a, b⟧
  := make_weq _ (isweq_linear_mor_to_duploid_mor a b).

(* The adjunction ⇓ -| ⇑ : thunkable_category C -> linear_category C *)
Theorem are_adjoints_downshift_upshift
  : are_adjoints
      (A:=thunkable_category C)
      (B:=linear_category C)
      included_downshift_functor
      included_upshift_functor.
Proof.
  use adj_from_nathomweq.
  use tpair. {
    intros a b.
    eapply weqcomp.
    apply weq_linear_mor_duploid_mor.
    apply weq_duploid_mor_thunkable_mor.
  }
  use tpair.
  - intros a b f c h.
    apply carrier_eq.
    simpl.
    change ((wrap c ⊙ ((#⇓ pr1 h) ⊙ pr1 f)) ⊙ delay b
            = pr1 h ⊙ ((wrap a ⊙ pr1 f) ⊙ delay b)).
    unfold downshiftf.
    rewrite (assoc_thunkable _ (pr2 h)).
    do 2 rewrite (assoc'_linear _ (pr2 f)).
    now rewrite wrap_unwrap_left.
  - intros a b f c h.
    apply carrier_eq.
    change ((wrap a ⊙ (pr1 f ⊙ pr1 h)) ⊙ delay c
            = ((wrap a ⊙ pr1 f) ⊙ delay b) ⊙ (#⇑ pr1 h)).
    unfold upshiftf.
    rewrite (assoc_negative _ (⇑b)).
    rewrite delay_force_interpose.
    now rewrite (assoc_linear _ (pr2 h)).
Defined.

End functors.

Definition polarization_choice_data (C : quasiduploid) : UU
  := ob C -> bool.

Identity Coercion Id_polarization_choice_data : polarization_choice_data >-> Funclass.

Lemma isaset_polarization_choice_data (C : quasiduploid)
  : isaset (polarization_choice_data C).
Proof.
  apply impred_isaset; intro.
  apply isasetbool.
Qed.

Definition is_polarization_choice {C : quasiduploid}
  (polarity : polarization_choice_data C) : UU.
Proof.
  refine (∏ (a : C), _).
  induction (polarity a).
  - exact (is_positive a).
  - exact (is_negative a).
Defined.

Lemma isaprop_is_polarization_choice {C : quasiduploid}
  (polarity : polarization_choice_data C)
  : isaprop (is_polarization_choice polarity).
Proof.
  apply impred; intro a.
  induction (polarity a).
  - apply isaprop_is_positive.
  - apply isaprop_is_negative.
Qed.

Definition polarization_choice (C : quasiduploid)
  := ∑ (polarity : polarization_choice_data C),
    is_polarization_choice polarity.

Lemma isaset_polarization_choice (C : quasiduploid)
  : isaset (polarization_choice C).
Proof.
  apply isaset_total2.
  - apply isaset_polarization_choice_data.
  - intro x. apply isasetaprop, isaprop_is_polarization_choice.
Qed.

Coercion data_of_polarization_choice (C : quasiduploid)
  (polarization : polarization_choice C)
  : polarization_choice_data C := pr1 polarization.

Definition shifts_respect_polarization_choice
  {C : duploid} (polarization : polarization_choice C) : UU
  := (∏ (a : C), polarization (⇓a) = true)
       × (∏ (a : C), polarization (⇑a) = false).

Lemma isaprop_shifts_respect_polarization_choice
  {C : duploid} (polarization : polarization_choice C)
  : isaprop (shifts_respect_polarization_choice polarization).
Proof.
  apply isapropdirprod; apply impred; intro a;
    apply isasetbool.
Qed.

Definition functor_preserves_polarization_choice
  {C C' : quasiduploid}
  (HC : polarization_choice C)
  (HC' : polarization_choice C')
  (F : functor C C') : UU
  := ∏ (a : C), HC' (F a) = HC a.

Lemma isaprop_functor_preserves_polarization_choice
  {C C' : quasiduploid}
  (HC : polarization_choice C)
  (HC' : polarization_choice C')
  (F : functor C C')
  : isaprop (functor_preserves_polarization_choice HC HC' F).
Proof. apply impred; intro a; apply isasetbool. Qed.

Definition split_preduploid : UU
  := ∑ (C : preduploid), polarization_choice C.
Coercion preduploid_of_split_preduploid (C : split_preduploid) : preduploid := pr1 C.
Coercion preduploid_polarization_choice
  (C : split_preduploid) : polarization_choice C := pr2 C.
Definition make_split_preduploid (C : preduploid) (H : polarization_choice C)
  : split_preduploid := C,,H.

Definition split_duploid : UU
  := ∑ (C : duploid), polarization_choice C.
Coercion duploid_of_split_duploid (C : split_duploid) : duploid := pr1 C.
Coercion duploid_polarization_choice
  (C : split_duploid) : polarization_choice C := pr2 C.
Definition make_split_duploid (C : duploid) (H : polarization_choice C)
  : split_duploid := C,,H.

Coercion split_preduploid_of_split_duploid (C : split_duploid) : split_preduploid
  := make_split_preduploid C C.

Definition functor_preserves_shifts {C C' : duploid}
  (F : functor C C') : UU
  := (∏ (a : C), is_linear (#F (force a)))
       × (∏ (a : C), is_thunkable (#F (wrap a))).

Lemma isaprop_functor_preserves_shifts {C C' : duploid}
  (F : functor C C')
  : isaprop (functor_preserves_shifts F).
Proof.
  apply isapropdirprod; apply impred; intro a.
  - apply isaprop_is_linear.
  - apply isaprop_is_thunkable.
Qed.

Definition split_preduploid_functor (C C' : split_preduploid) : UU
  := ∑ (F : functor C C'),
    functor_preserves_polarization_choice C C' F.
Coercion functor_of_split_preduploid_functor {C C' : split_preduploid}
  (F : split_preduploid_functor C C') : functor C C' := pr1 F.
Coercion split_preduploid_functor_preserves_polarization_choice {C C' : split_preduploid}
  (F : split_preduploid_functor C C')
  : functor_preserves_polarization_choice C C' F := pr2 F.
Definition make_split_preduploid_functor {C C' : split_preduploid}
  (F : functor C C') (H : functor_preserves_polarization_choice C C' F)
  : split_preduploid_functor C C' := F,,H.

Definition split_duploid_functor (C C' : split_duploid) : UU
  := ∑ (F : split_preduploid_functor C C'),
    functor_preserves_shifts F.
Coercion split_preduploid_functor_of_split_duploid_functor {C C' : split_duploid}
  (F : split_duploid_functor C C') : split_preduploid_functor C C' := pr1 F.
Coercion split_duploid_functor_preserves_shifts {C C' : split_duploid}
  (F : split_duploid_functor C C')
  : functor_preserves_shifts F := pr2 F.
Definition make_split_duploid_functor {C C' : split_duploid}
  (F : split_preduploid_functor C C') (H : functor_preserves_shifts F)
  : split_duploid_functor C C' := F,,H.

Definition split_preduploid_functor_identity (C : split_preduploid)
  : split_preduploid_functor C C.
Proof.
  use make_split_preduploid_functor.
  - apply functor_identity.
  - intro a. apply idpath.
Defined.

Definition split_duploid_functor_identity (C : split_duploid)
  : split_duploid_functor C C.
Proof.
  use make_split_duploid_functor.
  - apply split_preduploid_functor_identity.
  - split; intro a.
    + apply is_linear_force.
    + apply is_thunkable_wrap.
Defined.

Definition split_preduploid_functor_compose {C₁ C₂ C₃ : split_preduploid}
  (F : split_preduploid_functor C₁ C₂)
  (G : split_preduploid_functor C₂ C₃)
  : split_preduploid_functor C₁ C₃.
Proof.
  use make_split_preduploid_functor.
  - exact (F ∙ G).
  - intro a; simpl.
    rewrite (split_preduploid_functor_preserves_polarization_choice G).
    apply (split_preduploid_functor_preserves_polarization_choice F).
Defined.

Definition is_linear_and_thunkable {C : precategory_data}
  {a b : C} (f : a --> b) : UU
  := is_linear f × is_thunkable f.

Lemma isaprop_is_linear_and_thunkable {C : quasiduploid}
  {a b : C} (f : a --> b)
  : isaprop (is_linear_and_thunkable f).
Proof.
  apply isapropdirprod.
  apply isaprop_is_linear.
  apply isaprop_is_thunkable.
Qed.

Definition are_linear_and_thunkable_inverses {C : quasiduploid}
  {a b : C} (f : a --> b) (g : b --> a) : UU
  := is_inverse_in_precat f g
       × is_linear_and_thunkable f
       × is_linear_and_thunkable g.

Lemma isaprop_are_linear_and_thunkable_inverses {C : quasiduploid}
  {a b : C} (f : a --> b) (g : b --> a)
  : isaprop (are_linear_and_thunkable_inverses f g).
Proof.
  apply isapropdirprod; apply isapropdirprod.
  1, 2: apply duploid_homsets.
  1, 2: apply isaprop_is_linear_and_thunkable.
Qed.

Lemma is_linear_and_thunkable_identity {C : quasiduploid} (a : C)
  : is_linear_and_thunkable (identity a).
Proof.
  use tpair.
  apply is_linear_identity.
  apply is_thunkable_identity.
Qed.

Definition is_linear_and_thunkable_z_isomorphism {C : quasiduploid}
  {a b : C} (f : a --> b) : UU
  := ∑ (g : b --> a), are_linear_and_thunkable_inverses f g.

Definition isaprop_is_linear_and_thunkable_z_isomorphism {C : quasiduploid}
  {a b : C} (f : a --> b)
  : isaprop (is_linear_and_thunkable_z_isomorphism f).
Proof.
  apply isaproptotal2.
  1: intro h; apply isaprop_are_linear_and_thunkable_inverses.
  intros g g' H1 H2.
  apply (linear_inverse_unique f g g' (pr1 H1) (pr1 H2)).
  exact (pr122 H1).
Qed.

Definition is_linear_and_thunkable_z_isomorphism_idtomor {C : quasiduploid}
  {a b : C} (p : a = b)
  : is_linear_and_thunkable_z_isomorphism (idtomor _ _ p).
Proof.
  induction p.
  use tpair.
  1: apply identity.
  use tpair.
  1: use make_is_inverse_in_precat; apply duploid_id_left.
  use tpair.
  all: apply is_linear_and_thunkable_identity.
Defined.

Definition duploid_indistinguishable {C : quasiduploid} (a b : C)
  := ∑ (f : a --> b), is_linear_and_thunkable_z_isomorphism f.

Coercion duploid_indistinguishable_to_z_iso {C : quasiduploid} {a b : C}
  (f : duploid_indistinguishable a b) : z_iso a b.
Proof.
  use make_z_iso.
  - apply (pr1 f).
  - apply (pr12 f).
  - apply (pr122 f).
Defined.

Definition is_positive_of_duploid_indistinguishable {C : quasiduploid}
  (a b : C) : duploid_indistinguishable a b -> is_positive a -> is_positive b.
Proof.
  intros [f [f̂ [inv_f_f̂ [_ linear_and_thunkable_f̂]]]] Ha c g.
  assert (Hg : g = f̂ · (f · g)).
  { rewrite (assoc_thunkable _ (pr2 linear_and_thunkable_f̂)).
    now rewrite (pr2 inv_f_f̂), duploid_id_left. }
  rewrite Hg.
  apply is_linear_compose.
  - apply (pr1 linear_and_thunkable_f̂).
  - apply (is_linear_of_positive _ Ha).
Qed.

Definition is_negative_of_duploid_indistinguishable {C : quasiduploid}
  (a b : C) : duploid_indistinguishable a b -> is_negative a -> is_negative b.
Proof.
  intros [f [f̂ [inv_f_f̂ [linear_and_thunkable_f _]]]] Ha c g.
  assert (Hg : g = (g · f̂) · f).
  { rewrite (assoc'_linear _ (pr1 linear_and_thunkable_f)).
    now rewrite (pr2 inv_f_f̂), duploid_id_right. }
  rewrite Hg.
  apply is_thunkable_compose.
  - apply (is_thunkable_of_negative _ Ha).
  - apply (pr2 linear_and_thunkable_f).
Qed.

Definition id_to_duploid_indistinguishable {C : quasiduploid}
  {a b : C} (p : a = b) : duploid_indistinguishable a b.
Proof.
  use tpair.
  apply idtomor, p.
  apply is_linear_and_thunkable_z_isomorphism_idtomor.
Defined.

Definition duploid_is_univalent (C : quasiduploid) : UU
  := ∏ (a b : C), isweq (λ (p : a = b), id_to_duploid_indistinguishable p).

Definition isaprop_duploid_is_univalent (C : quasiduploid)
  : isaprop (duploid_is_univalent C).
Proof.
  do 2 (apply impred; intro).
  apply isapropisweq.
Qed.

End duploids.

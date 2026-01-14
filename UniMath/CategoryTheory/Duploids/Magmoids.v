(********************************************************************************

 Unital (pre)magmoids.

 A unital (pre)magmoid is a (pre)category without associativity.  It may also be
 called a "nonassociative category" as an allusion to this.  Another name is a
 "deductive system" as an allusion to its role in categorical semantics for
 nonassociative logic.

 This file provides alternative definitions of (pre)categories in terms of their
 unital (pre)magmoid, and coercions to reassociate all of the relevant data.
 This file also provides definitions and lemmas for working with unital
 magmoids, particularly important are the concepts of linearity, thunkability
 and polarization in section 4.

 Contents:
 1. Unbundled definitions of unitality and associativity
 2. Definition of a unital (pre)magmoid
 3. Alternative definitions of [precategory] and [category]
 4. Linearity, thunkability, and polarization
    1. Definitions of linearity, thunkability and polarization
    2. Lemmas for working with linearity, thunkability and polarization
    3. Bundled linear/thunkable morphisms and polarized objects
    4. Inverses and when they are unique
 5. Epics and monics in magmoids

 Author: B. Szilvasy
 January 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.opp_precat.

Local Open Scope cat.

Section magmoids.
  (** * 1. Unbundled definitions of unitality and associativity *)
  Definition unital_premagmoid_data := precategory_data.
  Identity Coercion Id_unital_premagmoid_data : unital_premagmoid_data >-> precategory_data.

  Definition is_unital_premagmoid (M : unital_premagmoid_data) : UU
    := ((∏ (a b : M) (f : a --> b), identity a · f = f)
          ×
          (∏ (a b : M) (f : a --> b), f · identity b = f)).
  Definition make_is_unital_premagmoid (M : unital_premagmoid_data)
    (H1 : ∏ (a b : M) (f : a --> b), identity a · f = f)
    (H2 : ∏ (a b : M) (f : a --> b), f · identity b = f)
    : is_unital_premagmoid M
    := H1,,H2.

  Definition isaprop_is_unital_premagmoid (M : unital_premagmoid_data) (hs : has_homsets M)
    : isaprop (is_unital_premagmoid M).
  Proof. apply isapropdirprod; do 3 (apply impred; intro); apply hs. Qed.

  Definition is_assoc_premagmoid (M : unital_premagmoid_data) : UU
    := ((∏ (a b c d : M) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h)
          ×
          (∏ (a b c d : M) (f : a --> b) (g : b --> c) (h : c --> d), (f · g) · h = f · (g · h))).
  Definition make_is_assoc_premagmoid (M : unital_premagmoid_data)
    (H1 : ∏ (a b c d : M) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h)
    (H2 : ∏ (a b c d : M) (f : a --> b) (g : b --> c) (h : c --> d), (f · g) · h = f · (g · h))
    : is_assoc_premagmoid M
    := H1,,H2.
  Definition make_is_one_assoc_premagmoid (M : unital_premagmoid_data)
    (H : ∏ (a b c d : M) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h)
    : is_assoc_premagmoid M
    := make_is_assoc_premagmoid M H (λ a b c d f g h, !H a b c d f g h).

  Definition isaprop_is_assoc_premagmoid (M : unital_premagmoid_data) (hs : has_homsets M)
    : isaprop (is_assoc_premagmoid M).
  Proof. apply isapropdirprod; do 7 (apply impred; intro); apply hs. Qed.

  (** * 2. Definition of a unital (pre)magmoid *)

  (** ** 1. Unital premagmoid *)
  Definition unital_premagmoid : UU
    := total2 is_unital_premagmoid.
  Coercion unital_premagmoid_to_precategory_data (M : unital_premagmoid) : unital_premagmoid_data := pr1 M.
  Definition unital_premagmoid_is_unital (M : unital_premagmoid) : is_unital_premagmoid M := pr2 M.
  Definition make_unital_premagmoid
    (M : unital_premagmoid_data) (H : is_unital_premagmoid M) : unital_premagmoid
    := M,,H.

  Definition magmoid_id_left {M : unital_premagmoid} {a b : M} (f : a --> b)
    : identity a · f = f
    := pr1 (unital_premagmoid_is_unital M) a b f.
  Definition magmoid_id_right {M : unital_premagmoid} {a b : M} (f : a --> b)
    : f · identity b = f
    := pr2 (unital_premagmoid_is_unital M) a b f.

  Definition precategory_is_unital (C : precategory) : is_unital_premagmoid C.
  Proof.
    use make_is_unital_premagmoid.
    - apply id_left.
    - apply id_right.
  Defined.

  Coercion precategory_to_unital_premagmoid (C : precategory) : unital_premagmoid
    := make_unital_premagmoid C (precategory_is_unital C).

  (** ** 2. Unital magmoid *)
  Definition unital_magmoid : UU
    := ∑ (M : unital_premagmoid), has_homsets M.
  Definition make_unital_magmoid
    (M : unital_premagmoid)
    (H : has_homsets M)
    : unital_magmoid
    := M,,H.
  Coercion unital_magmoid_to_unital_premagmoid (M : unital_magmoid) : unital_premagmoid := pr1 M.
  Definition unital_magmoid_has_homsets (M : unital_magmoid) : has_homsets M := pr2 M.
  Coercion category_to_unital_magmoid (M : category) : unital_magmoid
    := make_unital_magmoid M (homset_property M).

  Definition unital_magmoid_paths (N M : unital_magmoid)
    (data_eq : (N : precategory_data) = M)
    : N = M.
  Proof.
    apply subtypePath'.
    2: apply isaprop_has_homsets.
    apply subtypePath'.
    2: apply isaprop_is_unital_premagmoid, unital_magmoid_has_homsets.
    exact data_eq.
  Defined.

  (** ** 3. Alternative definitions of [precategory] and [category] *)

  (** *** 1. Alternative [precategory] *)
  Definition magmoid_precategory : UU
    := ∑ (M : unital_premagmoid), is_assoc_premagmoid M.
  Definition make_magmoid_precategory
    (M : unital_premagmoid)
    (H : is_assoc_premagmoid M) : magmoid_precategory
    := M,,H.
  Coercion magmoid_precategory_to_unital_premagmoid (C : magmoid_precategory) : unital_premagmoid := pr1 C.
  Definition magmoid_precategory_is_assoc (C : magmoid_precategory) : is_assoc_premagmoid C := pr2 C.

  Definition magmoid_precategory_is_precategory (C : magmoid_precategory) : is_precategory C.
  Proof.
    use make_dirprod.
    - apply unital_premagmoid_is_unital.
    - apply magmoid_precategory_is_assoc.
  Defined.
  Coercion magmoid_precategory_to_precategory (C : magmoid_precategory) : precategory
    := make_precategory C (magmoid_precategory_is_precategory C).

  Definition precategory_is_assoc (C : precategory) : is_assoc_premagmoid C.
  Proof.
    use make_is_assoc_premagmoid.
    - apply assoc.
    - apply assoc'.
  Defined.

  Coercion precategory_to_magmoid_precategory (C : precategory) : magmoid_precategory
    := make_magmoid_precategory C (precategory_is_assoc C).

  (** *** 2. Alternative [category] *)
  Definition magmoid_category : UU
    := ∑ (M : unital_magmoid), is_assoc_premagmoid M.
  Definition make_magmoid_category
    (M : unital_magmoid)
    (H : is_assoc_premagmoid M)
    : magmoid_category
    := M,,H.
  Coercion magmoid_category_to_unital_magmoid (M : magmoid_category) : unital_magmoid := pr1 M.
  Definition magmoid_category_is_assoc (M : magmoid_category) : is_assoc_premagmoid M := pr2 M.
  Coercion magmoid_category_to_magmoid_precategory (M : magmoid_category) : magmoid_precategory
    := make_magmoid_precategory M (magmoid_category_is_assoc M).
  Coercion magmoid_category_to_category (M : magmoid_category) : category
    := make_category M (unital_magmoid_has_homsets M).

  Coercion category_to_magmoid_category (M : category) : magmoid_category
    := make_magmoid_category M (precategory_is_assoc M).

End magmoids.

(** ** 4. Linearity, thunkability, and polarization

 1. A *linear* morphism associates when it is on the *right*.
 2. A *thunkable* morphism associates when it is on the *left*.
 3. A *positive* object is one where all *outgoing* morphisms are *linear*.
 4. A *negative* object is one where all *incoming* morphisms are *thunkable*.

 In other words, given objects and morphisms as follows, composition associates
 if any one of the annotations holds:

                       thunkable ↓           ↓ linear
                                 f     g     h
                              A --> B --> C --> D
                           negative ↑     ↑ positive

 When any of those named properties can be proven, the lemmas below can be used
 to reassociate:

 - [assoc_*]  : f · (g · h) = (f · g) · h     ("to the left")
 - [assoc'_*] : (f · g) · h) = f · (g · h)    ("to the right")

 Identities are both linear and thunkable, and composition preserves linearity.
 Indeed, a unital magmoid's submagmoid of linear morphisms is a category, and
 likewise for thunkable morphisms, but those definitions and more are in
 [Subcategories.v].

 *)

Section def_polarity.
  Context {M : unital_premagmoid_data}.
  Hypothesis hs : has_homsets M.

  (** *** 1. Definitions of linearity, thunkability and polarization *)

  Definition is_linear {a b : M} (f : a --> b) : UU
    := ∏ (c d : M) (g : c --> a) (h : d --> c),
      (h · g) · f = h · (g · f).
  Definition is_thunkable {a b : M} (f : b --> a) : UU
    := ∏ (c d : M) (g : a --> c) (h : c --> d),
      f · (g · h) = (f · g) · h.

  Lemma isaprop_is_linear' {a b : M} (f : a --> b) : isaprop (is_linear f).
  Proof. do 4 (apply impred; intro); apply hs. Qed.
  Lemma isaprop_is_thunkable' {a b : M} (f : a --> b) : isaprop (is_thunkable f).
  Proof. do 4 (apply impred; intro); apply hs. Qed.

  Definition is_positive (a : M) : UU
    := ∏ (b : M) (f : a --> b), is_linear f.
  Definition is_negative (a : M) : UU
    := ∏ (b : M) (f : b --> a), is_thunkable f.

  Lemma isaprop_is_positive' (a : M) : isaprop (is_positive a).
  Proof. do 2 (apply impred; intro); apply isaprop_is_linear'. Qed.
  Lemma isaprop_is_negative' (a : M) : isaprop (is_negative a).
  Proof. do 2 (apply impred; intro); apply isaprop_is_thunkable'. Qed.

  Definition is_linear_and_thunkable {a b : M} (f : a --> b) : UU
    := is_linear f × is_thunkable f.
  Definition make_is_linear_and_thunkable {a b : M} {f : a --> b}
    (H1 : is_linear f) (H2 : is_thunkable f) := H1,,H2.

  Coercion is_linear_and_thunkable_to_is_linear {a b : M} (f : a --> b)
    (H : is_linear_and_thunkable f) : is_linear f := pr1 H.
  Coercion is_linear_and_thunkable_to_is_thunkable {a b : M} (f : a --> b)
    (H : is_linear_and_thunkable f) : is_thunkable f := pr2 H.

  Lemma isaprop_is_linear_and_thunkable' {a b : M} (f : a --> b)
    : isaprop (is_linear_and_thunkable f).
  Proof.
    apply isapropdirprod.
    - apply isaprop_is_linear'.
    - apply isaprop_is_thunkable'.
  Qed.

End def_polarity.

(** *** 2. Lemmas for working with linearity, thunkability and polarization *)

Section lemma_polarity.
  Context {M : unital_premagmoid_data}.

  Definition is_linear_of_positive {a b : M} (f : a --> b)
    : is_positive a -> is_linear f := λ H, H _ f.
  Definition is_thunkable_of_negative {a b : M} (f : b --> a)
    : is_negative a -> is_thunkable f := λ H, H _ f.

  (** Lemmas for reassociating composition. *)

  Lemma assoc_linear {a b c d : M} (f : a --> b) (H : is_linear f)
    (g : c --> a) (h : d --> c) : h · (g · f) = (h · g) · f.
  Proof. apply pathsinv0, H. Defined.
  Lemma assoc'_linear {a b c d : M} (f : a --> b) (H : is_linear f)
    (g : c --> a) (h : d --> c) : (h · g) · f = h · (g · f).
  Proof. apply H. Defined.

  Lemma assoc_thunkable {a b c d : M} (f : b --> a) (H : is_thunkable f)
    (g : a --> c) (h : c --> d)
    : f · (g · h) = (f · g) · h.
  Proof. apply H. Defined.
  Lemma assoc'_thunkable {a b c d : M} (f : b --> a) (H : is_thunkable f)
    (g : a --> c) (h : c --> d) : (f · g) · h = f · (g · h).
  Proof. apply pathsinv0, H. Defined.

  Lemma assoc_positive {a b d : M} (c : M) (H : is_positive c)
    (f : a --> b) (g : b --> c) (h : c --> d)
    : f · (g · h) = (f · g) · h.
  Proof. apply assoc_linear, is_linear_of_positive, H. Defined.
  Lemma assoc'_positive {a b d : M} (c : M) (H : is_positive c)
    (f : a --> b) (g : b --> c) (h : c --> d)
    : (f · g) · h = f · (g · h).
  Proof. apply assoc'_linear, is_linear_of_positive, H. Defined.

  Lemma assoc_negative {a c d : M} (b : M) (H : is_negative b)
    (f : a --> b) (g : b --> c) (h : c --> d)
    : f · (g · h) = (f · g) · h.
  Proof. apply assoc_thunkable, is_thunkable_of_negative, H. Defined.
  Lemma assoc'_negative {a c d : M} (b : M) (H : is_negative b)
    (f : a --> b) (g : b --> c) (h : c --> d)
    : (f · g) · h = f · (g · h).
  Proof. apply assoc'_thunkable, is_thunkable_of_negative, H. Defined.

  (* Linearity and thunkability are preserved under composition. *)
  Lemma is_linear_compose {a b c : M} (f : a --> b) (g : b --> c)
    : is_linear f -> is_linear g -> is_linear (f · g).
  Proof. intros Hf Hg d e h k. now rewrite <- Hg, <- Hg, Hf, Hg. Qed.
  Lemma is_thunkable_compose {a b c : M} (f : a --> b) (g : b --> c)
    : is_thunkable f -> is_thunkable g -> is_thunkable (f · g).
  Proof. intros Hf Hg d e h k. now rewrite <- Hf, <- Hf, Hg, Hf. Qed.
  Lemma is_linear_and_thunkable_compose {a b c : M} (f : a --> b) (g : b --> c)
    : is_linear_and_thunkable f -> is_linear_and_thunkable g -> is_linear_and_thunkable (f · g).
  Proof.
    intros Hf Hg.
    apply make_is_linear_and_thunkable.
    - apply (is_linear_compose _ _ Hf Hg).
    - apply (is_thunkable_compose _ _ Hf Hg).
  Qed.

End lemma_polarity.

Section lemma_polarity.
  Context {M : unital_premagmoid}.

  (* Identities are linear and thunkable. *)
  Lemma is_linear_identity (a : M) : is_linear (identity a).
  Proof. intros b c g h. now do 2 rewrite magmoid_id_right. Defined.
  Lemma is_thunkable_identity (a : M) : is_thunkable (identity a).
  Proof. intros b c g h. now do 2 rewrite magmoid_id_left. Defined.
  Lemma is_linear_and_thunkable_identity (a : M) : is_linear_and_thunkable (identity a).
  Proof.
    apply make_is_linear_and_thunkable.
    - apply is_linear_identity.
    - apply is_thunkable_identity.
  Defined.

End lemma_polarity.

(** *** 3. Bundled linear/thunkable morphisms and polarized objects *)

Section polarized_subtypes.
  Context {M : unital_magmoid}.
  Let hs : has_homsets M := unital_magmoid_has_homsets M.

  (* Linear morphisms *)
  Definition isaprop_is_linear {a b : M} (f : a --> b) : isaprop (is_linear f).
  Proof. apply isaprop_is_linear', hs. Defined.
  Definition ish_linear {a b : M} (f : a --> b) : hProp
    := make_hProp (is_linear f) (isaprop_is_linear f).

  Definition linear_mor (a b : M) := ∑ (f : a --> b), ish_linear f.
  Definition make_linear_mor {a b : M} (f : a --> b) (H : is_linear f) : linear_mor a b := f,,H.
  Coercion linear_mor_to_mor {a b : M} (f : linear_mor a b) : a --> b := pr1 f.
  Coercion linear_mor_is_linear {a b : M} (f : linear_mor a b) : is_linear f := pr2 f.
  Definition isaset_linear_mor {a b : M} : isaset (linear_mor a b).
  Proof.
    apply isaset_total2.
    - apply hs.
    - intro x. apply isasetaprop, propproperty.
  Qed.
  Definition linear_identity (a : M)
    : linear_mor a a := make_linear_mor (identity a) (is_linear_identity a).
  Definition linear_compose {a b c : M} (f : linear_mor a b) (g : linear_mor b c)
    : linear_mor a c := make_linear_mor (f · g) (is_linear_compose f g f g).

  (* Thunkable morphisms *)
  Definition isaprop_is_thunkable {a b : M} (f : a --> b) : isaprop (is_thunkable f).
  Proof. apply isaprop_is_thunkable', hs. Defined.
  Definition ish_thunkable {a b : M} (f : a --> b) : hProp
    := make_hProp (is_thunkable f) (isaprop_is_thunkable f).

  Definition thunkable_mor (a b : M) := ∑ (f : a --> b), ish_thunkable f.
  Definition make_thunkable_mor {a b : M} (f : a --> b) (H : is_thunkable f) : thunkable_mor a b := f,,H.
  Coercion thunkable_mor_to_mor {a b : M} (f : thunkable_mor a b) : a --> b := pr1 f.
  Coercion thunkable_mor_is_thunkable {a b : M} (f : thunkable_mor a b) : is_thunkable f := pr2 f.
  Definition isaset_thunkable_mor {a b : M} : isaset (thunkable_mor a b).
  Proof.
    apply isaset_total2.
    - apply hs.
    - intro x. apply isasetaprop, propproperty.
  Qed.
  Definition thunkable_identity (a : M)
    : thunkable_mor a a := make_thunkable_mor (identity a) (is_thunkable_identity a).
  Definition thunkable_compose {a b c : M} (f : thunkable_mor a b) (g : thunkable_mor b c)
    : thunkable_mor a c := make_thunkable_mor (f · g) (is_thunkable_compose f g f g).

  (* Linear and thunkable morphisms *)
  Definition isaprop_is_linear_and_thunkable {a b : M} (f : a --> b) : isaprop (is_linear_and_thunkable f).
  Proof. apply isaprop_is_linear_and_thunkable', hs. Defined.
  Definition ish_linear_and_thunkable {a b : M} (f : a --> b) : hProp
    := make_hProp (is_linear_and_thunkable f) (isaprop_is_linear_and_thunkable f).

  Definition linear_and_thunkable_mor (a b : M) := ∑ (f : a --> b), ish_linear_and_thunkable f.
  Definition make_linear_and_thunkable_mor {a b : M} (f : a --> b) (H : is_linear_and_thunkable f) := f,,H.
  Definition make_linear_and_thunkable_mor' {a b : M} (f : a --> b) (H1 : is_linear f) (H2 : is_thunkable f)
    : linear_and_thunkable_mor a b := make_linear_and_thunkable_mor f (make_is_linear_and_thunkable H1 H2).
  Coercion linear_and_thunkable_mor_to_mor {a b : M} (f : linear_and_thunkable_mor a b) : a --> b := pr1 f.
  Coercion linear_and_thunkable_mor_is_linear_and_thunkable {a b : M} (f : linear_and_thunkable_mor a b)
    : is_linear_and_thunkable f := pr2 f.
  Coercion linear_and_thunkable_mor_to_linear_mor {a b : M} (f : linear_and_thunkable_mor a b)
    : linear_mor a b := make_linear_mor f f.
  Coercion linear_and_thunkable_mor_to_thunkable_mor {a b : M} (f : linear_and_thunkable_mor a b)
    : thunkable_mor a b := make_thunkable_mor f f.

  Definition linear_and_thunkable_identity (a : M) : linear_and_thunkable_mor a a
    := make_linear_and_thunkable_mor (identity a) (is_linear_and_thunkable_identity a).
  Definition linear_and_thunkable_compose {a b c : M}
    (f : linear_and_thunkable_mor a b) (g : linear_and_thunkable_mor b c)
    : linear_and_thunkable_mor a c
    := make_linear_and_thunkable_mor (f · g) (is_linear_and_thunkable_compose f g f g).

  Definition isaset_linear_and_thunkable_mor {a b : M} : isaset (linear_and_thunkable_mor a b).
  Proof.
    apply isaset_total2.
    - apply hs.
    - intro x. apply isasetaprop, propproperty.
  Qed.

  (* Positive objects *)
  Definition isaprop_is_positive (a : M) : isaprop (is_positive a).
  Proof. apply isaprop_is_positive', hs. Defined.
  Definition ish_positive (a : M) : hProp
    := make_hProp (is_positive a) (isaprop_is_positive a).

  Definition positive_ob : UU := ∑ (a : M), ish_positive a.
  Definition make_positive_ob (a : M) (H : is_positive a) : positive_ob := a,,H.
  Coercion positive_ob_to_ob (a : positive_ob) : M := pr1 a.
  Coercion positive_ob_is_positive (a : positive_ob) : is_positive a := pr2 a.

  (* Negative objects *)
  Definition isaprop_is_negative (a : M) : isaprop (is_negative a).
  Proof. apply isaprop_is_negative', hs. Defined.
  Definition ish_negative (a : M) : hProp
    := make_hProp (is_negative a) (isaprop_is_negative a).

  Definition negative_ob : UU := ∑ (a : M), ish_negative a.
  Definition make_negative_ob (a : M) (H : is_negative a) : negative_ob := a,,H.
  Coercion negative_ob_to_ob (a : negative_ob) : M := pr1 a.
  Coercion negative_ob_is_negative (a : negative_ob) : is_negative a := pr2 a.

End polarized_subtypes.
Arguments positive_ob _ : clear implicits.
Arguments negative_ob _ : clear implicits.

(** ** 4. Inverses and when they are unique *)
Section inverses.
  Context {M : unital_magmoid} {a b : M} (f : a --> b).

  Lemma isaprop_is_inverse_in_precat_of_magmoid (g : a <-- b) : isaprop (is_inverse_in_precat f g).
  Proof. apply isapropdirprod; apply unital_magmoid_has_homsets. Qed.

  (* Linear inverses are unique *)
  Lemma inverse_unique_linear
    (g g' : a <-- b) (H : is_linear g)
    (Hg : is_inverse_in_precat f g)
    (Hg' : is_inverse_in_precat f g')
    : g = g'.
  Proof.
    refine (!magmoid_id_left _ @ _ @ magmoid_id_right _).
    now rewrite <- (is_inverse_in_precat1 Hg),
      <- (is_inverse_in_precat2 Hg'), (assoc_linear _ H).
  Qed.

  Definition has_linear_inverse : UU
    := ∑ (g : linear_mor b a), is_inverse_in_precat f g.
  Definition make_has_linear_inverse
    (g : linear_mor b a) (H : is_inverse_in_precat f g)
    : has_linear_inverse := g,,H.
  Coercion has_linear_inverse_to_mor (I : has_linear_inverse) : linear_mor b a := pr1 I.
  Coercion has_linear_inverse_is_inverse (I : has_linear_inverse) : is_inverse_in_precat f I := pr2 I.

  Lemma isaprop_has_linear_inverse : isaprop has_linear_inverse.
  Proof.
    apply invproofirrelevance; intros g g'.
    apply subtypePath'.
    2: apply isaprop_is_inverse_in_precat_of_magmoid.
    apply carrier_eq, inverse_unique_linear.
    - apply (has_linear_inverse_to_mor g).
    - apply g.
    - apply g'.
  Qed.

  (* Thunkable inverses are unique *)
  Lemma inverse_unique_thunkable
    (g g' : a <-- b) (H : is_thunkable g)
    (Hg : is_inverse_in_precat f g)
    (Hg' : is_inverse_in_precat f g')
    : g = g'.
  Proof.
    refine (!magmoid_id_right _ @ _ @ magmoid_id_left _).
    now rewrite <- (is_inverse_in_precat2 Hg),
      <- (is_inverse_in_precat1 Hg'), (assoc_thunkable _ H).
  Qed.

  Definition has_thunkable_inverse : UU
    := ∑ (g : thunkable_mor b a), is_inverse_in_precat f g.
  Definition make_has_thunkable_inverse
    (g : thunkable_mor b a) (H : is_inverse_in_precat f g)
    : has_thunkable_inverse := g,,H.
  Coercion has_thunkable_inverse_to_mor (I : has_thunkable_inverse) : thunkable_mor b a := pr1 I.
  Coercion has_thunkable_inverse_is_inverse (I : has_thunkable_inverse) : is_inverse_in_precat f I := pr2 I.

  Lemma isaprop_has_thunkable_inverse : isaprop has_thunkable_inverse.
  Proof.
    apply invproofirrelevance; intros g g'.
    apply subtypePath'.
    2: apply isaprop_is_inverse_in_precat_of_magmoid.
    apply carrier_eq, inverse_unique_thunkable.
    - apply (has_thunkable_inverse_to_mor g).
    - apply g.
    - apply g'.
  Qed.

End inverses.

(** ** 5. Epics and monics in magmoids *)
Section def_epi_monic.
  Context {M : unital_premagmoid_data}.
  Hypothesis hs : has_homsets M.

  (** Definition and construction of is_epi. *)
  Definition is_epi {x y : M} (f : x --> y) : UU :=
    ∏ (z : M) (g h : y --> z), f · g = f · h -> g = h.

  Definition make_is_epi {x y : M} (f : x --> y)
    (H : ∏ (z : M) (g h : y --> z), f · g = f · h -> g = h) : is_epi f := H.

  Lemma isaprop_is_epi {y z : M} (f : y --> z) : isaprop (is_epi f).
  Proof. do 4 (apply impred; intro); apply hs. Qed.

  (** Definition and construction of epi. *)
  Definition epi (x y : M) : UU := ∑ f : x --> y, is_epi f.
  Definition make_epi {x y : M} (f : x --> y) (H : is_epi f) :
    epi x y := f,,H.

  (** Gets the arrow out of epi. *)
  Coercion epi_to_arrow {x y : M} (E : epi x y) : M⟦x, y⟧ := pr1 E.
  Definition epi_is_epi {x y : M} (E : epi x y) : is_epi E := pr2 E.

  (** Definition and construction of is_monic. *)
  Definition is_monic {x y : M} (f : x <-- y) : UU :=
    ∏ (z : M) (g h : y <-- z), g · f = h · f -> g = h.

  Definition make_is_monic {x y : M} (f : x <-- y)
    (H : ∏ (z : M) (g h : y <-- z), g · f = h · f -> g = h) : is_monic f := H.

  Lemma isaprop_is_monic {y z : M} (f : y --> z) : isaprop (is_monic f).
  Proof. do 4 (apply impred; intro); apply hs. Qed.

  (** Definition and construction of monic. *)
  Definition monic (x y : M) : UU := ∑ f : x --> y, is_monic f.
  Definition make_monic {x y : M} (f : x --> y) (H : is_monic f) :
    monic x y := f,,H.

  (** Gets the arrow out of monic. *)
  Coercion monic_to_arrow {x y : M} (E : monic x y) : M⟦x, y⟧ := pr1 E.
  Definition monic_is_monic {x y : M} (E : monic x y) : is_monic E := pr2 E.
End def_epi_monic.

Section lemma_epi_monic.
  Context {M : unital_premagmoid}.
  Hypothesis hs : has_homsets M.

  Lemma is_epi_identity (x : M) : is_epi (identity x).
  Proof.
    intros b g h H.
    exact (!magmoid_id_left g @ H @ magmoid_id_left h).
  Defined.

  Lemma is_monic_identity (x : M) : is_monic (identity x).
  Proof.
    intros b g h H.
    exact (!magmoid_id_right g @ H @ magmoid_id_right h).
  Defined.

  Lemma is_epi_compose {x y z : M} (f : x --> y) (g : y --> z)
    (Hf : is_epi f) (Hg : is_epi g) (Hf' : is_thunkable f)
    : is_epi (f · g).
  Proof.
    intros a h k H.
    apply Hg, Hf.
    refine (_ @ H @ _).
    - apply (assoc_thunkable _ Hf').
    - apply (assoc'_thunkable _ Hf').
  Defined.

  Lemma is_monic_compose {x y z : M} (f : x --> y) (g : y --> z)
    (Hf : is_monic f) (Hg : is_monic g) (Hg' : is_linear g)
    : is_monic (f · g).
  Proof.
    intros a h k H.
    apply Hf, Hg.
    refine (_ @ H @ _).
    - apply (assoc'_linear _ Hg').
    - apply (assoc_linear _ Hg').
  Defined.

End lemma_epi_monic.

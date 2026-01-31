(********************************************************************************

 Unital (Pre)magmoids

 Author: B. Szilvasy
 January 2026

 A unital (pre)magmoid is a (pre)category without associativity.  It may also be
 called a "nonassociative category" as an allusion to this.  Another name is a
 "deductive system" as an allusion to its role in categorical semantics for
 nonassociative logic.

 This file defines unital magmoids, and provides definitions and lemmas for the
 important special cases when unital magmoids do associate.

 Contents:
 1. Unbundled definitions of unitality and associativity
 2. Definition of a unital (pre)magmoid
 3. Definitions of linearity, thunkability and polarization
 4. Lemmas for working with linearity, thunkability and polarization
 5. Bundled linear/thunkable morphisms and polarized objects

 ** Linearity, thunkability and polarization

 Linearity, thunkability, and polarization are those properties of morphisms or
 objects that provide associatitivy of composition around them, in the following
 ways (described in diagram order):

 1. A *linear* morphism associates when it is on the *right*.
 2. A *thunkable* morphism associates when it is on the *left*.
 3. A *positive* object is one where all *outgoing* morphisms are *linear*.
 4. A *negative* object is one where all *incoming* morphisms are *thunkable*.

 In pictorial form, given objects and morphisms as follows, composition
 associates if any one of the annotations holds:

 <<
                       thunkable ↓           ↓ linear
                                 f     g     h
                              A --> B --> C --> D
                           negative ↑     ↑ positive
 >>

 When any of those named properties can be proven, the lemmas named below can be
 used to reassociate, replacing the [*] with the property:

 - [assoc_*]  : f · (g · h) = (f · g) · h     ("to the left")
 - [assoc'_*] : (f · g) · h) = f · (g · h)    ("to the right")

 Identities are both linear and thunkable, and composition preserves linearity.
 Indeed, a unital magmoid's submagmoid of linear morphisms is a category, and
 likewise for thunkable morphisms, but those definitions and more are in
 [Subcategories.v].

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Local Open Scope cat.

Declare Scope unital_magmoid.
Delimit Scope unital_magmoid with unital_magmoid.
Local Open Scope unital_magmoid.

Section magmoid_defs.
  (** ** 1. Unbundled definitions of unitality and associativity *)

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

  (** ** 2. Definition of a unital (pre)magmoid *)

  (** *** 1. Unital premagmoid *)
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

  (** *** 2. Unital magmoid *)
  Definition unital_magmoid : UU
    := ∑ (M : unital_premagmoid), has_homsets M.
  Definition make_unital_magmoid
    (M : unital_premagmoid)
    (H : has_homsets M)
    : unital_magmoid
    := M,,H.
  Coercion unital_magmoid_to_unital_premagmoid (M : unital_magmoid) : unital_premagmoid := pr1 M.
  Definition unital_magmoid_has_homsets (M : unital_magmoid) : has_homsets M := pr2 M.

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

  Definition um_homset {M : unital_magmoid} (a b : M) : hSet
    := make_hSet (M⟦a, b⟧) (unital_magmoid_has_homsets M a b).

End magmoid_defs.

(** ** 3. Definition of linearity, thunkability, and polarization *)

Section polarity_defs.

  Context {M : unital_premagmoid_data}.
  Hypothesis hs : has_homsets M.

  (** Linear and thunkable *)

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

  (** Positive and negative *)

  Definition is_positive (a : M) : UU
    := ∏ (b : M) (f : a --> b), is_linear f.
  Definition is_negative (a : M) : UU
    := ∏ (b : M) (f : b --> a), is_thunkable f.

  Lemma isaprop_is_positive' (a : M) : isaprop (is_positive a).
  Proof. do 2 (apply impred; intro); apply isaprop_is_linear'. Qed.
  Lemma isaprop_is_negative' (a : M) : isaprop (is_negative a).
  Proof. do 2 (apply impred; intro); apply isaprop_is_thunkable'. Qed.

  (** Linear-and-thunkable *)

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

End polarity_defs.

(** ** 4. Lemmas for working with linearity, thunkability and polarization *)

Section polarity_lemmas.
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

  (** Linearity and thunkability are preserved under composition. *)
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

End polarity_lemmas.

Section polarity_lemmas.
  Context {M : unital_premagmoid}.

  (** Identities are linear and thunkable. *)
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

  (** Characterisations of [is_assoc_premagmoid] in a unital magmoid *)
  Lemma any_is_linear_iff_assoc
    : (∏ (a b : M) (f : a --> b), is_linear f) <-> is_assoc_premagmoid M.
  Proof.
    split; intro H.
    - apply make_is_one_assoc_premagmoid; intros.
      apply assoc_linear, H.
    - intros a b f c d g h. apply H.
  Defined.

  Lemma any_is_thunkable_iff_assoc
    : (∏ (a b : M) (f : a <-- b), is_thunkable f) <-> is_assoc_premagmoid M.
  Proof.
    split; intro H.
    - apply make_is_one_assoc_premagmoid; intros.
      apply assoc_thunkable, H.
    - intros a b f c d g h. apply H.
  Defined.

  Lemma any_is_positive_iff_assoc
    : (∏ (a : M), is_positive a) <-> is_assoc_premagmoid M.
  Proof.
    eapply logeq_trans; [|apply any_is_linear_iff_assoc].
    split; intro H; intros.
    - apply is_linear_of_positive, H.
    - intros b f.
      apply H.
  Defined.

  Lemma any_is_negative_iff_assoc
    : (∏ (a : M), is_negative a) <-> is_assoc_premagmoid M.
  Proof.
    eapply logeq_trans; [|apply any_is_thunkable_iff_assoc].
    split; intro H; intros.
    - apply is_thunkable_of_negative, H.
    - intros b f.
      apply H.
  Defined.

End polarity_lemmas.

(** ** 5. Bundled linear/thunkable morphisms and polarized objects *)

Section polarized_subtypes.
  Context {M : unital_magmoid}.
  Let hs : has_homsets M := unital_magmoid_has_homsets M.

  (** Linear morphisms *)
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

  (** Thunkable morphisms *)
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

  (** Linear and thunkable morphisms *)
  Definition isaprop_is_linear_and_thunkable {a b : M} (f : a --> b) : isaprop (is_linear_and_thunkable f).
  Proof. apply isaprop_is_linear_and_thunkable', hs. Defined.
  Definition ish_linear_and_thunkable {a b : M} (f : a --> b) : hProp
    := make_hProp (is_linear_and_thunkable f) (isaprop_is_linear_and_thunkable f).

  Definition linear_and_thunkable_mor (a b : M) := ∑ (f : a --> b), ish_linear_and_thunkable f.
  Definition make_linear_and_thunkable_mor {a b : M} (f : a --> b) (H : is_linear_and_thunkable f)
    : linear_and_thunkable_mor a b := f,,H.
  Definition make_linear_and_thunkable_mor' {a b : M} (f : a --> b) (H1 : is_linear f) (H2 : is_thunkable f)
    : linear_and_thunkable_mor a b := make_linear_and_thunkable_mor f (make_is_linear_and_thunkable H1 H2).
  Coercion linear_and_thunkable_mor_to_mor {a b : M} (f : linear_and_thunkable_mor a b) : a --> b := pr1 f.
  Coercion linear_and_thunkable_mor_is_linear_and_thunkable {a b : M} (f : linear_and_thunkable_mor a b)
    : is_linear_and_thunkable f := pr2 f.
  Coercion linear_and_thunkable_mor_to_linear_mor {a b : M} (f : linear_and_thunkable_mor a b)
    : linear_mor a b := make_linear_mor f f.
  Coercion linear_and_thunkable_mor_to_thunkable_mor {a b : M} (f : linear_and_thunkable_mor a b)
    : thunkable_mor a b := make_thunkable_mor f f.

  Definition make_linear_and_thunkable_mor_from_thunkable {a b : M} (f : thunkable_mor a b)
    (H : is_linear f) : linear_and_thunkable_mor a b.
  Proof.
    use (make_linear_and_thunkable_mor f).
    set (H' := f : is_thunkable f).
    apply make_is_linear_and_thunkable; assumption.
  Defined.

  Definition make_linear_and_thunkable_mor_from_linear {a b : M} (f : linear_mor a b)
    (H : is_thunkable f) : linear_and_thunkable_mor a b.
  Proof.
    use (make_linear_and_thunkable_mor f).
    set (H' := f : is_linear f).
    apply make_is_linear_and_thunkable; assumption.
  Defined.

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

  (** Positive objects *)
  Definition isaprop_is_positive (a : M) : isaprop (is_positive a).
  Proof. apply isaprop_is_positive', hs. Defined.
  Definition ish_positive (a : M) : hProp
    := make_hProp (is_positive a) (isaprop_is_positive a).

  Definition positive_ob : UU := ∑ (a : M), ish_positive a.
  Definition make_positive_ob (a : M) (H : is_positive a) : positive_ob := a,,H.
  Coercion positive_ob_to_ob (a : positive_ob) : M := pr1 a.
  Coercion positive_ob_is_positive (a : positive_ob) : is_positive a := pr2 a.

  (** Negative objects *)
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

(********************************************************************************

 The subcategories of unital magmoids.

 There are several subcategories of a given unital magmoid M:

 - [linear_category M] written M ₗ has all objects and linear morphisms.
 - [thunkable_category M] written M ₜ has all objects and thunkable morphisms.
 - [linear_and_thunkable_category M] written M ₗₜ has all objects and linear-and-thunkable morphisms.

 - [negative_category] written M⁻ has negative objects and thunkable morphisms.
 - [positive_category] written M⁺ has positive objects and linear morphisms.

 - [negative_linear_category] written M⁻ₗ has negative objects and linear-and-thunkable morphisms.
 - [positive_thunkable_category] written M⁺ₜ has positive objects and linear-and-thunkable morphisms.

 Contents:
 1. Definitions of unital magmoid subcategories
 2. Inclusion functors
 3. Definition of the shift functors of a duploid
 4. Adjunctions of the shift functors of a duploid

 Author: B. Szilvasy
 January 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

Require Import UniMath.CategoryTheory.Duploids.Magmoids.
Require Import UniMath.CategoryTheory.Duploids.Duploids.

Local Open Scope duploid.
Local Open Scope cat.

(** ** 1. Definitions of unital magmoid subcategories *)
Section polarized_categories.
  Context (M : unital_magmoid).

  (** The category of all objects and linear maps. *)
  Definition linear_category : category.
  Proof.
    use makecategory.
    - exact (ob M).
    - exact linear_mor.
    - apply @isaset_linear_mor.
    - apply linear_identity.
    - apply @linear_compose.
    - intros a b f; apply carrier_eq, magmoid_id_left.
    - intros a b f; apply carrier_eq, magmoid_id_right.
    - intros a b c d f g h; apply carrier_eq, assoc_linear, h.
    - intros a b c d f g h; apply carrier_eq, assoc'_linear, h.
  Defined.

  (** The category of all objects and thunkable maps. *)
  Definition thunkable_category : category.
  Proof.
    use makecategory.
    - exact (ob M).
    - exact thunkable_mor.
    - apply @isaset_thunkable_mor.
    - apply thunkable_identity.
    - apply @thunkable_compose.
    - intros a b f; apply carrier_eq, magmoid_id_left.
    - intros a b f; apply carrier_eq, magmoid_id_right.
    - intros a b c d f g h; apply carrier_eq, assoc_thunkable, f.
    - intros a b c d f g h; apply carrier_eq, assoc'_thunkable, f.
  Defined.

  Definition linear_and_thunkable_category : category.
  Proof.
    use makecategory.
    - exact (ob M).
    - exact linear_and_thunkable_mor.
    - apply @isaset_linear_and_thunkable_mor.
    - apply linear_and_thunkable_identity.
    - apply @linear_and_thunkable_compose.
    - intros a b f; apply carrier_eq, magmoid_id_left.
    - intros a b f; apply carrier_eq, magmoid_id_right.
    - intros a b c d f g h; apply carrier_eq, assoc_linear, h.
    - intros a b c d f g h; apply carrier_eq, assoc'_thunkable, f.
  Defined.

  (** The category of positive objects and linear maps. *)
  Definition positive_category : category
    := full_sub_category linear_category (λ a, ish_positive a).
  (** The category of positive objects and thunkable maps. *)
  Definition positive_thunkable_category : category
    := full_sub_category thunkable_category (λ a, ish_positive a).
  (** The category of negative objects and thunkable maps. *)
  Definition negative_category : category
    := full_sub_category thunkable_category (λ a, ish_negative a).
  (** The category of negative objects and linear maps. *)
  Definition negative_linear_category : category
    := full_sub_category linear_category (λ a, ish_negative a).
End polarized_categories.

Notation "M 'ₗ'" := (linear_category M) (at level 10) : duploid.
  (* type in Emacs using agda-input with \_l *)
Notation "M 'ₜ'" := (thunkable_category M) (at level 10) : duploid.
  (* type in Emacs using agda-input with \_t *)
Notation "M 'ₗₜ'" := (linear_and_thunkable_category M) (at level 10) : duploid.
  (* type in Emacs using agda-input with \_l \_t *)
Notation "M '⁺'" := (positive_category M) (at level 10) : duploid.
  (* type in Emacs using agda-input with \^+ *)
Notation "M '⁻'" := (negative_category M) (at level 10) : duploid.
  (* type in Emacs using agda-input with \^- *)
Notation "M '⁺ₜ'" := (positive_thunkable_category M) (at level 10) : duploid.
  (* type in Emacs using agda-input with \^+ \_t *)
Notation "M '⁻ₗ'" := (negative_linear_category M) (at level 10) : duploid.
(* type in Emacs using agda-input with \^- \_l *)

(** ** 2. Inclusion functors

  The inclusion functors between the categories of a unital magmoid M
  are depicted in the commutative diagram below. Of these, all but
  the four vertically drawn functors are fully faithful.

                      M⁺  ⟶ Mₗ    ↰
                      ↑     ↑
                      M⁺ₜ → Mₗₜ  ← M⁻ₗ
                            ↓     ↓
                      ↳     Mₜ  ← M⁻

  All categories also have inclusion functors into M itself.

 *)
Section inclusion_functors.
  Context (M : unital_magmoid).

  (* The easy fully-faithful inclusion functors for the above. *)

  Definition positive_category_to_linear_category : M⁺ ⟶ M ₗ
    := sub_precategory_inclusion _ _.
  Definition positive_thunkable_category_to_thunkable_category : M⁺ₜ ⟶ M ₜ
    := sub_precategory_inclusion _ _.
  Definition negative_category_to_thunkable_category : M⁻ ⟶ M ₜ
    := sub_precategory_inclusion _ _.
  Definition negative_linear_category_to_linear_category : M⁻ₗ ⟶ M ₗ
    := sub_precategory_inclusion _ _.

  Lemma fully_faithful_positive_category_to_linear_category
    : fully_faithful positive_category_to_linear_category.
  Proof. apply fully_faithful_sub_precategory_inclusion. Defined.
  Lemma fully_faithful_positive_thunkable_category_to_thunkable_category
    : fully_faithful positive_thunkable_category_to_thunkable_category.
  Proof. apply fully_faithful_sub_precategory_inclusion. Defined.
  Lemma fully_faithful_negative_category_to_thunkable_category
    : fully_faithful negative_category_to_thunkable_category.
  Proof. apply fully_faithful_sub_precategory_inclusion. Defined.
  Lemma fully_faithful_negative_linear_category_to_linear_category
    : fully_faithful negative_linear_category_to_linear_category.
  Proof. apply fully_faithful_sub_precategory_inclusion. Defined.

  (* M⁺ₜ into M ₗₜ *)
  Definition positive_thunkable_mor_to_linear_and_thunkable_mor {a b : positive_ob M}
    (f : thunkable_mor a b) : linear_and_thunkable_mor a b
    := (make_linear_and_thunkable_mor' f (is_linear_of_positive _ a) f).
  Definition positive_thunkable_mor_of_linear_and_thunkable_mor {a b : positive_ob M}
    (f : linear_and_thunkable_mor a b) : thunkable_mor a b := f.

  Definition positive_thunkable_category_to_linear_and_thunkable_category : M⁺ₜ ⟶ M ₗₜ.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro a; apply a.
      + intros a b f. apply positive_thunkable_mor_to_linear_and_thunkable_mor, f.
    - abstract (use make_is_functor;
                [ intro a; now apply carrier_eq
                | intros a b c f g; now apply carrier_eq ]).
  Defined.

  Lemma fully_faithful_positive_thunkable_category_to_linear_and_thunkable_category
    : fully_faithful positive_thunkable_category_to_linear_and_thunkable_category.
  Proof.
    intros a b.
    use isweq_iso.
    - intro f.
      refine (_,,tt).
      apply positive_thunkable_mor_of_linear_and_thunkable_mor, f.
    - intro f. now apply carrier_eq.
    - intro f. now apply carrier_eq.
  Defined.

  (* M⁻ₗ into M ₗₜ *)
  Definition negative_linear_mor_to_linear_and_thunkable_mor {a b : negative_ob M}
    (f : linear_mor a b) : linear_and_thunkable_mor a b
    := (make_linear_and_thunkable_mor' f f (is_thunkable_of_negative _ b)).
  Definition negative_linear_mor_of_linear_and_thunkable_mor {a b : negative_ob M}
    (f : linear_and_thunkable_mor a b) : linear_mor a b := f.

  Definition negative_linear_category_to_linear_and_thunkable_category : M⁻ₗ ⟶ M ₗₜ.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro a; apply a.
      + intros a b f. apply negative_linear_mor_to_linear_and_thunkable_mor, f.
    - abstract (use make_is_functor;
                [ intro a; now apply carrier_eq
                | intros a b c f g; now apply carrier_eq ]).
   Defined.

  Lemma fully_faithful_negative_linear_category_to_linear_and_thunkable_category
    : fully_faithful negative_linear_category_to_linear_and_thunkable_category.
  Proof.
    intros a b.
    use isweq_iso.
    - intro f.
      refine (_,,tt).
      apply negative_linear_mor_of_linear_and_thunkable_mor, f.
    - intro f. now apply carrier_eq.
    - intro f. now apply carrier_eq.
  Defined.

  (* M ₗₜ into M ₗ *)
  Definition linear_and_thunkable_category_to_linear_category : M ₗₜ ⟶ M ₗ.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro a. apply a.
      + intros a b f. apply ((f : linear_and_thunkable_mor a b) : linear_mor a b).
    - abstract (use make_is_functor;
                [ intro a; apply idpath
                | intros a b c f g; now apply carrier_eq ]).
  Defined.

  Lemma faithful_linear_and_thunkable_category_to_linear_category
    : faithful linear_and_thunkable_category_to_linear_category.
  Proof.
    intros a b.
    apply isinclbetweensets.
    1, 2: apply homset_property.
    intros f f' p. apply carrier_eq, (base_paths _ _ p).
  Defined.

  (* M ₗₜ into M ₜ *)
  Definition linear_and_thunkable_category_to_thunkable_category : M ₗₜ ⟶ M ₜ.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro a. apply a.
      + intros a b f. apply ((f : linear_and_thunkable_mor a b) : thunkable_mor a b).
    - abstract (use make_is_functor;
                [ intro a; apply idpath
                | intros a b c f g; now apply carrier_eq ]).
  Defined.

  Lemma faithful_linear_and_thunkable_category_to_thunkable_category
    : faithful linear_and_thunkable_category_to_thunkable_category.
  Proof.
    intros a b.
    apply isinclbetweensets.
    1, 2: apply homset_property.
    intros f f' p.
    apply carrier_eq, (base_paths _ _ p).
  Defined.

  (* M⁺ₜ into M⁺ *)
  Definition positive_thunkable_category_to_positive_category : M⁺ₜ ⟶ M⁺.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro a; apply a.
      + intros a b f.
        simple refine ((make_linear_mor _ _),,tt).
        * apply f.
        * apply is_linear_of_positive, a.
    - abstract (use make_is_functor;
                [ intro a; now do 2 apply carrier_eq
                | intros a b c f g; now do 2 apply carrier_eq ]).
  Defined.

  Lemma faithful_positive_thunkable_category_to_positive_category
    : faithful positive_thunkable_category_to_positive_category.
  Proof.
    intros a b.
    apply isinclbetweensets.
    1, 2: apply homset_property.
    intros f f' p.
    do 2 apply carrier_eq.
    do 2 apply base_paths in p.
    exact p.
  Defined.

  (* M⁻ₗ into M⁻ *)
  Definition negative_linear_category_to_negative_category : M⁻ₗ ⟶ M⁻.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro a; apply a.
      + intros a b f.
        simple refine ((make_thunkable_mor _ _),,tt).
        * apply f.
        * apply is_thunkable_of_negative, b.
    - abstract (use make_is_functor;
                [ intro a; now do 2 apply carrier_eq
                | intros a b c f g; now do 2 apply carrier_eq ]).
  Defined.

  Lemma faithful_negative_linear_category_to_negative_category
    : faithful negative_linear_category_to_negative_category.
  Proof.
    intros a b.
    apply isinclbetweensets.
    1, 2: apply homset_property.
    intros f f' p.
    do 2 apply carrier_eq.
    do 2 apply base_paths in p.
    exact p.
  Defined.

  (* M⁺ₜ into M ₗ *)
  Definition positive_thunkable_category_to_linear_category : M⁺ₜ ⟶ M ₗ
    := positive_thunkable_category_to_linear_and_thunkable_category
         ∙ linear_and_thunkable_category_to_linear_category.
  Definition faithful_positive_thunkable_category_to_linear_category
    : faithful positive_thunkable_category_to_linear_category.
  Proof.
    apply comp_faithful_is_faithful.
    - apply fully_faithful_implies_full_and_faithful,
        fully_faithful_positive_thunkable_category_to_linear_and_thunkable_category.
    - apply faithful_linear_and_thunkable_category_to_linear_category.
  Defined.

  (* I : M⁺ₜ ⟶ M ₗ factors through M⁺ *)
  Lemma positive_thunkable_category_to_linear_category_through_positive
    : positive_thunkable_category_to_linear_category
      = (positive_thunkable_category_to_positive_category
           ∙ positive_category_to_linear_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

  (* M⁻ₗ into M ₜ *)
  Definition negative_linear_category_to_thunkable_category : M⁻ₗ ⟶ M ₜ
    := negative_linear_category_to_linear_and_thunkable_category
         ∙ linear_and_thunkable_category_to_thunkable_category.
  Definition faithful_negative_linear_category_to_thunkable_category
    : faithful negative_linear_category_to_thunkable_category.
  Proof.
    apply comp_faithful_is_faithful.
    - apply fully_faithful_implies_full_and_faithful,
        fully_faithful_negative_linear_category_to_linear_and_thunkable_category.
    - apply faithful_linear_and_thunkable_category_to_thunkable_category.
  Defined.

  (* I : M⁻ₗ ⟶ M ₜ factors through M⁻ *)
  Lemma negative_linear_category_to_thunkable_category_through_negative
    : negative_linear_category_to_thunkable_category
      = (negative_linear_category_to_negative_category
           ∙ negative_category_to_thunkable_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

  (* I : M⁻ₗ ⟶ M ₗ factors through M ₗₜ *)
  Lemma negative_linear_category_to_linear_category_through_thunkable
    : negative_linear_category_to_linear_category
      = (negative_linear_category_to_linear_and_thunkable_category
           ∙ linear_and_thunkable_category_to_linear_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

  (* I : M⁺ₜ ⟶ M ₜ factors through M ₜₗ *)
  Lemma positive_thunkable_category_to_thunkable_category_through_linear
    : positive_thunkable_category_to_thunkable_category
      = (positive_thunkable_category_to_linear_and_thunkable_category
           ∙ linear_and_thunkable_category_to_thunkable_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

  (* Inclusion functors into M. *)
  Definition linear_category_to_unital_magmoid : M ₗ ⟶ M.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro a; exact a.
      + intros a b f; apply f.
    - abstract (use make_is_functor; now intros).
  Defined.

  Lemma faithful_linear_category_to_unital_magmoid
    : faithful linear_category_to_unital_magmoid.
  Proof.
    intros a b.
    apply isinclbetweensets.
    - apply homset_property.
    - apply unital_magmoid_has_homsets.
    - intros f f' p. apply carrier_eq, p.
  Defined.

  Definition thunkable_category_to_unital_magmoid : M ₜ ⟶ M.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro a; exact a.
      + intros a b f; apply f.
    - abstract (use make_is_functor; now intros).
  Defined.

  Lemma faithful_thunkable_category_to_unital_magmoid
    : faithful thunkable_category_to_unital_magmoid.
  Proof.
    intros a b.
    apply isinclbetweensets.
    - apply homset_property.
    - apply unital_magmoid_has_homsets.
    - intros f f' p. apply carrier_eq, p.
  Defined.

End inclusion_functors.

(** ** 3. Definition of the shift functors of a duploid

 The shifts of a duploid D give rise to the following non-functorial maps on
 morphisms, defined just below.

 - #⇑ : D⟦a, b⟧ -> D ₜ⟦⇑a, ⇑b⟧
 - #⇓ : D⟦a, b⟧ -> D ₗ⟦⇓a, ⇓b⟧

 When extended and restricted along the relevant inclusion functors, we obtain
 the following two commutative diagrams of (almost) functors:

  D⁺ ↪ Dₗ  ↪  D
     ⇑ ↓      ↓ ⇑
       D⁺ₗ ↪  D⁻  ↪  Dₜ

  D⁻ ↪ Dₜ  ↪  D
     ⇓ ↓      ↓ ⇓
       D⁻ₜ ↪  D⁺  ↪  Dₗ

 Where all but the rightmost arrows are functorial.

 *)

Definition upshiftf {D : duploid} {a b : D} (f : a --> b) : ⇑a --> ⇑b := (force a · f) · delay b.
Definition downshiftf {D : duploid} {a b : D} (f : a --> b) : ⇓a --> ⇓b := unwrap a · (f · wrap b).

Notation "'#⇑' f" := (upshiftf f) (at level 40) : duploid.
  (* type in Emacs using agda-input with # \Uparrow *)
Notation "'#⇓' f" := (downshiftf f) (at level 40) : duploid.
  (* type in Emacs using agda-input with # \Downarrow *)

Section shift_functors.
  Context (D : duploid).

  (* Upshift functor *)
  Lemma upshiftf_id (a : D) : #⇑identity a = identity (⇑a).
  Proof.
    unfold upshiftf.
    now rewrite magmoid_id_right, force_delay_id.
  Qed.

  Lemma upshiftf_comp {a b c : D} (f : a --> b) (g : b --> c)
    (H : is_linear g) : #⇑(f · g) = (#⇑f) · (#⇑g).
  Proof.
    unfold upshiftf.
    rewrite (assoc_negative _ (⇑b)).
    do 2 rewrite (assoc_linear _ H).
    now rewrite delay_force_right.
  Qed.

  Lemma is_linear_upshiftf {a b : D} (f : a --> b) (H : is_linear f)
    : is_linear (#⇑f).
  Proof.
    apply is_linear_compose; try (apply is_linear_compose);
      (apply linear_mor_is_linear || apply H).
  Defined.

  (** ⇑ on objects gives a non-functorial map on objects and morphisms D ⟶ D⁻ *)
  Definition upshiftf' {a b : D} (f : D⟦a, b⟧) : thunkable_mor (⇑a) (⇑b)
    := make_thunkable_mor (#⇑f) (is_thunkable_of_negative _ (⇑_)).

  Definition upshift_'_to_negative : functor_data D (D⁻).
  Proof.
    use make_functor_data.
    - apply upshift.
    - intros a b f; apply (upshiftf' f,,tt).
  Defined.

  Definition upshift_data_linear_to_negative_linear : functor_data (D ₗ) (D⁻ₗ).
  Proof.
    use make_functor_data.
    - apply upshift_'_to_negative.
    - cbn; intros a b f.
      refine (_,,tt).
      use make_linear_mor.
      + apply (#upshift_'_to_negative f).
      + apply is_linear_upshiftf, f.
  Defined.

  Lemma upshift_is_functor_linear_to_negative_linear
    : is_functor upshift_data_linear_to_negative_linear.
  Proof.
    use make_is_functor.
    - intro a.
      do 2 apply carrier_eq.
      apply upshiftf_id.
    - intros a b c f g.
      do 2 apply carrier_eq.
      apply upshiftf_comp, linear_mor_is_linear.
  Qed.

  Definition upshift_linear_to_negative_linear : D ₗ ⟶ D⁻ₗ
    := make_functor _ upshift_is_functor_linear_to_negative_linear.
  Definition upshift_negative_linear_to_negative_linear : D⁻ₗ ⟶ D⁻ₗ
    := negative_linear_category_to_linear_category D ∙ upshift_linear_to_negative_linear.
  Definition upshift_linear_to_linear : D ₗ ⟶ D ₗ
    := upshift_linear_to_negative_linear ∙ negative_linear_category_to_linear_category D.
  Definition upshift_linear_to_thunkable : D ₗ ⟶ D ₜ
    := upshift_linear_to_negative_linear ∙ negative_linear_category_to_thunkable_category D.
  Definition upshift_linear_to_negative : D ₗ ⟶ D⁻
    := upshift_linear_to_negative_linear ∙ negative_linear_category_to_negative_category D.
  Definition upshift_positive_to_negative : D⁺ ⟶ D⁻
    := positive_category_to_linear_category D ∙ upshift_linear_to_negative.

  (** This non-functorial map is useful for defining the adjunctions below. *)
  Definition upshift_'_to_thunkable : functor_data D (D ₜ)
    := functor_composite_data upshift_'_to_negative
         (negative_category_to_thunkable_category D).

  (** Alternative characterisation of [upshift_linear_to_negative]
      factoring through D instead of D ₗ. *)
  Definition upshift_data_linear_to_negative' : functor_data (D ₗ) (D⁻)
    := functor_composite_data (linear_category_to_unital_magmoid D)
         upshift_'_to_negative.

  Lemma upshift_is_functor_linear_to_negative' : is_functor upshift_data_linear_to_negative'.
  Proof. apply (pr2 upshift_linear_to_negative). Defined.

  Definition upshift_linear_to_negative' : D ₗ ⟶ D⁻ :=
    make_functor _ upshift_is_functor_linear_to_negative'.

  (** [upshift_linear_to_negative] and [upshift_linear_to_negative'] are equal,
      definitionally. *)
  Lemma upshift_linear_to_negative_eq
    : upshift_linear_to_negative = upshift_linear_to_negative'.
  Proof. reflexivity. Defined.

  (* Downshift functor *)
  Lemma downshiftf_id (a : D) : #⇓identity a = identity (⇓a).
  Proof.
    unfold downshiftf.
    now rewrite magmoid_id_left, unwrap_wrap_id.
  Qed.

  Lemma downshiftf_comp {a b c : D} (f : a <-- b) (g : b <-- c)
    (H : is_thunkable g) : #⇓(f ∘ g) = (#⇓f) ∘ (#⇓g).
  Proof.
    unfold downshiftf.
    rewrite (assoc'_positive _ (⇓b)).
    do 2 rewrite (assoc'_thunkable _ H).
    now rewrite wrap_unwrap_left.
  Qed.

  Lemma is_thunkable_downshiftf {a b : D} (f : a <-- b) (H : is_thunkable f)
    : is_thunkable (#⇓f).
  Proof.
    apply is_thunkable_compose; try (apply is_thunkable_compose);
      (apply thunkable_mor_is_thunkable || apply H).
  Defined.

  (** ⇓ on objects gives a non-functorial map on objects and morphisms D ⟶ D⁺ *)
  Definition downshiftf' {a b : D} (f : D⟦a, b⟧) : linear_mor (⇓a) (⇓b)
    := make_linear_mor (#⇓f) (is_linear_of_positive _ (⇓_)).

  Definition downshift_'_to_positive : functor_data D (D⁺).
  Proof.
    use make_functor_data.
    - apply downshift.
    - intros a b f; apply (downshiftf' f,,tt).
  Defined.

  Definition downshift_data_thunkable_to_positive_thunkable : functor_data (D ₜ) (D⁺ₜ).
  Proof.
    use make_functor_data.
    - apply downshift_'_to_positive.
    - cbn; intros a b f.
      refine (_,,tt).
      use make_thunkable_mor.
      + apply (#downshift_'_to_positive f).
      + apply is_thunkable_downshiftf, f.
  Defined.

  Lemma downshift_is_functor_thunkable_to_positive_thunkable
    : is_functor downshift_data_thunkable_to_positive_thunkable.
  Proof.
    use make_is_functor.
    - intro a.
      do 2 apply carrier_eq.
      apply downshiftf_id.
    - intros a b c f g.
      do 2 apply carrier_eq.
      apply downshiftf_comp, thunkable_mor_is_thunkable.
  Qed.

  Definition downshift_thunkable_to_positive_thunkable : D ₜ ⟶ D⁺ₜ
    := make_functor _ downshift_is_functor_thunkable_to_positive_thunkable.
  Definition downshift_positive_thunkable_to_positive_thunkable : D⁺ₜ ⟶ D⁺ₜ
    := positive_thunkable_category_to_thunkable_category D ∙ downshift_thunkable_to_positive_thunkable.
  Definition downshift_thunkable_to_thunkable : D ₜ ⟶ D ₜ
    := downshift_thunkable_to_positive_thunkable ∙ positive_thunkable_category_to_thunkable_category D.
  Definition downshift_thunkable_to_linear : D ₜ ⟶ D ₗ
    := downshift_thunkable_to_positive_thunkable ∙ positive_thunkable_category_to_linear_category D.
  Definition downshift_thunkable_to_positive : D ₜ ⟶ D⁺
    := downshift_thunkable_to_positive_thunkable ∙ positive_thunkable_category_to_positive_category D.
  Definition downshift_negative_to_positive : D⁻ ⟶ D⁺
    := negative_category_to_thunkable_category D ∙ downshift_thunkable_to_positive.

  (** This non-functorial map is useful for defining the adjunctions below. *)
  Definition downshift_'_to_linear : functor_data D (D ₗ)
    := functor_composite_data downshift_'_to_positive
         (positive_category_to_linear_category D).

  (** Alternative characterisation of [downshift_thunkable_to_positive]
      factoring through D instead of D ₜ. *)
  Definition downshift_data_thunkable_to_positive' : functor_data (D ₜ) (D⁺)
    := functor_composite_data (thunkable_category_to_unital_magmoid D)
         downshift_'_to_positive.

  Lemma downshift_is_functor_thunkable_to_positive' : is_functor downshift_data_thunkable_to_positive'.
  Proof. apply (pr2 downshift_thunkable_to_positive). Defined.

  Definition downshift_thunkable_to_positive' : D ₜ ⟶ D⁺ :=
    make_functor _ downshift_is_functor_thunkable_to_positive'.

  (** [downshift_thunkable_to_positive] and [downshift_thunkable_to_positive'] are equal,
      definitionally. *)
  Lemma downshift_thunkable_to_positive_eq
    : downshift_thunkable_to_positive = downshift_thunkable_to_positive'.
  Proof. reflexivity. Defined.

End shift_functors.

(** ** 4. Adjunctions of the shift functors of a duploid *)
Section shift_functors_adjunction.
  Context (D : duploid).

  Definition delayed_mor (a b : D) := thunkable_mor a (⇑b).
  Definition wrapped_mor (a b : D) := linear_mor (⇓a) b.

  Identity Coercion Id_delayed_mor : delayed_mor >-> thunkable_mor.
  Identity Coercion Id_wrapped_mor : wrapped_mor >-> linear_mor.

  (** The natural isomorphism [delayed_mor] ≃ [D⟦-, -⟧] *)
  Definition mor_to_delayed_mor {a b : D} (f : D⟦a, b⟧) : delayed_mor a b.
  Proof.
    use make_thunkable_mor.
    - apply (f · delay _).
    - apply is_thunkable_of_negative, (⇑_).
  Defined.

  Definition mor_from_delayed_mor {a b : D} (f : delayed_mor a b) : D⟦a, b⟧.
  Proof. apply (thunkable_mor_to_mor f · force _). Defined.

  Lemma mor_to_from_delayed_mor {a b : D} (f : delayed_mor a b)
    : mor_to_delayed_mor (mor_from_delayed_mor f) = f.
  Proof.
    apply carrier_eq; cbn.
    refine (assoc'_thunkable _ f _ _ @ _ @ magmoid_id_right _).
    apply cancel_precomposition, force_delay_id.
  Qed.

  Lemma mor_from_to_delayed_mor {a b : D} (f : D⟦a, b⟧)
    : mor_from_delayed_mor (mor_to_delayed_mor f) = f.
  Proof. apply delay_force_right. Qed.

  Lemma weq_delayed_mor (a b : D) : delayed_mor a b ≃ D⟦a, b⟧.
  Proof.
    use weq_iso.
    - apply mor_from_delayed_mor.
    - apply mor_to_delayed_mor.
    - apply mor_to_from_delayed_mor.
    - apply mor_from_to_delayed_mor.
  Defined.

  Lemma invmap_weq_delayed_mor {a b : D} (f : D⟦a, b⟧)
    : invmap (weq_delayed_mor a b) f = mor_to_delayed_mor f.
  Proof.
    apply invmap_eq, pathsinv0, mor_from_to_delayed_mor.
  Qed.

  (** The natural isomorphism [wrapped_mor] ≃ [D⟦-, -⟧] *)
  Definition mor_to_wrapped_mor {a b : D} (f : D⟦a, b⟧) : wrapped_mor a b.
  Proof.
    use make_linear_mor.
    - apply (f ∘ unwrap _).
    - apply is_linear_of_positive, (⇓_).
  Defined.

  Definition mor_from_wrapped_mor {a b : D} (f : wrapped_mor a b) : D⟦a, b⟧.
  Proof. apply (linear_mor_to_mor f ∘ wrap _). Defined.

  Lemma mor_to_from_wrapped_mor {a b : D} (f : wrapped_mor a b)
    : mor_to_wrapped_mor (mor_from_wrapped_mor f) = f.
  Proof.
    apply carrier_eq; cbn.
    refine (assoc_linear _ f _ _ @ _ @ magmoid_id_left _).
    apply cancel_postcomposition, unwrap_wrap_id.
  Qed.

  Lemma mor_from_to_wrapped_mor {a b : D} (f : D⟦a, b⟧)
    : mor_from_wrapped_mor (mor_to_wrapped_mor f) = f.
  Proof. apply wrap_unwrap_left. Qed.

  Lemma weq_wrapped_mor (a b : D) : wrapped_mor a b ≃ D⟦a, b⟧.
  Proof.
    use weq_iso.
    - apply mor_from_wrapped_mor.
    - apply mor_to_wrapped_mor.
    - apply mor_to_from_wrapped_mor.
    - apply mor_from_to_wrapped_mor.
  Defined.

  Lemma invmap_weq_wrapped_mor {a b : D} (f : D⟦a, b⟧)
    : invmap (weq_wrapped_mor a b) f = mor_to_wrapped_mor f.
  Proof.
    apply invmap_eq, pathsinv0, mor_from_to_wrapped_mor.
  Qed.

  (** The naturalities themselves *)

  (* The adjunction D ₗ⟦⇓I-, -⟧ ≃ D ₜ⟦-, ⇑I-⟧. *)
  Lemma nathomweq_delayed_mor
    : natural_hom_weq
        (thunkable_category_to_unital_magmoid D)
        (upshift_'_to_thunkable D).
  Proof.
    use tpair. {
      intros a b.
      apply invweq, weq_delayed_mor.
    }
    use make_dirprod.
    - cbn; intros a b f c g.
      apply carrier_eq; cbn.
      apply (assoc'_linear _ (delay _)).
    - cbn; intros a b f c g.
      apply carrier_eq; cbn.
      unfold upshiftf.
      rewrite (assoc'_linear _ (delay _)).
      apply pathsinv0.
      etrans. apply delay_force_interpose.
      apply (assoc_linear _ (delay _)).
  Defined.

  Lemma nathomweq_wrapped_mor
    : natural_hom_weq
        (downshift_'_to_linear D)
        (linear_category_to_unital_magmoid D).
  Proof.
    use tpair. {
      intros a b.
      apply weq_wrapped_mor.
    }
    use make_dirprod.
    - cbn; intros a b f c g.
      refine (_ @ wrap_unwrap_left _).
      unfold mor_from_wrapped_mor; cbn.
      apply maponpaths.
      refine (assoc'_thunkable _ (unwrap _) _ _ @ _).
      apply maponpaths.
      apply (assoc'_linear _ f).
    - intros a b f c g.
      apply (assoc_thunkable _ (wrap _)).
  Defined.

  Lemma nathomweq_delayed_wrapped
    : natural_hom_weq
        (downshift_thunkable_to_linear D)
        (upshift_linear_to_thunkable D).
  Proof.
    apply (natural_hom_weq_compose _ _ _ _
             nathomweq_delayed_mor
             nathomweq_wrapped_mor).
  Defined.

  Lemma are_adjoints_downshift_upshift_thunkable_to_linear
    : are_adjoints (downshift_thunkable_to_linear D) (upshift_linear_to_thunkable D).
  Proof. apply adj_from_nathomweq, nathomweq_delayed_wrapped. Defined.

  (* The adjunction D⁺ ⟦⇓I-, -⟧ ≃ D⁻ ⟦-, ⇑I-⟧. *)
  Lemma nathomweq_delayed_mor'
    : natural_hom_weq
        (negative_category_to_thunkable_category D
           ∙ thunkable_category_to_unital_magmoid D)
        (upshift_'_to_negative D).
  Proof.
    use tpair. {
      intros a b.
      refine (weqcomp _ _).
      2: apply invweq, weqtotalsubtype.
      apply (hom_weq nathomweq_delayed_mor).
    }
    use make_dirprod.
    - intros a b c f g.
      apply carrier_eq.
      apply (hom_natural_precomp nathomweq_delayed_mor).
    - intros a b c f g.
      apply carrier_eq.
      apply (hom_natural_postcomp nathomweq_delayed_mor).
  Defined.

  Lemma nathomweq_wrapped_mor'
    : natural_hom_weq
        (downshift_'_to_positive D)
        (positive_category_to_linear_category D
           ∙ linear_category_to_unital_magmoid D).
  Proof.
    use tpair. {
      intros a b.
      refine (weqcomp _ _).
      1: apply weqtotalsubtype.
      apply (hom_weq nathomweq_wrapped_mor).
    }
    use make_dirprod.
    - intros a b c f g.
      apply (hom_natural_precomp nathomweq_wrapped_mor).
    - intros a b c f g.
      apply (hom_natural_postcomp nathomweq_wrapped_mor).
  Defined.

  Lemma nathomweq_delayed_wrapped'
    : natural_hom_weq
        (downshift_negative_to_positive D)
        (upshift_positive_to_negative D).
  Proof.
    apply (natural_hom_weq_compose _ _ _ _
             nathomweq_delayed_mor'
             nathomweq_wrapped_mor').
  Defined.

  Lemma are_adjoints_downshift_upshift_negative_to_positive
    : are_adjoints
        (downshift_negative_to_positive D)
        (upshift_positive_to_negative D).
  Proof. apply adj_from_nathomweq, nathomweq_delayed_wrapped'. Defined.

End shift_functors_adjunction.

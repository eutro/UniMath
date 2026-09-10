(********************************************************************************

 Subcategories of a Unital Magmoid

 Author: B. Szilvasy
 January 2026

 There are several subcategories of a given unital magmoid M:

 - [linear_category M] written M ₗ has all objects and linear morphisms.
 - [thunkable_category M] written M ₜ has all objects and thunkable morphisms.
 - [linear_and_thunkable_category M] written M ₗₜ has all objects and linear-and-thunkable morphisms.

 - [negative_category M] written M⁻ has negative objects and thunkable morphisms.
 - [positive_category M] written M⁺ has positive objects and linear morphisms.

 - [negative_linear_category M] written M⁻ₗ has negative objects and linear-and-thunkable morphisms.
 - [positive_thunkable_category M] written M⁺ₜ has positive objects and linear-and-thunkable morphisms.

 Contents:
 1. Definitions of unital magmoid subcategories
 2. Inclusion functors
 3. Extra weak equivalences of polarized subtypes

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.

Local Open Scope cat.
Local Open Scope unital_magmoid.

(** ** 1. Definitions of unital magmoid subcategories *)
Section polarized_categories.
  Context (M : unital_magmoid).

  Definition wide_submagmoid_to_unital_magmoid
    (P : wide_submagmoid M)
    : unital_magmoid.
  Proof.
    use make_unital_magmoid.
    1: use make_unital_premagmoid.
    - exact (wide_submagmoid_to_unital_premagmoid_data P).
    - use make_is_unital_premagmoid.
      + intros a b f; apply carrier_eq, magmoid_id_left.
      + intros a b f; apply carrier_eq, magmoid_id_right.
    - intros a b; apply isaset_wide_submagmoid_carrier.
  Defined.

  Definition wide_subcategory_to_category
    (P : wide_subcategory M)
    : category.
  Proof.
    use make_category.
    1: use make_precategory.
    - exact (wide_submagmoid_to_unital_premagmoid_data P).
    - use make_is_precategory.
      + intros a b f; apply carrier_eq, magmoid_id_left.
      + intros a b f; apply carrier_eq, magmoid_id_right.
      + intros a b c d f g h.
        apply carrier_eq.
        exact (wide_subcategory_is_associative P
                 _ _ _ _ _ _ _ (pr2 f) (pr2 g) (pr2 h)).
      + intros a b c d f g h.
        apply carrier_eq.
        exact (!wide_subcategory_is_associative P
                 _ _ _ _ _ _ _ (pr2 f) (pr2 g) (pr2 h)).
    - intros a b; apply isaset_wide_submagmoid_carrier.
  Defined.

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

  (** The category of all objects and linear-and-thunkable maps. *)
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

Notation "M 'ₗ'" := (linear_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \_l *)
Notation "M 'ₜ'" := (thunkable_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \_t *)
Notation "M 'ₗₜ'" := (linear_and_thunkable_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \_l \_t *)
Notation "M '⁺'" := (positive_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \^+ *)
Notation "M '⁻'" := (negative_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \^- *)
Notation "M '⁺ₜ'" := (positive_thunkable_category M) (at level 1) : unital_magmoid.
  (* type in Emacs using agda-input with \^+ \_t *)
Notation "M '⁻ₗ'" := (negative_linear_category M) (at level 1) : unital_magmoid.
(* type in Emacs using agda-input with \^- \_l *)

(** ** 2. Inclusion functors

  The inclusion functors between the categories of a unital magmoid M
  are depicted in the commutative diagram below. Of these, all but
  the four vertically drawn functors are fully faithful.

  <<
                      M⁺  ⟶ Mₗ    ↰
                      ↑     ↑
                      M⁺ₜ → Mₗₜ  ← M⁻ₗ
                            ↓     ↓
                      ↳     Mₜ  ← M⁻
  >>

  All categories also have inclusion functors into M itself.

 *)
Section inclusion_functors.
  Context (M : unital_magmoid).

  (** The easy fully-faithful inclusion functors for the above. *)

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

  (** M⁺ₜ into M ₗₜ *)
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

  (** M⁻ₗ into M ₗₜ *)
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

  (** M ₗₜ into M ₗ *)
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

  (** M ₗₜ into M ₜ *)
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

  (** M⁺ₜ into M⁺ *)
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

  (** M⁻ₗ into M⁻ *)
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

  (** M⁺ₜ into M ₗ *)
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

  (** I : M⁺ₜ ⟶ M ₗ factors through M⁺ *)
  Lemma positive_thunkable_category_to_linear_category_through_positive
    : positive_thunkable_category_to_linear_category
      = (positive_thunkable_category_to_positive_category
           ∙ positive_category_to_linear_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

  (** M⁻ₗ into M ₜ *)
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

  (** I : M⁻ₗ ⟶ M ₜ factors through M⁻ *)
  Lemma negative_linear_category_to_thunkable_category_through_negative
    : negative_linear_category_to_thunkable_category
      = (negative_linear_category_to_negative_category
           ∙ negative_category_to_thunkable_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

  (** I : M⁻ₗ ⟶ M ₗ factors through M ₗₜ *)
  Lemma negative_linear_category_to_linear_category_through_thunkable
    : negative_linear_category_to_linear_category
      = (negative_linear_category_to_linear_and_thunkable_category
           ∙ linear_and_thunkable_category_to_linear_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

  (** I : M⁺ₜ ⟶ M ₜ factors through M ₜₗ *)
  Lemma positive_thunkable_category_to_thunkable_category_through_linear
    : positive_thunkable_category_to_thunkable_category
      = (positive_thunkable_category_to_linear_and_thunkable_category
           ∙ linear_and_thunkable_category_to_thunkable_category).
  Proof. now apply (functor_eq _ _ (homset_property _)). Defined.

  (** Inclusion functors into M. *)
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

  Definition positive_category_to_unital_magmoid : M⁺ ⟶ M
    := positive_category_to_linear_category ∙ linear_category_to_unital_magmoid.

  Lemma fully_faithful_positive_category_to_unital_magmoid
    : fully_faithful positive_category_to_unital_magmoid.
  Proof.
    intros a b.
    use isweq_iso.
    - intro f.
      refine (make_linear_mor f _,,tt).
      apply is_linear_of_positive, (pr2 a).
    - abstract (intros f; now do 2 apply carrier_eq).
    - easy.
  Defined.

  Definition negative_category_to_unital_magmoid : M⁻ ⟶ M
    := negative_category_to_thunkable_category ∙ thunkable_category_to_unital_magmoid.

  Lemma fully_faithful_negative_category_to_unital_magmoid
    : fully_faithful negative_category_to_unital_magmoid.
  Proof.
    intros a b.
    use isweq_iso.
    - intro f.
      refine (make_thunkable_mor f _,,tt).
      apply is_thunkable_of_negative, (pr2 b).
    - abstract (intros f; now do 2 apply carrier_eq).
    - easy.
  Defined.

End inclusion_functors.

(** ** Extra weak equivalences of polarized subtypes *)

Section polarized_equivs.
  Lemma iscontr_is_linear_of_positive {M : unital_magmoid}
    {a b : M} (f : a --> b) (H : is_positive a)
    : iscontr (is_linear f).
  Proof.
    apply iscontraprop1; [apply isaprop_is_linear|].
    apply is_linear_of_positive, H.
  Qed.

  Lemma weq_linear_mor_of_positive {M : unital_magmoid}
    (a b : M) (H : is_positive a)
    : linear_mor a b ≃ M⟦a, b⟧.
  Proof.
    apply weqpr1; intro f.
    apply iscontr_is_linear_of_positive, H.
  Defined.

  Lemma weq_mor_to_positive_category {M : unital_magmoid}
    (a b : positive_ob M) : M⟦a, b⟧ ≃ M⁺⟦a, b⟧.
  Proof.
    apply invweq,
      (weq_from_fully_faithful
         (fully_faithful_positive_category_to_unital_magmoid M)).
  Defined.

  Lemma iscontr_is_thunkable_of_negative {M : unital_magmoid}
    {a b : M} (f : a <-- b) (H : is_negative a)
    : iscontr (is_thunkable f).
  Proof.
    apply iscontraprop1; [apply isaprop_is_thunkable|].
    apply is_thunkable_of_negative, H.
  Qed.

  Lemma weq_thunkable_mor_of_negative {M : unital_magmoid}
    (a b : M) (H : is_negative b)
    : thunkable_mor a b ≃ M⟦a, b⟧.
  Proof.
    apply weqpr1; intro f.
    apply iscontr_is_thunkable_of_negative, H.
  Defined.

  Lemma weq_mor_to_negative_category {M : unital_magmoid}
    (a b : negative_ob M) : M⟦a, b⟧ ≃ M⁻⟦a, b⟧.
  Proof.
    apply invweq,
      (weq_from_fully_faithful
         (fully_faithful_negative_category_to_unital_magmoid M)).
  Defined.

  Lemma weq_linear_and_thunkable_mor_to_thunkable_mor {M : unital_magmoid}
    (a b : M) (H : is_positive a)
    : linear_and_thunkable_mor a b ≃ thunkable_mor a b.
  Proof.
    Succeed
      (apply weqfibtototal; intro f;
       apply invweq, dirprod_with_contr_l;
       apply iscontr_is_linear_of_positive, H).
    (* Proving it directly for performance. *)
    apply (make_weq linear_and_thunkable_mor_to_thunkable_mor).
    use isweq_iso.
    - intro f; apply (make_linear_and_thunkable_mor_from_thunkable f).
      abstract (apply is_linear_of_positive, H).
    - abstract (intro f; now apply carrier_eq).
    - abstract (intro f; now apply carrier_eq).
  Defined.

  Lemma weq_linear_and_thunkable_mor_to_linear_mor {M : unital_magmoid}
    (a b : M) (H : is_negative b)
    : linear_and_thunkable_mor a b ≃ linear_mor a b.
  Proof.
    Succeed
      (apply weqfibtototal; intro f;
       apply invweq, dirprod_with_contr_r;
       apply iscontr_is_thunkable_of_negative, H).
    (* Proving it directly for performance. *)
    apply (make_weq linear_and_thunkable_mor_to_linear_mor).
    use isweq_iso.
    - intro f; apply (make_linear_and_thunkable_mor_from_linear f).
      abstract (apply is_thunkable_of_negative, H).
    - abstract (intro f; now apply carrier_eq).
    - abstract (intro f; now apply carrier_eq).
  Defined.

  Lemma weq_linear_and_thunkable_mor_to_linear_and_thunkable_category {M : unital_magmoid}
    (a b : M) : M ₗₜ⟦a, b⟧ ≃ linear_and_thunkable_mor a b.
  Proof. apply idweq. Defined.

  Lemma weq_linear_and_thunkable_mor_to_positive_thunkable_category {M : unital_magmoid}
    (a b : positive_ob M) : M⁺ₜ⟦a, b⟧ ≃ linear_and_thunkable_mor a b.
  Proof.
    eapply weqcomp; [|apply weq_linear_and_thunkable_mor_to_linear_and_thunkable_category].
    apply (weq_from_fully_faithful
             (fully_faithful_positive_thunkable_category_to_linear_and_thunkable_category M)).
  Defined.

  Lemma weq_linear_and_thunkable_mor_to_negative_linear_category {M : unital_magmoid}
    (a b : negative_ob M) : M⁻ₗ⟦a, b⟧ ≃ linear_and_thunkable_mor a b.
  Proof.
    eapply weqcomp; [|apply weq_linear_and_thunkable_mor_to_linear_and_thunkable_category].
    apply (weq_from_fully_faithful
             (fully_faithful_negative_linear_category_to_linear_and_thunkable_category M)).
  Defined.

  Lemma weq_z_iso_submm_iso {M : unital_magmoid} (P : wide_submagmoid M)
    (a b : M)
    : submm_iso P a b ≃ z_iso (C:=P) a b.
  Proof.
    use weq_iso.
    - intros [f [g Hfg]].
      apply (make_z_iso (C:=P) f g).
      split; apply carrier_eq.
      + exact (pr1 Hfg).
      + exact (pr2 Hfg).
    - intros [f [g Hfg]].
      apply (make_submm_iso_2 P f g).
      split.
      + exact (base_paths _ _ (pr1 Hfg)).
      + exact (base_paths _ _ (pr2 Hfg)).
    - abstract (intros f; do 2 apply pair_path_in2;
                apply isaprop_is_inverse_in_precat_of_magmoid).
    - abstract (intros f; do 2 apply pair_path_in2;
                apply isaprop_is_inverse_in_precat_of_magmoid).
  Defined.

  Lemma weq_z_iso_submm_iso' {M : unital_magmoid} (P : wide_submagmoid M)
    (a b : M)
    : submm_iso' P a b ≃ z_iso (C:=P) a b.
  Proof.
    use weq_iso.
    - intros [f [Hf [g Hfg]]].
      apply (make_z_iso (C:=P) (f,,Hf) g).
      split; apply carrier_eq.
      + exact (pr1 Hfg).
      + exact (pr2 Hfg).
    - intros [f [g Hfg]].
      apply (make_submm_iso' P (pr1carrier _ f) (pr2 f)).
      apply (make_has_submm_inverse P _ g).
      split.
      + exact (base_paths _ _ (pr1 Hfg)).
      + exact (base_paths _ _ (pr2 Hfg)).
    - abstract (intros f; do 3 apply pair_path_in2;
                apply isaprop_is_inverse_in_precat_of_magmoid).
    - abstract (intros f; do 2 apply pair_path_in2;
                apply isaprop_is_inverse_in_precat_of_magmoid).
  Defined.

  Lemma weq_z_iso_lt_iso {M : unital_magmoid} (a b : M)
    : lt_iso a b ≃ z_iso (C:=linear_and_thunkable_category M) a b.
  Proof.
    exact (weq_z_iso_submm_iso' (isw_linear_and_thunkable M) a b).
  Defined.

  Lemma weq_z_iso_lt_iso_positive {M : unital_magmoid} (a b : positive_ob M)
    : lt_iso a b ≃ z_iso (C:=positive_thunkable_category M) a b.
  Proof.
    eapply weqcomp; [apply weq_z_iso_lt_iso|].
    apply invweq,
      (weq_ff_functor_on_z_iso
         (fully_faithful_positive_thunkable_category_to_linear_and_thunkable_category M)).
  Defined.

  Lemma weq_z_iso_lt_iso_negative {M : unital_magmoid} (a b : negative_ob M)
    : lt_iso a b ≃ z_iso (C:=negative_linear_category M) a b.
  Proof.
    eapply weqcomp; [apply weq_z_iso_lt_iso|].
    apply invweq,
      (weq_ff_functor_on_z_iso
         (fully_faithful_negative_linear_category_to_linear_and_thunkable_category M)).
  Defined.

End polarized_equivs.

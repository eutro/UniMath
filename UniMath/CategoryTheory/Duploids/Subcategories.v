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
Require Import UniMath.CategoryTheory.Duploids.Magmoids.
Require Import UniMath.CategoryTheory.Duploids.Duploids.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

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
    - apply isaset_linear_mor.
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
    - apply isaset_thunkable_mor.
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
    - apply isaset_linear_and_thunkable_mor.
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

(** ** 2. Inclusion functors *)
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
  Definition positive_linear_category_to_positive_category : M⁺ₜ ⟶ M⁺.
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

  Lemma faithful_positive_linear_category_to_positive_category
    : faithful positive_linear_category_to_positive_category.
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
  Definition negative_thunkable_category_to_negative_category : M⁻ₗ ⟶ M⁻.
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

  Lemma faithful_negative_thunkable_category_to_negative_category
    : faithful negative_thunkable_category_to_negative_category.
  Proof.
    intros a b.
    apply isinclbetweensets.
    1, 2: apply homset_property.
    intros f f' p.
    do 2 apply carrier_eq.
    do 2 apply base_paths in p.
    exact p.
  Defined.

End inclusion_functors.

(** ** 3. Definition of the shift functors of a duploid *)

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
  Proof. unfold upshiftf. now rewrite magmoid_id_right, force_delay_id. Qed.
  Lemma upshiftf_comp {a b c : D} (f : linear_mor a b) (g : linear_mor b c)
    : #⇑(f · g) = (#⇑f) · (#⇑g).
  Proof.
    unfold upshiftf.
    rewrite (assoc_negative _ (⇑b)).
    do 2 rewrite (assoc_linear _ g).
    now rewrite delay_force_right.
  Qed.
  Lemma is_linear_upshiftf {a b : D} (f : linear_mor a b) : is_linear (#⇑f).
  Proof.
    apply is_linear_compose.
    - apply is_linear_compose.
      + apply (force a).
      + apply f.
    - apply (delay b).
  Defined.

  Lemma upshift_functor_data : functor_data (linear_category D) (negative_linear_category D).
  Proof.
    use make_functor_data.
    - apply upshift.
    - intros a b f.
      use (make_linear_mor _ _,,tt).
      + apply upshiftf, f.
      + apply is_linear_upshiftf.
  Defined.
  Lemma upshift_functor_is_functor :
    is_functor upshift_functor_data.
  Proof.
    use make_is_functor.
    - intro a. apply carrier_eq, carrier_eq, upshiftf_id.
    - intros a b c f g. apply carrier_eq, carrier_eq, upshiftf_comp.
  Qed.
  Definition upshift_functor : D ₗ ⟶ D⁻ₗ
    := make_functor _ upshift_functor_is_functor.

  (* Downshift functor *)
  Lemma downshiftf_id (a : D) : #⇓identity a = identity (⇓a).
  Proof. unfold downshiftf. now rewrite magmoid_id_left, unwrap_wrap_id. Qed.
  Lemma downshiftf_comp {a b c : D} (f : thunkable_mor a b) (g : thunkable_mor b c)
    : #⇓(f · g) = (#⇓f) · (#⇓g).
  Proof.
    unfold downshiftf.
    rewrite (assoc'_positive _ (⇓b)).
    do 2 rewrite (assoc'_thunkable _ f).
    now rewrite wrap_unwrap_left.
  Qed.
  Lemma is_thunkable_downshiftf {a b : D} (f : thunkable_mor a b) : is_thunkable (#⇓f).
  Proof.
    apply is_thunkable_compose.
    - apply (unwrap a).
    - apply is_thunkable_compose.
      + apply f.
      + apply (wrap b).
  Defined.

  Lemma downshift_functor_data : functor_data (thunkable_category D) (positive_thunkable_category D).
  Proof.
    use make_functor_data.
    - apply downshift.
    - intros a b f.
      use (make_thunkable_mor _ _,,tt).
      + apply downshiftf, f.
      + apply is_thunkable_downshiftf.
  Defined.
  Lemma downshift_functor_is_functor :
    is_functor downshift_functor_data.
  Proof.
    use make_is_functor.
    - intro a. apply carrier_eq, carrier_eq, downshiftf_id.
    - intros a b c f g. apply carrier_eq, carrier_eq, downshiftf_comp.
  Qed.
  Definition downshift_functor : D ₜ ⟶ D⁺ₜ
    := make_functor _ downshift_functor_is_functor.

End shift_functors.

(** ** 4. Adjunctions of the shift functors of a duploid *)
Section shift_functors_adjunction.
  Context (D : duploid).

  (* The extended upshift functor I⇑ : D ₗ ⟶ D ₗ which is naturally isomorphic to 1_{D ₗ}. *)
  Definition extended_upshift_functor : D ₗ ⟶ D ₗ
    := upshift_functor D ∙ negative_linear_category_to_linear_category D.

  Lemma extended_upshift_functor_nat_z_iso_identity
    : nat_z_iso extended_upshift_functor (functor_identity (D ₗ)).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro a. apply (force a).
      + abstract (intros a b f; apply carrier_eq, delay_force_right).
    - intro a.
      use make_is_z_isomorphism.
      + apply (delay a).
      + constructor; apply carrier_eq.
        * apply force_delay_id.
        * apply delay_force_id.
  Defined.

  (* The negative-only upshift functor ⇑I : D⁻ₗ ⟶ D⁻ₗ *)
  Definition negative_only_upshift_functor : D⁻ₗ ⟶ D⁻ₗ
    := negative_linear_category_to_linear_category D ∙ upshift_functor D.

  Lemma negative_only_upshift_functor_nat_z_iso_identity
    : nat_z_iso negative_only_upshift_functor (functor_identity (D⁻ₗ)).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro a; refine (_,,tt); apply (force (a : negative_ob D)).
      + abstract (intros a b f; apply carrier_eq, carrier_eq, delay_force_right).
    - intro a.
      use make_is_z_isomorphism.
      + refine (_,,tt); apply (delay (a : negative_ob D)).
      + constructor; do 2 apply carrier_eq.
        * apply force_delay_id.
        * apply delay_force_id.
  Defined.

  (* The adjoint equivalence I ⊣ ⇑ : D ₗ ⟶ D⁻ₗ *)
  Definition upshift_equivalent_inclusion_adj_data
    : adjunction_data (D⁻ₗ) (D ₗ).
  Proof.
    use make_adjunction_data.
    - exact (negative_linear_category_to_linear_category D).
    - exact (upshift_functor D).
    - apply nat_z_iso_inv, negative_only_upshift_functor_nat_z_iso_identity.
    - apply extended_upshift_functor_nat_z_iso_identity.
  Defined.

  Definition upshift_equivalent_inclusion
    : forms_equivalence upshift_equivalent_inclusion_adj_data.
  Proof.
    use make_forms_equivalence.
    - apply (pr2_nat_z_iso (nat_z_iso_inv negative_only_upshift_functor_nat_z_iso_identity)).
    - apply (pr2_nat_z_iso extended_upshift_functor_nat_z_iso_identity).
  Defined.

  Definition negative_linear_equivalent_linear : equivalence_of_cats (D⁻ₗ) (D ₗ)
    := make_equivalence_of_cats _ upshift_equivalent_inclusion.
  Definition negative_linear_adj_equivalent_linear
    : adj_equivalence_of_cats (negative_linear_category_to_linear_category D)
    := adjointification negative_linear_equivalent_linear.

  (* The extended downshift functor I⇓ : D ₜ ⟶ D ₜ which is naturally isomorphic to 1_{D ₜ}. *)
  Definition extended_downshift_functor : D ₜ ⟶ D ₜ
    := downshift_functor D ∙ positive_thunkable_category_to_thunkable_category D.

  Lemma extended_downshift_functor_nat_z_iso_identity
    : nat_z_iso (functor_identity (D ₜ)) extended_downshift_functor.
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro a. apply (wrap a).
      + abstract (intros a b f; apply carrier_eq, pathsinv0, wrap_unwrap_left).
    - intro a.
      use make_is_z_isomorphism.
      + apply (unwrap a).
      + constructor; apply carrier_eq.
        * apply wrap_unwrap_id.
        * apply unwrap_wrap_id.
  Defined.

  (* The positive-only downshift functor ⇓I : D⁺ₜ ⟶ D⁺ₜ *)
  Definition positive_only_downshift_functor : D⁺ₜ ⟶ D⁺ₜ
    := restrict_functor_to_sub_precategory _ (downshift_functor D).

  Lemma positive_only_downshift_functor_nat_z_iso_identity
    : nat_z_iso (functor_identity (D⁺ₜ)) positive_only_downshift_functor.
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro a; refine (_,,tt); apply (wrap (a : positive_ob D)).
      + abstract (
            intros a b f;
            apply carrier_eq, carrier_eq, pathsinv0, wrap_unwrap_left).
    - intro a.
      use make_is_z_isomorphism.
      + refine (_,,tt); apply (unwrap (a : positive_ob D)).
      + constructor; do 2 apply carrier_eq.
        * apply wrap_unwrap_id.
        * apply unwrap_wrap_id.
  Defined.

  (* The adjoint equivalence I ⊣ ⇓ : D ₜ ⟶ D⁺ₜ *)
  Definition downshift_equivalent_inclusion_adj_data
    : adjunction_data (D⁺ₜ) (D ₜ).
  Proof.
    use make_adjunction_data.
    - exact (positive_thunkable_category_to_thunkable_category D).
    - exact (downshift_functor D).
    - apply positive_only_downshift_functor_nat_z_iso_identity.
    - apply nat_z_iso_inv, extended_downshift_functor_nat_z_iso_identity.
  Defined.

  Definition downshift_equivalent_inclusion
    : forms_equivalence downshift_equivalent_inclusion_adj_data.
  Proof.
    use make_forms_equivalence.
    - apply (pr2_nat_z_iso positive_only_downshift_functor_nat_z_iso_identity).
    - apply (pr2_nat_z_iso (nat_z_iso_inv extended_downshift_functor_nat_z_iso_identity)).
  Defined.

  Definition positive_thunkable_equivalent_thunkable : equivalence_of_cats (D⁺ₜ) (D ₜ)
    := make_equivalence_of_cats _ downshift_equivalent_inclusion.
  Definition positive_thunkable_adj_equivalent_thunkable
    : adj_equivalence_of_cats (positive_thunkable_category_to_thunkable_category D)
    := adjointification positive_thunkable_equivalent_thunkable.

  (* The adjunction D ₗ ⟦I⇓-, -⟧ ≃ D ₜ ⟦-, I⇑-⟧. *)
  Lemma are_adjoints_downshift_upshift
    : are_adjoints
        (downshift_functor D
           ∙ positive_thunkable_category_to_linear_and_thunkable_category D
           ∙ linear_and_thunkable_category_to_linear_category D)
        (upshift_functor D
           ∙ negative_linear_category_to_linear_and_thunkable_category D
           ∙ linear_and_thunkable_category_to_thunkable_category D).
  Abort.

End shift_functors_adjunction.

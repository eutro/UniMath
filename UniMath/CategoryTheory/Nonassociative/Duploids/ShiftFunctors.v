(********************************************************************************

 Shift Functors of a Duploid

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition of the shift functors of a duploid
 2. Adjunctions of the shift functors of a duploid
 3. Definition and adjunction of the restricted shift functors of a duploid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

(** ** 1. Definition of the shift functors of a duploid

 The shifts of a duploid D give rise to the following non-functorial maps on
 morphisms, defined just below.

 - #⇑ : D⟦a, b⟧ -> D ₜ⟦⇑a, ⇑b⟧
 - #⇓ : D⟦a, b⟧ -> D ₗ⟦⇓a, ⇓b⟧

 When extended and restricted along the relevant inclusion functors, we obtain
 the following two commutative diagrams of (almost) functors:

 <<
  D⁺ ↪ Dₗ  ↪  D
     ⇑ ↓      ↓ ⇑
       D⁺ₗ ↪  D⁻  ↪  Dₜ

  D⁻ ↪ Dₜ  ↪  D
     ⇓ ↓      ↓ ⇓
       D⁻ₜ ↪  D⁺  ↪  Dₗ
 >>

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

  (** *** Upshift functor *)
  (** **** Conditional functoriality *)
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

  (** **** ⇑ on objects gives a non-functorial map on objects and morphisms D ⟶ D⁻ *)
  Definition upshiftf' {a b : D} (f : D⟦a, b⟧) : thunkable_mor (⇑a) (⇑b)
    := make_thunkable_mor (#⇑f) (is_thunkable_of_negative _ (⇑_)).

  Definition upshift_'_to_negative : functor_data D (D⁻).
  Proof.
    use make_functor_data.
    - apply upshift.
    - intros a b f; apply (upshiftf' f,,tt).
  Defined.

  (** **** ⇑ is functorial once restricted to linear morphisms **)
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

  (** **** The various extended upshift functors *)
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

  (** These non-functorial maps are useful for defining the adjunctions below. *)
  Definition upshift_'_to_thunkable : functor_data D (D ₜ)
    := functor_composite_data upshift_'_to_negative
         (negative_category_to_thunkable_category D).
  Definition upshift_'_to_' : functor_data D D
    := functor_composite_data upshift_'_to_thunkable
         (thunkable_category_to_unital_magmoid D).

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

  (** *** Downshift functor *)
  (** **** Conditional functoriality *)
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

  (** **** ⇓ on objects gives a non-functorial map on objects and morphisms D ⟶ D⁺ *)
  Definition downshiftf' {a b : D} (f : D⟦a, b⟧) : linear_mor (⇓a) (⇓b)
    := make_linear_mor (#⇓f) (is_linear_of_positive _ (⇓_)).

  Definition downshift_'_to_positive : functor_data D (D⁺).
  Proof.
    use make_functor_data.
    - apply downshift.
    - intros a b f; apply (downshiftf' f,,tt).
  Defined.

  (** **** ⇓ is functorial once restricted to thunkable morphisms **)
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

  (** **** The various extended downshift functors *)
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

  (** These non-functorial maps are useful for defining the adjunctions below. *)
  Definition downshift_'_to_linear : functor_data D (D ₗ)
    := functor_composite_data downshift_'_to_positive
         (positive_category_to_linear_category D).
  Definition downshift_'_to_' : functor_data D D
    := functor_composite_data downshift_'_to_linear
         (linear_category_to_unital_magmoid D).

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

(** ** 3. Adjunctions of the shift functors of a duploid

  In a duploid D, morphisms take part in the following isomorphism:

  << Dₗ⟦⇓a, b⟧ ≃ D⟦⇓a, b⟧ ≃ D⟦a, b⟧ ≃ D⟦a, ⇑b⟧ ≃ Dₜ⟦a, ⇑b⟧ >>

  Moreover, these isomorphisms are natural in (a : Dₜ) and (b : Dₗ), yielding an
  adjunction ⇓ ⊣ ⇑ : D ₗ ⟶ D ₜ.  In fact, each isomorphism is "natural" even for
  (a : D) and (b : D), in the sense that they would be natural were it not for
  the lack of functoriality of ⇑, ⇓ and D's homsets.

  The above adjunction can be restricted along the inclusion functors (I : D⁻ ⟶
  Dₜ) and (J : D⁺ ⟶ Dₗ) to yield the adjunction ⇓I ⊣ ⇑J : D⁺ ⟶ D⁻.  The two
  halves of the adjunction can also be split and restricted along the inclusion
  functors (I : D⁺ₜ ⟶ Dₜ) and (J : D⁻ₗ ⟶ Dₗ) to give the following adjunctions,
  which moreover form adjoint equivalences, I ⊣ ⇓ : Dₜ ≃ D⁺ₜ and I ⊣ ⇑ : Dₗ ≃
  D⁻ₗ.

  TODO: would it be better to define all the [wrap]/[unwrap]/[force]/[delay]
  natural transformations?  Them being included in the data would be helpful,
  but it would be terribly frustrating proving their naturality over and over
  again...

*)
Section shift_functor_adjunctions.
  Context (D : duploid).

  (** *** Morphisms Dₜ⟦a, ⇑b⟧ ([delayed_mor]) and Dₗ⟦⇓a, b⟧ ([wrapped_mor]). *)
  Definition delayed_mor (a b : D) := thunkable_mor a (⇑b).
  Definition wrapped_mor (a b : D) := linear_mor (⇓a) b.

  Identity Coercion Id_delayed_mor : delayed_mor >-> thunkable_mor.
  Identity Coercion Id_wrapped_mor : wrapped_mor >-> linear_mor.

  (** *** The isomorphism [delayed_mor] ≃ [D⟦-, -⟧] *)
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

  (** *** The isomorphism [wrapped_mor] ≃ [D⟦-, -⟧] *)
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

  (** *** The adjunction D ₗ⟦⇓I-, -⟧ ≃ D ₜ⟦-, ⇑I-⟧. *)

  (** D⟦a, b⟧ ≃ D ₜ⟦a, ⇑b⟧, "naturally" in a and b *)
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

  (** D ₗ⟦⇓a, b⟧ ≃ D⟦a, b⟧, "naturally" in a and b *)
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

  (** D ₗ⟦⇓a, b⟧ ≃ D ₜ⟦a, ⇑b⟧, naturally in a and b *)
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

  (** *** The adjunction D⁺ ⟦⇓I-, -⟧ ≃ D⁻ ⟦-, ⇑I-⟧. *)

  (** D⟦a, b⟧ ≃ D⁻⟦a, ⇑b⟧, "naturally" in a and b *)
  Lemma nathomweq_delayed_mor'
    : natural_hom_weq
        (negative_category_to_thunkable_category D
           ∙ thunkable_category_to_unital_magmoid D)
        (upshift_'_to_negative D).
  Proof.
    use tpair. {
      intros a b.
      refine (weqcomp _ _).
      2: apply invweq,
          (weq_from_fully_faithful (fully_faithful_negative_category_to_thunkable_category D)).
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

  (** D⁺⟦⇓a, b⟧ ≃ D⟦a, b⟧, "naturally" in a and b *)
  Lemma nathomweq_wrapped_mor'
    : natural_hom_weq
        (downshift_'_to_positive D)
        (positive_category_to_linear_category D
           ∙ linear_category_to_unital_magmoid D).
  Proof.
    use tpair. {
      intros a b.
      refine (weqcomp _ _).
      1: apply (weq_from_fully_faithful (fully_faithful_positive_category_to_linear_category D)).
      apply (hom_weq nathomweq_wrapped_mor).
    }
    use make_dirprod.
    - intros a b c f g.
      apply (hom_natural_precomp nathomweq_wrapped_mor).
    - intros a b c f g.
      apply (hom_natural_postcomp nathomweq_wrapped_mor).
  Defined.

  (** D⁺⟦⇓a, b⟧ ≃ D⁻⟦a, ⇑b⟧, naturally in a and b *)
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

  (** *** Morphisms Dₗₜ⟦a, ⇑b⟧ ([linear_delayed_mor]) and Dₗₜ⟦⇓a, b⟧ ([thunkable_wrapped_mor]) *)

  Definition linear_delayed_mor (a b : D) := linear_and_thunkable_mor a (⇑b).
  Definition thunkable_wrapped_mor (a b : D) := linear_and_thunkable_mor (⇓a) b.

  Identity Coercion Id_linear_delayed_mor : linear_delayed_mor >-> linear_and_thunkable_mor.
  Identity Coercion Id_thunkable_wrapped_mor : thunkable_wrapped_mor >-> linear_and_thunkable_mor.

  Coercion linear_delayed_mor_to_delayed_mor {a b : D} (f : linear_delayed_mor a b) : delayed_mor a b := f.
  Coercion thunkable_wrapped_mor_to_wrapped_mor {a b : D} (f : thunkable_wrapped_mor a b) : wrapped_mor a b := f.

  (** *** The isomorphism [linear_delayed_mor] ≃ [Dₗ⟦-, -⟧] *)

  Definition linear_mor_to_linear_delayed_mor {a b : D} (f : linear_mor a b) : linear_delayed_mor a b.
  Proof.
    use make_linear_and_thunkable_mor_from_thunkable.
    - exact (mor_to_delayed_mor f).
    - apply is_linear_compose; apply linear_mor_is_linear.
  Defined.

  Definition linear_mor_from_linear_delayed_mor {a b : D} (f : linear_delayed_mor a b) : linear_mor a b.
  Proof.
    use make_linear_mor.
    - exact (mor_from_delayed_mor f).
    - apply is_linear_compose;
        (apply linear_and_thunkable_mor_is_linear_and_thunkable
         || apply linear_mor_is_linear).
  Defined.

  Lemma linear_mor_to_from_linear_delayed_mor {a b : D} (f : linear_delayed_mor a b)
    : linear_mor_to_linear_delayed_mor (linear_mor_from_linear_delayed_mor f) = f.
  Proof.
    apply carrier_eq.
    set (H := mor_to_from_delayed_mor f).
    apply base_paths in H.
    exact H.
  Qed.

  Lemma linear_mor_from_to_linear_delayed_mor {a b : D} (f : linear_mor a b)
    : linear_mor_from_linear_delayed_mor (linear_mor_to_linear_delayed_mor f) = f.
  Proof. apply carrier_eq, mor_from_to_delayed_mor. Qed.

  Lemma weq_linear_delayed_mor (a b : D) : linear_delayed_mor a b ≃ linear_mor a b.
  Proof.
    use weq_iso.
    - apply linear_mor_from_linear_delayed_mor.
    - apply linear_mor_to_linear_delayed_mor.
    - apply linear_mor_to_from_linear_delayed_mor.
    - apply linear_mor_from_to_linear_delayed_mor.
  Defined.

  Lemma invmap_weq_linear_delayed_mor {a b : D} (f : linear_mor a b)
    : invmap (weq_linear_delayed_mor a b) f = linear_mor_to_linear_delayed_mor f.
  Proof.
    apply invmap_eq, pathsinv0, linear_mor_from_to_linear_delayed_mor.
  Qed.

  (** *** The isomorphism [thunkable_wrapped_mor] ≃ [Dₜ⟦-, -⟧] *)

  Definition thunkable_mor_to_thunkable_wrapped_mor {a b : D} (f : thunkable_mor a b) : thunkable_wrapped_mor a b.
  Proof.
    use make_linear_and_thunkable_mor_from_linear.
    - exact (mor_to_wrapped_mor f).
    - apply is_thunkable_compose; apply thunkable_mor_is_thunkable.
  Defined.

  Definition thunkable_mor_from_thunkable_wrapped_mor {a b : D} (f : thunkable_wrapped_mor a b) : thunkable_mor a b.
  Proof.
    use make_thunkable_mor.
    - exact (mor_from_wrapped_mor f).
    - apply is_thunkable_compose;
        (apply linear_and_thunkable_mor_is_linear_and_thunkable
         || apply thunkable_mor_is_thunkable).
  Defined.

  Lemma thunkable_mor_to_from_thunkable_wrapped_mor {a b : D} (f : thunkable_wrapped_mor a b)
    : thunkable_mor_to_thunkable_wrapped_mor (thunkable_mor_from_thunkable_wrapped_mor f) = f.
  Proof.
    apply carrier_eq.
    set (H := mor_to_from_wrapped_mor f).
    apply base_paths in H.
    exact H.
  Qed.

  Lemma thunkable_mor_from_to_thunkable_wrapped_mor {a b : D} (f : thunkable_mor a b)
    : thunkable_mor_from_thunkable_wrapped_mor (thunkable_mor_to_thunkable_wrapped_mor f) = f.
  Proof. apply carrier_eq, mor_from_to_wrapped_mor. Qed.

  Lemma weq_thunkable_wrapped_mor (a b : D) : thunkable_wrapped_mor a b ≃ thunkable_mor a b.
  Proof.
    use weq_iso.
    - apply thunkable_mor_from_thunkable_wrapped_mor.
    - apply thunkable_mor_to_thunkable_wrapped_mor.
    - apply thunkable_mor_to_from_thunkable_wrapped_mor.
    - apply thunkable_mor_from_to_thunkable_wrapped_mor.
  Defined.

  Lemma invmap_weq_thunkable_wrapped_mor {a b : D} (f : thunkable_mor a b)
    : invmap (weq_thunkable_wrapped_mor a b) f = thunkable_mor_to_thunkable_wrapped_mor f.
  Proof.
    apply invmap_eq, pathsinv0, thunkable_mor_from_to_thunkable_wrapped_mor.
  Qed.

  (** *** The adjoint equivalence I ⊣ ⇑ : D ₗ ⟶ D⁻ₗ *)

  Lemma nathomweq_linear_delayed_mor
    : natural_hom_weq
        (negative_linear_category_to_linear_category D)
        (upshift_linear_to_negative_linear D).
  Proof.
    use tpair. {
      cbn; intros a b.
      intermediate_weq (linear_delayed_mor a b).
      - apply invweq, weq_linear_delayed_mor.
      - apply invweq,
          (weq_from_fully_faithful (fully_faithful_negative_linear_category_to_linear_and_thunkable_category D) a (⇑b)).
    }
    use make_dirprod.
    - cbn; intros a b f c g.
      do 2 apply carrier_eq; cbn.
      transparent assert (g' : (thunkable_mor c a)). {
        use (make_thunkable_mor (pr11 g)).
        apply is_thunkable_of_negative, a.
      }
      set (H := hom_natural_precomp nathomweq_delayed_mor a b f c g').
      apply base_paths in H.
      apply H.
    - cbn; intros a b f c g.
      do 2 apply carrier_eq; cbn.
      set (H := hom_natural_postcomp nathomweq_delayed_mor a b f c g).
      apply base_paths in H.
      apply H.
  Defined.

  Lemma are_adjoints_upshift_linear_to_negative_linear_inclusion
    : are_adjoints
        (negative_linear_category_to_linear_category D)
        (upshift_linear_to_negative_linear D).
  Proof.
    apply adj_from_nathomweq, nathomweq_linear_delayed_mor.
  Defined.

  Lemma forms_equivalence_upshift_linear_to_negative_linear
    : forms_equivalence are_adjoints_upshift_linear_to_negative_linear_inclusion.
  Proof.
    use make_forms_equivalence.
    - intro a.
      exists (force _,,tt).
      use make_is_inverse_in_precat.
      + do 2 apply carrier_eq.
        apply delay_force_right.
      + do 2 apply carrier_eq.
        refine (_ @ force_delay_id _).
        apply cancel_precomposition, magmoid_id_left.
    - intro a.
      exists (delay _).
      use make_is_inverse_in_precat.
      + apply carrier_eq.
        refine (_ @ force_delay_id _).
        apply cancel_postcomposition, magmoid_id_left.
      + apply carrier_eq.
        refine (_ @ delay_force_id _).
        apply cancel_precomposition, magmoid_id_left.
  Qed.

  Local Lemma adj_equivalence_negative_linear_to_linear
    : adj_equivalence_of_cats (negative_linear_category_to_linear_category D).
  Proof.
    refine (make_adj_equivalence_of_cats _
              (upshift_linear_to_negative_linear D)
              _ _ _
              forms_equivalence_upshift_linear_to_negative_linear).
    apply are_adjoints_upshift_linear_to_negative_linear_inclusion.
  Defined.

  Lemma adj_equivalence_upshift_linear_to_negative_linear
    : adj_equivalence_of_cats (upshift_linear_to_negative_linear D).
  Proof.
    apply (adj_equivalence_of_cats_inv _ adj_equivalence_negative_linear_to_linear).
  Defined.

  (** *** The adjoint equivalence I ⊣ ⇓ : D ₜ ⟶ D⁺ₜ *)
  Lemma nathomweq_thunkable_wrapped_mor
    : natural_hom_weq
        (downshift_thunkable_to_positive_thunkable D)
        (positive_thunkable_category_to_thunkable_category D).
  Proof.
    use tpair. {
      cbn; intros a b.
      intermediate_weq (thunkable_wrapped_mor a b).
      - apply (weq_from_fully_faithful (fully_faithful_positive_thunkable_category_to_linear_and_thunkable_category D) (⇓a) b).
      - apply weq_thunkable_wrapped_mor.
    }
    use make_dirprod.
    - cbn; intros a b f c g.
      apply carrier_eq; cbn.
      transparent assert (f' : (linear_mor (⇓a) b)). {
        use (make_linear_mor (pr11 f)).
        apply is_linear_of_positive, (⇓a).
      }
      apply (hom_natural_precomp nathomweq_wrapped_mor a b f' c g).
    - cbn; intros a b f c g.
      apply carrier_eq; cbn.
      transparent assert (f' : (linear_mor (⇓a) b)). {
        use (make_linear_mor (pr11 f)).
        apply is_linear_of_positive, (⇓a).
      }
      transparent assert (g' : (linear_mor b c)). {
        use (make_linear_mor (pr11 g)).
        apply is_linear_of_positive, b.
      }
      apply (hom_natural_postcomp nathomweq_wrapped_mor a b f' c g').
  Defined.

  Lemma are_adjoints_downshift_thunkable_to_positive_thunkable_inclusion
    : are_adjoints
        (downshift_thunkable_to_positive_thunkable D)
        (positive_thunkable_category_to_thunkable_category D).
  Proof.
    apply adj_from_nathomweq, nathomweq_thunkable_wrapped_mor.
  Defined.

  Lemma forms_equivalence_downshift_thunkable_to_positive_thunkable
    : forms_equivalence are_adjoints_downshift_thunkable_to_positive_thunkable_inclusion.
  Proof.
    use make_forms_equivalence.
    - intro a.
      exists (unwrap _).
      use make_is_inverse_in_precat.
      + apply carrier_eq.
        refine (_ @ wrap_unwrap_id _).
        apply cancel_postcomposition, magmoid_id_right.
      + apply carrier_eq.
        refine (_ @ unwrap_wrap_id _).
        apply cancel_precomposition, magmoid_id_right.
    - intro a.
      exists (wrap _,,tt).
      use make_is_inverse_in_precat.
      + do 2 apply carrier_eq.
        refine (_ @ unwrap_wrap_id _).
        apply cancel_postcomposition, magmoid_id_right.
      + do 2 apply carrier_eq.
        apply wrap_unwrap_left.
  Qed.

  Lemma adj_equivalence_downshift_thunkable_to_positive_thunkable
    : adj_equivalence_of_cats (downshift_thunkable_to_positive_thunkable D).
  Proof.
    refine (make_adj_equivalence_of_cats _
              (positive_thunkable_category_to_thunkable_category D)
              _ _ _
              forms_equivalence_downshift_thunkable_to_positive_thunkable).
    apply are_adjoints_downshift_thunkable_to_positive_thunkable_inclusion.
  Defined.

  (** *** Wrap, delay, and force as natural isomorphisms. *)

  (** **** Wrap/Unwrap as [nat_z_iso] *)
  Definition unwrap_nat_trans_data
    : nat_trans_data (downshift_thunkable_to_thunkable D) (functor_identity (D ₜ))
    := unwrap (D:=D).
  Definition wrap_nat_trans_data
    : nat_trans_data (functor_identity (D ₜ)) (downshift_thunkable_to_thunkable D)
    := wrap (D:=D).

  Lemma unwrap_is_nat_trans : is_nat_trans _ _ unwrap_nat_trans_data.
  Proof.
    intros a b f.
    apply carrier_eq.
    etrans. 2: apply wrap_unwrap_right.
    apply cancel_postcomposition, (assoc_thunkable _ (unwrap _)).
  Qed.

  Lemma wrap_is_nat_trans : is_nat_trans _ _ wrap_nat_trans_data.
  Proof.
    intros a b f.
    apply carrier_eq, pathsinv0, wrap_unwrap_left.
  Qed.

  Definition unwrap_nat_trans := make_nat_trans _ _ _ unwrap_is_nat_trans.
  Definition wrap_nat_trans := make_nat_trans _ _ _ wrap_is_nat_trans.

  Lemma is_nat_z_iso_wrap : is_nat_z_iso wrap_nat_trans.
  Proof.
    intro a.
    exists (unwrap_nat_trans a).
    use make_is_inverse_in_precat; apply carrier_eq.
    - apply wrap_unwrap_id.
    - apply unwrap_wrap_id.
  Defined.

  Definition wrap_nat_z_iso := make_nat_z_iso _ _ _ is_nat_z_iso_wrap.
  Definition unwrap_nat_z_iso := nat_z_iso_inv wrap_nat_z_iso.

  (** **** Force/Delay as [nat_z_iso] *)

  Definition delay_nat_trans_data
    : nat_trans_data (functor_identity (D ₗ)) (upshift_linear_to_linear D)
    := delay (D:=D).
  Definition force_nat_trans_data
    : nat_trans_data (upshift_linear_to_linear D) (functor_identity (D ₗ))
    := force (D:=D).

  Lemma delay_is_nat_trans
    : is_nat_trans _ _ delay_nat_trans_data.
  Proof.
    intros a b f.
    apply carrier_eq.
    etrans. 1: apply pathsinv0, delay_force_left.
    apply cancel_precomposition, (assoc_linear _ (delay _)).
  Defined.

  Lemma force_is_nat_trans
    : is_nat_trans _ _ force_nat_trans_data.
  Proof.
    intros a b f.
    apply carrier_eq, delay_force_right.
  Defined.

  Definition delay_nat_trans := make_nat_trans _ _ _ delay_is_nat_trans.
  Definition force_nat_trans := make_nat_trans _ _ _ force_is_nat_trans.

  Lemma is_nat_z_iso_force : is_nat_z_iso force_nat_trans.
  Proof.
    intro a.
    exists (delay_nat_trans a).
    use make_is_inverse_in_precat; apply carrier_eq.
    - apply force_delay_id.
    - apply delay_force_id.
  Defined.

  Definition force_nat_z_iso := make_nat_z_iso _ _ _ is_nat_z_iso_force.
  Definition delay_nat_z_iso := nat_z_iso_inv force_nat_z_iso.

End shift_functor_adjunctions.

(** ** 3. Definition and adjunction of the restricted shift functors of a duploid

 The restricted shift functors are ↑ : D⁺ₜ ⟶ D⁻ₗ and ↓ : D⁻ₗ ⟶ D⁺ₜ given by
 restricting ⇑ and ⇓ along the obvious inclusion functors.  This gives rise to a
 different adjunction, ↑ ⊣ ↓ : D⁻ₗ ⟶ D⁺ₜ (by contrast to ⇓ ⊣ ⇑ : D⁺ ⟶ D⁻).

 *)

Section restricted_shift_functors.
  Context (D : duploid).

  Definition upshift_positive_thunkable_to_negative_linear : D⁺ₜ ⟶ D⁻ₗ
    := positive_thunkable_category_to_linear_category D ∙ upshift_linear_to_negative_linear D.
  Definition downshift_negative_linear_to_positive_thunkable : D⁻ₗ ⟶ D⁺ₜ
    := negative_linear_category_to_thunkable_category D ∙ downshift_thunkable_to_positive_thunkable D.

  Lemma are_adjoints_upshift_downshift_negative_linear_to_positive_thunkable
    : are_adjoints
        upshift_positive_thunkable_to_negative_linear
        downshift_negative_linear_to_positive_thunkable.
  Proof.
    use make_are_adjoints.
    - use make_nat_trans.

  Abort.

End restricted_shift_functors.

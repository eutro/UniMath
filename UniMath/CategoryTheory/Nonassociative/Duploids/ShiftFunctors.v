(********************************************************************************

 Shift Functors of a Duploid

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition of the shift functors of a duploid
 2. Adjunctions of the shift functors of a duploid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

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

(** ** 3. Adjunctions of the shift functors of a duploid *)
Section shift_functor_adjunctions.
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

End shift_functor_adjunctions.

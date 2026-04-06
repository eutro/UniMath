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
Require Import UniMath.CategoryTheory.Adjunctions.HomIsos.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.ShiftFacts.
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

 Where all but the right ↓ arrows are functorial.

 *)

Definition upshiftf {D : duploid} {a b : D} (f : a --> b) : ⇑a --> ⇑b := (force a · f) · delay b.
Definition downshiftf {D : duploid} {a b : D} (f : a --> b) : ⇓a --> ⇓b := unwrap a · (f · wrap b).

Remark downshiftf_from_lift {D : duploid} {a b : D} (f : a --> b)
  : downshiftf f = positive_lift (f · wrap b).
Proof. reflexivity. Defined.

Remark upshiftf_from_lift {D : duploid} {a b : D} (f : a --> b)
  : upshiftf f = negative_lift (force a · f).
Proof. reflexivity. Defined.

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
    do 2 rewrite (assoc_negative _ (⇑b)).
    rewrite delay_force_right.
    now rewrite (assoc_linear _ H).
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

  Definition upshift_data_'_to_negative : functor_data D (D⁻).
  Proof.
    use make_functor_data.
    - apply upshift.
    - intros a b f; apply (upshiftf' f,,tt).
  Defined.

  Definition upshift_'_to_negative : D ⟶¹ (D⁻).
  Proof.
    apply (make_rxfunctor upshift_data_'_to_negative).
    abstract (intro a; do 2 (apply carrier_eq); apply upshiftf_id).
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
  Definition upshift_linear_to_linear_and_thunkable : D ₗ ⟶ D ₗₜ
    := upshift_linear_to_negative_linear ∙ negative_linear_category_to_linear_and_thunkable_category D.
  Definition upshift_linear_and_thunkable_to_linear_and_thunkable : D ₗₜ ⟶ D ₗₜ
    := linear_and_thunkable_category_to_linear_category D ∙ upshift_linear_to_linear_and_thunkable.
  Definition upshift_positive_thunkable_to_negative_linear : D⁺ₜ ⟶ D⁻ₗ
    := positive_thunkable_category_to_linear_category D ∙ upshift_linear_to_negative_linear.

  (** These reflexive graph functors are useful for defining the adjunctions below. *)
  Definition upshift_'_to_thunkable : D ⟶¹ (D ₜ)
    := rxfunctor_compose upshift_'_to_negative
         (negative_category_to_thunkable_category D).
  Definition upshift_'_to_' : D ⟶¹ D
    := rxfunctor_compose upshift_'_to_thunkable
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
    do 2 rewrite (assoc'_positive _ (⇓b)).
    rewrite wrap_unwrap_left.
    now rewrite (assoc'_thunkable _ H).
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

  Definition downshift_data_'_to_positive : functor_data D (D⁺).
  Proof.
    use make_functor_data.
    - apply downshift.
    - intros a b f; apply (downshiftf' f,,tt).
  Defined.

  Definition downshift_'_to_positive : D ⟶¹ (D⁺).
  Proof.
    apply (make_rxfunctor downshift_data_'_to_positive).
    abstract (intro a; do 2 (apply carrier_eq); apply downshiftf_id).
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
  Definition downshift_thunkable_to_linear_and_thunkable : D ₜ ⟶ D ₗₜ
    := downshift_thunkable_to_positive_thunkable ∙ positive_thunkable_category_to_linear_and_thunkable_category D.
  Definition downshift_linear_and_thunkable_to_linear_and_thunkable : D ₗₜ ⟶ D ₗₜ
    := linear_and_thunkable_category_to_thunkable_category D ∙ downshift_thunkable_to_linear_and_thunkable.
  Definition downshift_negative_linear_to_positive_thunkable : D⁻ₗ ⟶ D⁺ₜ
    := negative_linear_category_to_thunkable_category D ∙ downshift_thunkable_to_positive_thunkable.

  (** These reflexive graph functors are useful for defining the adjunctions below. *)
  Definition downshift_'_to_linear : D ⟶¹ (D ₗ)
    := rxfunctor_compose downshift_'_to_positive
         (positive_category_to_linear_category D).
  Definition downshift_'_to_' : D ⟶¹ D
    := rxfunctor_compose downshift_'_to_linear
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

  <<
       Dₗ⟦⇓a, b⟧ ≃ D⟦⇓a, b⟧
                 ≃ D⟦a, b⟧
                 ≃ D⟦a, ⇑b⟧ ≃ Dₜ⟦a, ⇑b⟧
  >>

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
Local Notation "F '⟸' G" := (nat_trans G F) (at level 39).
  (* type in Emacs using agda-input with \l * *)
Local Notation "F '⟹' G" := (nat_trans F G) (at level 39).
  (* type in Emacs using agda-input with \r * *)

Section shift_functor_adjunctions.
  Context (D : duploid).

  (** *** Natural transformations [wrap]/[unwrap]/[force]/[delay] *)

  (* All of the naturality goals below are equations through subtypes of D-morphisms.  I prove first
     those on D-morphisms, and then use this tactic to ignore the subtypes with [carrier_eq]. *)
  Local Tactic Notation "carrier_naturality" int_or_var(ncarriers) constr(naturality_lemma) :=
    abstract (intros a b f; do ncarriers apply carrier_eq; apply naturality_lemma).

  (** Naturality of [wrap] *)
  Lemma wrap_natural (a b : D) (f : D⟦a, b⟧)
    : f · wrap b = wrap a · #⇓ f.
  Proof. apply pathsinv0, wrap_unwrap_left. Qed.

  (** Naturality of [unwrap] *)
  Lemma unwrap_natural (a b : D) (f : D⟦a, b⟧)
    : #⇓ f · unwrap b = unwrap a · f.
  Proof.
    apply positive_lift_unique.
    etrans; [apply assoc_thunkable, (wrap _)|].
    etrans; [apply cancel_postcomposition, positive_lift_factors|].
    apply wrap_unwrap_right.
  Qed.

  (** Naturality of [force] *)
  Lemma force_natural (a b : D) (f : D⟦a, b⟧)
    : #⇑ f · force b = force a · f.
  Proof. apply delay_force_right. Qed.

  (** Naturality of [delay] *)
  Lemma delay_natural (a b : D) (f : D⟦a, b⟧)
    : f · delay b = delay a · #⇑ f.
  Proof.
    apply pathsinv0, negative_lift_unique.
    etrans; [apply assoc'_linear, (force _)|].
    etrans; [apply cancel_precomposition, negative_lift_factors|].
    apply delay_force_left.
  Qed.

  (** **** [wrap] as natural transformations *)
  Definition wrap_' : functor_identity D ⟹ downshift_'_to_' D.
  Proof.
    use make_nat_trans.
    - intro a; apply wrap.
    - carrier_naturality 0 wrap_natural.
  Defined.

  Definition wrap_positive_thunkable
    : functor_identity (D⁺ₜ) ⟹ downshift_positive_thunkable_to_positive_thunkable D.
  Proof.
    use make_nat_trans.
    - intro a; apply (wrap _,,tt).
    - carrier_naturality 2 wrap_natural.
  Defined.

  Definition wrap_thunkable
    : functor_identity (D ₜ) ⟹ downshift_thunkable_to_thunkable D.
  Proof.
    use make_nat_trans.
    - intro a; apply wrap.
    - carrier_naturality 1 wrap_natural.
  Defined.

  (** **** [unwrap] as natural transformations *)
  Definition unwrap_' : functor_identity D ⟸ downshift_'_to_' D.
  Proof.
    use make_nat_trans.
    - intro a; apply unwrap.
    - carrier_naturality 0 unwrap_natural.
  Defined.

  Definition unwrap_positive_thunkable
    : functor_identity (D⁺ₜ) ⟸ downshift_positive_thunkable_to_positive_thunkable D.
  Proof.
    use make_nat_trans.
    - intro a; apply (unwrap _,,tt).
    - carrier_naturality 2 unwrap_natural.
  Defined.

  Definition unwrap_thunkable
    : functor_identity (D ₜ) ⟸ downshift_thunkable_to_thunkable D.
  Proof.
    use make_nat_trans.
    - intro a; apply unwrap.
    - carrier_naturality 1 unwrap_natural.
  Defined.

  Definition unwrap_linear_and_thunkable
    : functor_identity (D ₗₜ) ⟸ downshift_linear_and_thunkable_to_linear_and_thunkable D.
  Proof.
    use make_nat_trans.
    - intro a.
      apply (make_linear_and_thunkable_mor_from_thunkable (unwrap a)).
      apply is_linear_of_positive, (⇓_).
    - carrier_naturality 1 unwrap_natural.
  Defined.

  (** **** [force] as natural transformations *)
  Definition force_' : functor_identity D ⟸ upshift_'_to_' D.
  Proof.
    use make_nat_trans.
    - intro a; apply force.
    - carrier_naturality 0 force_natural.
  Defined.

  Definition force_negative_linear
    : functor_identity (D⁻ₗ) ⟸ upshift_negative_linear_to_negative_linear D.
  Proof.
    use make_nat_trans.
    - intro a; apply (force _,,tt).
    - carrier_naturality 2 force_natural.
  Defined.

  Definition force_linear
    : functor_identity (D ₗ) ⟸ upshift_linear_to_linear D.
  Proof.
    use make_nat_trans.
    - intro a; apply force.
    - carrier_naturality 1 force_natural.
  Defined.

  (** **** [delay] as natural transformations *)
  Definition delay_' : functor_identity D ⟹ upshift_'_to_' D.
  Proof.
    use make_nat_trans.
    - intro a; apply delay.
    - carrier_naturality 0 delay_natural.
  Defined.

  Definition delay_negative_linear
    : functor_identity (D⁻ₗ) ⟹ upshift_negative_linear_to_negative_linear D.
  Proof.
    use make_nat_trans.
    - intro a; apply (delay _,,tt).
    - carrier_naturality 2 delay_natural.
  Defined.

  Definition delay_linear
    : functor_identity (D ₗ) ⟹ upshift_linear_to_linear D.
  Proof.
    use make_nat_trans.
    - intro a; apply delay.
    - carrier_naturality 1 delay_natural.
  Defined.

  Definition delay_linear_and_thunkable
    : functor_identity (D ₗₜ) ⟹ upshift_linear_and_thunkable_to_linear_and_thunkable D.
  Proof.
    use make_nat_trans.
    - intro a.
      apply (make_linear_and_thunkable_mor_from_linear (delay a)).
      apply is_thunkable_of_negative, (⇑_).
    - carrier_naturality 1 delay_natural.
  Defined.

  (** *** Adjoint equivalences *)

  (** I ⊣ ⇓ : Dₜ ≃ D⁺ₜ *)
  Definition downshift_thunkable_to_positive_thunkable_adjunction_data : adjunction_data (D⁺ₜ) (D ₜ).
  Proof.
    use make_adjunction_data.
    - apply positive_thunkable_category_to_thunkable_category.
    - apply downshift_thunkable_to_positive_thunkable.
    - apply wrap_positive_thunkable.
    - apply unwrap_thunkable.
  Defined.

  Definition downshift_thunkable_to_positive_thunkable_form_adjunction
    : form_adjunction' downshift_thunkable_to_positive_thunkable_adjunction_data.
  Proof.
    apply make_form_adjunction.
    - intro a; apply carrier_eq, wrap_unwrap_id.
    - intro a; do 2 apply carrier_eq; cbn.
      etrans; [apply positive_lift_factors|].
      apply unwrap_wrap_id.
  Qed.

  Lemma downshift_thunkable_to_positive_thunkable_are_adjoints
    : are_adjoints (positive_thunkable_category_to_thunkable_category D)
        (downshift_thunkable_to_positive_thunkable D).
  Proof.
    apply (make_are_adjoints _ _ _ _ downshift_thunkable_to_positive_thunkable_form_adjunction).
  Defined.

  Lemma downshift_thunkable_to_positive_thunkable_is_equivalence
    : adj_equivalence_of_cats (downshift_thunkable_to_positive_thunkable D).
  Proof.
    use adj_equivalence_from_right_adjoint.
    - eapply are_adjoints_to_is_right_adjoint,
        downshift_thunkable_to_positive_thunkable_are_adjoints.
    - abstract (intro a; exists (unwrap (pr1 a),,tt);
                split; do 2 apply carrier_eq; apply are_inverses_unwrap_wrap).
    - abstract (intro a; exists (wrap a);
                split; apply carrier_eq, are_inverses_unwrap_wrap).
  Defined.

  (** I ⊣ ⇑ : Dₗ ≃ D⁻ₗ *)
  Definition upshift_linear_to_negative_linear_adjunction_data : adjunction_data (D ₗ) (D⁻ₗ).
  Proof.
    use make_adjunction_data.
    - apply upshift_linear_to_negative_linear.
    - apply negative_linear_category_to_linear_category.
    - apply delay_linear.
    - apply force_negative_linear.
  Defined.

  Definition upshift_linear_to_negative_linear_form_adjunction
    : form_adjunction' upshift_linear_to_negative_linear_adjunction_data.
  Proof.
    apply make_form_adjunction.
    - intro a; do 2 apply carrier_eq.
      etrans; [apply negative_lift_factors|].
      apply force_delay_id.
    - intro a; apply carrier_eq, delay_force_id.
  Qed.

  Lemma upshift_linear_to_negative_linear_are_adjoints
    : are_adjoints (upshift_linear_to_negative_linear D)
        (negative_linear_category_to_linear_category D).
  Proof.
    apply (make_are_adjoints _ _ _ _ upshift_linear_to_negative_linear_form_adjunction).
  Defined.

  Lemma upshift_linear_to_negative_linear_is_equivalence
    : adj_equivalence_of_cats (upshift_linear_to_negative_linear D).
  Proof.
    eapply make_adj_equivalence_of_cats; [| split].
    - apply upshift_linear_to_negative_linear_form_adjunction.
    - abstract (intro a; exists (force a);
                split; apply carrier_eq, are_inverses_force_delay).
    - abstract (intro a; exists (delay (pr1 a),,tt);
                split; do 2 apply carrier_eq; apply are_inverses_force_delay).
  Defined.

  (** *** Adjunction ⇓ ⊣ ⇑ : Dₗ ⟶ Dₜ *)

  (** Triangle equations of [wrap]/[unwrap] for the would-be-adjunction Dₗ⟦⇓a, b⟧ ≃ D⟦a, b⟧ *)
  Lemma triangle_1_wrap_unwrap_' (a : D)
    : #⇓(wrap a) · unwrap (⇓a) = identity (⇓a).
  Proof.
    apply (is_epi_wrap' D D).
    etrans; [apply assoc_positive, (⇓_)|].
    etrans; [apply cancel_postcomposition, positive_lift_factors|].
    refine (_ @ !magmoid_id_right _).
    apply wrap_unwrap_right.
  Qed.
  (* Note: triangle_2 is just wrap_unwrap_id *)

  (** Triangle equations of [force]/[delay] for the would-be-adjunction Dₜ⟦a, ⇑b⟧ ≃ D⟦a, b⟧ *)
  Lemma triangle_2_delay_force_' (a : D)
    : #⇑(force a) ∘ delay (⇑a) = identity (⇑a).
  Proof.
    apply (is_monic_force' D D).
    etrans; [apply assoc'_negative, (⇑_)|].
    etrans; [apply cancel_precomposition, negative_lift_factors|].
    refine (_ @ !magmoid_id_left _).
    apply delay_force_left.
  Qed.
  (* Note: triangle_1 is just delay_force_id *)

  (** D⟦⇓a, b⟧ ≃ D⟦a, b⟧ : D × D *)
  Lemma downshift_hom_weq_'_'
    : bi_hom_weq
        (downshift_'_to_' D)
        (functor_identity D)
        (functor_identity D)
        (functor_identity D).
  Proof.
    intros a b.
    use weq_iso.
    - intro f.
      apply (wrap _ · f).
    - intro f.
      apply (positive_lift f).
    - abstract (intro f; now apply pathsinv0, positive_lift_unique).
    - abstract (intro f; apply positive_lift_factors).
  Defined.

  Lemma downshift_homweq_'_'_precomp_law
    : bi_hom_weq_precomp_law downshift_hom_weq_'_'.
  Proof.
    intros a b f c h.
    etrans; [apply assoc_thunkable, (wrap _)|].
    etrans; [apply cancel_postcomposition, positive_lift_factors|].
    apply assoc'_positive, (⇓_).
  Qed.

  Lemma downshift_homweq_'_'_postcomp_law
    : bi_hom_weq_postcomp_law downshift_hom_weq_'_'.
  Proof.
    intros a b f c h.
    apply assoc_thunkable, (wrap _).
  Qed.

  Lemma downshift_nathomweq_'_'
    : natural_bi_hom_weq
        (downshift_'_to_' D)
        (functor_identity D)
        (functor_identity D)
        (functor_identity D).
  Proof.
    use make_natural_bi_hom_weq.
    - apply downshift_hom_weq_'_'.
    - apply downshift_homweq_'_'_precomp_law.
    - apply downshift_homweq_'_'_postcomp_law.
  Defined.

  (** Dₗ⟦⇓a, b⟧ ≃ D⟦a, b⟧ : Dₜ × Dₗ *)
  Lemma downshift_nathomweq_linear_'_left
    : natural_bi_hom_weq
        (downshift_thunkable_to_linear D)
        (functor_identity (D ₗ))
        (thunkable_category_to_unital_magmoid D)
        (linear_category_to_unital_magmoid D).
  Proof.
    use make_natural_bi_hom_weq.
    - intros a b; cbn.
      intermediate_weq (D⟦⇓a, b⟧).
      + apply weq_linear_mor_of_positive, (⇓_).
      + apply downshift_hom_weq_'_'.
    - abstract (intros a b f c h; apply downshift_homweq_'_'_precomp_law).
    - abstract (intros a b f c h; apply downshift_homweq_'_'_postcomp_law).
  Defined.

  (** D⁺⟦⇓a, b⟧ ≃ D⟦a, b⟧ : D⁻ × D⁺ *)
  Lemma downshift_nathomweq_positive_'_left
    : natural_bi_hom_weq
        (downshift_negative_to_positive D)
        (functor_identity (D⁺))
        (negative_category_to_thunkable_category D ∙ thunkable_category_to_unital_magmoid D)
        (positive_category_to_linear_category D ∙ linear_category_to_unital_magmoid D).
  Proof.
    use make_natural_bi_hom_weq.
    - intros a b; cbn.
      eapply weqcomp; [apply weqtotalsubtype|].
      apply (natural_bi_hom_weq_to_weq downshift_nathomweq_linear_'_left).
    - abstract (intros a b f c h; apply downshift_homweq_'_'_precomp_law).
    - abstract (intros a b f c h; apply downshift_homweq_'_'_postcomp_law).
  Defined.

  (** D⟦a, ⇑b⟧ ≃ D⟦a, b⟧ : D × Dᵒᵖ ⟶¹ Set *)
  Lemma upshift_hom_weq_'_'
    : bi_hom_weq
        (functor_identity D)
        (upshift_'_to_' D)
        (functor_identity D)
        (functor_identity D).
  Proof.
    intros a b.
    use weq_iso.
    - intro f.
      apply (force _ ∘ f).
    - intro f.
      apply (negative_lift f).
    - abstract (intro f; now apply pathsinv0, negative_lift_unique).
    - abstract (intro f; apply negative_lift_factors).
  Defined.

  Lemma upshift_homweq_'_'_postcomp_law
    : bi_hom_weq_postcomp_law upshift_hom_weq_'_'.
  Proof.
    intros a b f c h.
    etrans; [apply assoc'_linear, (force _)|].
    etrans; [apply cancel_precomposition, negative_lift_factors|].
    apply assoc_negative, (⇑_).
  Qed.

  Lemma upshift_homweq_'_'_precomp_law
    : bi_hom_weq_precomp_law upshift_hom_weq_'_'.
  Proof.
    intros a b f c h.
    apply assoc'_linear, (force _).
  Qed.

  Lemma upshift_nathomweq_'_'
    : natural_bi_hom_weq
        (functor_identity D)
        (upshift_'_to_' D)
        (functor_identity D)
        (functor_identity D).
  Proof.
    use make_natural_bi_hom_weq.
    - apply upshift_hom_weq_'_'.
    - apply upshift_homweq_'_'_precomp_law.
    - apply upshift_homweq_'_'_postcomp_law.
  Defined.

  (** Dₜ⟦a, ⇑b⟧ ≃ D⟦a, b⟧ : Dₜ × Dₗ *)
  Lemma upshift_nathomweq_thunkable_'_right
    : natural_bi_hom_weq
        (functor_identity (D ₜ))
        (upshift_linear_to_thunkable D)
        (thunkable_category_to_unital_magmoid D)
        (linear_category_to_unital_magmoid D).
  Proof.
    use make_natural_bi_hom_weq.
    - intros a b; cbn.
      intermediate_weq (D⟦a, ⇑b⟧).
      + apply weq_thunkable_mor_of_negative, (⇑_).
      + apply upshift_hom_weq_'_'.
    - abstract (intros a b f c h; apply upshift_homweq_'_'_precomp_law).
    - abstract (intros a b f c h; apply upshift_homweq_'_'_postcomp_law).
  Defined.

  (** D⁻⟦a, ⇑b⟧ ≃ D⟦a, b⟧ : D⁺ × D⁻ *)
  Lemma upshift_nathomweq_negative_'_right
    : natural_bi_hom_weq
        (functor_identity (D⁻))
        (upshift_positive_to_negative D)
        (negative_category_to_thunkable_category D ∙ thunkable_category_to_unital_magmoid D)
        (positive_category_to_linear_category D ∙ linear_category_to_unital_magmoid D).
  Proof.
    use make_natural_bi_hom_weq.
    - intros a b; cbn.
      eapply weqcomp; [apply weqtotalsubtype|].
      apply (natural_bi_hom_weq_to_weq upshift_nathomweq_thunkable_'_right).
    - abstract (intros a b f c h; apply upshift_homweq_'_'_precomp_law).
    - abstract (intros a b f c h; apply upshift_homweq_'_'_postcomp_law).
  Defined.

  (** Helper for changing the units of these adjunctions.
      This undercuts computing all of the [invmap]s that [adj_from_nathomweq] produces, and also
      lets me remove the ugly identity morphisms that it leaves. *)
  Lemma are_adjoints_change_units {C₁ C₂ : precategory}
    (L : functor C₂ C₁) (R : functor C₁ C₂)
    (θ : are_adjoints L R)
    (η : nat_trans_data (functor_identity C₂) (functor_composite L R))
    (Hη : η = adjunit θ)
    (ε : nat_trans_data (functor_composite R L) (functor_identity C₁))
    (Hε : ε = adjcounit θ)
    : are_adjoints L R.
  Proof.
    use make_are_adjoints.
    - apply (make_nat_trans _ _ η).
      abstract (rewrite Hη; exact (nat_trans_ax (adjunit θ))).
    - apply (make_nat_trans _ _ ε).
      abstract (rewrite Hε; exact (nat_trans_ax (adjcounit θ))).
    - abstract (
          change ((∏ a : C₂, # L (η a) · ε (L a) = identity (L a)) × (∏ b : C₁, η (R b) · # R (ε b) = identity (R b)));
          rewrite Hε, Hη;
          exact (pr2 θ)).
  Defined.

  (** D⟦⇓a, b⟧ ≃ D⟦a, ⇑b⟧ : D × Dᵒᵖ *)
  Definition upshift_downshift_nathomweq_'_to_'
    : natural_hom_weq (downshift_'_to_' D) (upshift_'_to_' D)
    := natural_bi_hom_weq_compose
         downshift_nathomweq_'_' (natural_bi_hom_weq_inv upshift_nathomweq_'_').

  (** Dₗ⟦⇓a, b⟧ ≃ Dₜ⟦a, ⇑b⟧ : Dₜ × Dₗᵒᵖ *)
  Definition upshift_downshift_nathomweq_linear_to_thunkable
    : natural_hom_weq (downshift_thunkable_to_linear D) (upshift_linear_to_thunkable D)
    := natural_bi_hom_weq_compose
         downshift_nathomweq_linear_'_left (natural_bi_hom_weq_inv upshift_nathomweq_thunkable_'_right).

  Definition adjunction_upshift_downshift_linear_to_thunkable
    : are_adjoints (downshift_thunkable_to_linear D) (upshift_linear_to_thunkable D).
  Proof.
    use are_adjoints_change_units.
    - apply (adj_from_nathomweq upshift_downshift_nathomweq_linear_to_thunkable).
    - intro a; exact (negative_lift (wrap a)).
    - abstract (apply funextsec; intro a; apply carrier_eq; simpl;
                apply (maponpaths (λ f, negative_lift' D D f));
                apply pathsinv0, magmoid_id_right).
    - intro a; exact (positive_lift (force a)).
    - abstract (apply funextsec; intro a; apply carrier_eq; simpl;
                apply (maponpaths (λ f, positive_lift' D D f));
                apply pathsinv0, magmoid_id_left).
  Defined.

  (** D⁺⟦⇓a, b⟧ ≃ D⁻⟦a, ⇑b⟧ : D⁻ × D⁺ᵒᵖ *)
  Definition upshift_downshift_nathomweq_positive_to_negative
    : natural_hom_weq (downshift_negative_to_positive D) (upshift_positive_to_negative D)
    := natural_bi_hom_weq_compose
         downshift_nathomweq_positive_'_left (natural_bi_hom_weq_inv upshift_nathomweq_negative_'_right).

  Definition adjunction_upshift_downshift_positive_to_negative
    : are_adjoints (downshift_negative_to_positive D) (upshift_positive_to_negative D).
  Proof.
    use are_adjoints_change_units.
    - apply (adj_from_nathomweq upshift_downshift_nathomweq_positive_to_negative).
    - intro a; cbn in a.
      exact (negative_lift (wrap a),,tt).
    - abstract (apply funextsec; intro a; do 2 apply carrier_eq; simpl;
                apply (maponpaths (λ f, negative_lift' D D f));
                apply pathsinv0, magmoid_id_right).
    - intro a; cbn in a.
      exact (positive_lift (force a),,tt).
    - abstract (apply funextsec; intro a; do 2 apply carrier_eq; simpl;
                apply (maponpaths (λ f, positive_lift' D D f));
                apply pathsinv0, magmoid_id_left).
  Defined.

End shift_functor_adjunctions.

(** ** 3. Definition and adjunction of the restricted shift functors of a duploid

 The restricted shift functors are ↑ : D⁺ₜ ⟶ D⁻ₗ and ↓ : D⁻ₗ ⟶ D⁺ₜ given by
 restricting ⇑ and ⇓ along the obvious inclusion functors.  This gives rise to a
 different adjunction, ↑ ⊣ ↓ : D⁻ₗ ⟶ D⁺ₜ (by contrast to ⇓ ⊣ ⇑ : D⁺ ⟶ D⁻).

 *)

Section restricted_shift_functors.
  Context (D : duploid).

  Definition downshift_hom_weq_linear_and_thunkable_positive_thunkable
    : bi_hom_weq
        (positive_thunkable_category_to_linear_and_thunkable_category D)
        (functor_identity (D ₗₜ))
        (functor_identity (D ⁺ₜ))
        (linear_and_thunkable_category_to_thunkable_category D ∙ downshift_thunkable_to_positive_thunkable D).
  Proof.
    set (ADJ := (downshift_thunkable_to_positive_thunkable_are_adjoints D)).
    intros a b.
    eapply weqcomp.
    - apply weq_linear_and_thunkable_mor_to_thunkable_mor, a.
    - exact (adjunction_hom_weq ADJ _ _).
  Defined.

  Lemma downshift_hom_weq_linear_and_thunkable_positive_thunkable_precomp_law
    : bi_hom_weq_precomp_law downshift_hom_weq_linear_and_thunkable_positive_thunkable.
  Proof.
    set (ADJ := (downshift_thunkable_to_positive_thunkable_are_adjoints D)).
    intros a b f c h.
    do 2 apply carrier_eq.
    cbn in a, b, c, f, h |- *.
    set (H := φ_adj_natural_precomp ADJ a b (f : thunkable_mor _ _) c h).
    do 2 apply base_paths in H.
    exact H.
  Qed.

  Lemma downshift_hom_weq_linear_and_thunkable_positive_thunkable_postcomp_law
    : bi_hom_weq_postcomp_law downshift_hom_weq_linear_and_thunkable_positive_thunkable.
  Proof.
    set (ADJ := (downshift_thunkable_to_positive_thunkable_are_adjoints D)).
    intros a b f c h.
    do 2 apply carrier_eq.
    cbn in a, b, c, f, h |- *.
    set (H := φ_adj_natural_postcomp ADJ a b (f : thunkable_mor _ _) c (h : thunkable_mor _ _)).
    do 2 apply base_paths in H.
    exact H.
  Qed.

  Definition downshift_nat_hom_weq_linear_and_thunkable_positive_thunkable
    := make_natural_bi_hom_weq _
         downshift_hom_weq_linear_and_thunkable_positive_thunkable_precomp_law
         downshift_hom_weq_linear_and_thunkable_positive_thunkable_postcomp_law.

  Definition upshift_hom_weq_linear_and_thunkable_negative_linear
    : bi_hom_weq
        (linear_and_thunkable_category_to_linear_category D
           ∙ upshift_linear_to_negative_linear D)
        (functor_identity (D ⁻ₗ))
        (functor_identity (D ₗₜ))
        (negative_linear_category_to_linear_and_thunkable_category D).
  Proof.
    set (ADJ := (upshift_linear_to_negative_linear_are_adjoints D)).
    intros a b.
    eapply weqcomp.
    - exact (adjunction_hom_weq ADJ _ _).
    - apply invweq, weq_linear_and_thunkable_mor_to_linear_mor, b.
  Defined.

  Lemma upshift_hom_weq_linear_and_thunkable_negative_linear_precomp_law
    : bi_hom_weq_precomp_law upshift_hom_weq_linear_and_thunkable_negative_linear.
  Proof.
    set (ADJ := (upshift_linear_to_negative_linear_are_adjoints D)).
    intros a b f c h.
    apply carrier_eq.
    cbn in a, b, c, h |- *.
    set (H := φ_adj_natural_precomp ADJ a b f c (h : linear_mor _ _)).
    apply base_paths in H.
    exact H.
  Qed.

  Lemma upshift_hom_weq_linear_and_thunkable_negative_linear_postcomp_law
    : bi_hom_weq_postcomp_law upshift_hom_weq_linear_and_thunkable_negative_linear.
  Proof.
    set (ADJ := (upshift_linear_to_negative_linear_are_adjoints D)).
    intros a b f c h.
    apply carrier_eq.
    cbn in a, b, c, h |- *.
    set (H := φ_adj_natural_postcomp ADJ a b f c h).
    apply base_paths in H.
    exact H.
  Qed.

  Definition upshift_nat_hom_weq_linear_and_thunkable_negative_linear
    := make_natural_bi_hom_weq _
         upshift_hom_weq_linear_and_thunkable_negative_linear_precomp_law
         upshift_hom_weq_linear_and_thunkable_negative_linear_postcomp_law.

  Definition nat_hom_weq_upshift_downshift_negative_linear_to_positive_thunkable
    : natural_hom_weq
        (upshift_positive_thunkable_to_negative_linear D)
        (downshift_negative_linear_to_positive_thunkable D)
    := natural_bi_hom_weq_hcomp
         downshift_nat_hom_weq_linear_and_thunkable_positive_thunkable
         upshift_nat_hom_weq_linear_and_thunkable_negative_linear.

  Lemma are_adjoints_upshift_downshift_negative_linear_to_positive_thunkable
    : are_adjoints
        (upshift_positive_thunkable_to_negative_linear D)
        (downshift_negative_linear_to_positive_thunkable D).
  Proof.
    use are_adjoints_change_units.
    - use adj_from_nathomweq.
      exact (natural_bi_hom_weq_hcomp
               downshift_nat_hom_weq_linear_and_thunkable_positive_thunkable
               upshift_nat_hom_weq_linear_and_thunkable_negative_linear).
    - intro a; cbn in a.
      refine (make_thunkable_mor (delay a · wrap (⇑a)) _,,tt).
      abstract (apply is_thunkable_compose;
                first [ apply is_thunkable_delay
                      | apply (wrap _) ]).
    - abstract (apply funextsec; intro a; do 2 apply carrier_eq; simpl;
                apply pathsinv0; etrans; [apply positive_lift_factors|];
                apply cancel_postcomposition, magmoid_id_right).
    - intro a; cbn in a.
      refine (make_linear_mor (force (⇓a) · unwrap a) _,,tt).
      abstract (apply is_linear_compose;
                first [ apply is_linear_unwrap
                      | apply (force _) ]).
    - abstract (apply funextsec; intro a; do 2 apply carrier_eq; simpl;
                apply pathsinv0; etrans; [apply negative_lift_factors|];
                apply cancel_precomposition, magmoid_id_left).
  Defined.

End restricted_shift_functors.

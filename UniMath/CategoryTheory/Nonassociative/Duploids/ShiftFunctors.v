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

 Where all but the right ↓ arrows are functorial.

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
  Definition upshift_linear_to_linear_and_thunkable : D ₗ ⟶ D ₗₜ
    := upshift_linear_to_negative_linear ∙ negative_linear_category_to_linear_and_thunkable_category D.
  Definition upshift_linear_and_thunkable_to_linear_and_thunkable : D ₗₜ ⟶ D ₗₜ
    := linear_and_thunkable_category_to_linear_category D ∙ upshift_linear_to_linear_and_thunkable.

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
  Definition downshift_thunkable_to_linear_and_thunkable : D ₜ ⟶ D ₗₜ
    := downshift_thunkable_to_positive_thunkable ∙ positive_thunkable_category_to_linear_and_thunkable_category D.
  Definition downshift_linear_and_thunkable_to_linear_and_thunkable : D ₗₜ ⟶ D ₗₜ
    := linear_and_thunkable_category_to_thunkable_category D ∙ downshift_thunkable_to_linear_and_thunkable.

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
    unfold downshiftf.
    rewrite (assoc'_thunkable _ (unwrap _)).
    apply cancel_precomposition.
    rewrite (assoc'_positive _ (⇓_)), wrap_unwrap_id.
    apply magmoid_id_right.
  Qed.

  (** Naturality of [force] *)
  Lemma force_natural (a b : D) (f : D⟦a, b⟧)
    : #⇑ f · force b = force a · f.
  Proof. apply delay_force_right. Qed.

  (** Naturality of [delay] *)
  Lemma delay_natural (a b : D) (f : D⟦a, b⟧)
    : f · delay b = delay a · #⇑ f.
  Proof.
    unfold upshiftf.
    rewrite (assoc_linear _ (delay _)).
    apply cancel_postcomposition.
    rewrite (assoc_negative _ (⇑_)), delay_force_id.
    apply pathsinv0, magmoid_id_left.
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
    - intro a; do 2 apply carrier_eq.
      refine (wrap_unwrap_left _ @ _).
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
      refine (delay_force_right _ @ _).
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
    unfold downshiftf.
    rewrite (assoc_thunkable _ (unwrap _)).
    rewrite unwrap_wrap_id, magmoid_id_left.
    apply wrap_unwrap_id.
  Qed.
  (* Note: triangle_2 is just wrap_unwrap_id *)

  (** Triangle equations of [force]/[delay] for the would-be-adjunction Dₜ⟦a, ⇑b⟧ ≃ D⟦a, b⟧ *)
  Lemma triangle_2_delay_force_' (a : D)
    : #⇑(force a) ∘ delay (⇑a) = identity (⇑a).
  Proof.
    unfold upshiftf.
    rewrite (assoc'_linear _ (delay _)).
    rewrite force_delay_id, magmoid_id_right.
    apply delay_force_id.
  Qed.
  (* Note: triangle_1 is just delay_force_id *)

  (** Unit of ⇓ ⊣ ⇑ *)
  Definition wrap_then_delay_thunkable
    : functor_identity (D ₜ) ⟹ downshift_thunkable_to_linear D ∙ upshift_linear_to_thunkable D
    := nat_trans_comp _ _ _
         wrap_thunkable
         (pre_whisker (downshift_thunkable_to_linear_and_thunkable D)
               (post_whisker delay_linear_and_thunkable
                  (linear_and_thunkable_category_to_thunkable_category D))).

  (** Counit of ⇓ ⊣ ⇑ *)
  Definition force_then_unwrap_linear
    : functor_identity (D ₗ) ⟸ upshift_linear_to_thunkable D ∙ downshift_thunkable_to_linear D
    := nat_trans_comp _ _ _
         (pre_whisker (upshift_linear_to_linear_and_thunkable D)
            (post_whisker unwrap_linear_and_thunkable
               (linear_and_thunkable_category_to_linear_category D)))
         force_linear.

  Definition upshift_downshift_linear_to_thunkable_adjunction_data
    : adjunction_data (D ₜ) (D ₗ).
  Proof.
    use make_adjunction_data.
    - apply downshift_thunkable_to_linear.
    - apply upshift_linear_to_thunkable.
    - apply wrap_then_delay_thunkable.
    - apply force_then_unwrap_linear.
  Defined.

  Definition upshift_downshift_linear_to_thunkable_form_adjunction
    : form_adjunction' upshift_downshift_linear_to_thunkable_adjunction_data.
  Proof.
    use make_form_adjunction.
    - intro a.
      apply carrier_eq; cbn.
      refine (_ @ triangle_1_wrap_unwrap_' a).
      etrans. { apply cancel_postcomposition, downshiftf_comp, (wrap _). }
      etrans. { apply assoc'_thunkable, is_thunkable_downshiftf, (wrap _). }
      apply cancel_precomposition.
      etrans. { apply assoc_linear, (force _). }
      etrans. { apply cancel_postcomposition, unwrap_natural. }
      etrans. { apply assoc'_thunkable, (unwrap _). }
      refine (_ @ magmoid_id_right _).
      apply cancel_precomposition, delay_force_id.
    - intro a.
      apply carrier_eq; cbn.
      refine (_ @ triangle_2_delay_force_' a).
      etrans. { apply cancel_precomposition, upshiftf_comp, (force _). }
      etrans. { apply assoc_linear, is_linear_upshiftf, (force _). }
      apply cancel_postcomposition.
      etrans. { apply assoc'_thunkable, (wrap _). }
      etrans. { apply cancel_precomposition, pathsinv0, delay_natural. }
      etrans. { apply assoc_linear, (delay _). }
      refine (_ @ magmoid_id_left _).
      apply cancel_postcomposition, wrap_unwrap_id.
  Qed.

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

  Definition delay_then_wrap_positive_thunkable
    : functor_identity (D⁺ₜ) ⟹
         upshift_positive_thunkable_to_negative_linear ∙
         downshift_negative_linear_to_positive_thunkable.
  Proof.
    use make_nat_trans.
    - intro a.
      refine (_,,tt).
      apply (make_thunkable_mor (delay _ · wrap _)).
      apply is_thunkable_compose;
        first [ apply is_thunkable_of_negative, (⇑_)
              | apply wrap ].
    - abstract (
          intros a b f;
          do 2 apply carrier_eq;
          cbn;
          etrans; [apply assoc_thunkable, (pr21 f)|];
          etrans; [apply cancel_postcomposition, delay_natural|];
          etrans; [apply (assoc'_negative _ (⇑_))|];
          etrans; [apply cancel_precomposition, wrap_natural|];
          apply (assoc_negative _ (⇑_))).
  Defined.

  Definition unwrap_then_force_negative_linear
    : functor_identity (D⁻ₗ) ⟸
         downshift_negative_linear_to_positive_thunkable ∙
         upshift_positive_thunkable_to_negative_linear.
  Proof.
    use make_nat_trans.
    - intro a.
      refine (_,,tt).
      apply (make_linear_mor (unwrap _ ∘ force _)).
      apply is_linear_compose;
        first [ apply is_linear_of_positive, (⇓_)
              | apply force ].
    - abstract (
          intros a b f;
          do 2 apply carrier_eq;
          cbn;
          apply pathsinv0;
          etrans; [apply assoc'_linear, (pr21 f)|];
          etrans; [apply maponpaths, (!unwrap_natural _ _ _ _)|];
          etrans; [apply (assoc_positive _ (⇓_))|];
          etrans; [apply cancel_postcomposition, (!force_natural _ _ _ _)|];
          apply (assoc'_positive _ (⇓_))).
  Defined.

  Lemma upshift_downshift_negative_linear_to_positive_thunkable_adjunction_data
    : adjunction_data (D⁺ₜ) (D⁻ₗ).
  Proof.
    use make_adjunction_data.
    - apply upshift_positive_thunkable_to_negative_linear.
    - apply downshift_negative_linear_to_positive_thunkable.
    - apply delay_then_wrap_positive_thunkable.
    - apply unwrap_then_force_negative_linear.
  Defined.

  Lemma upshift_downshift_negative_linear_to_positive_thunkable_form_adjunction
    : form_adjunction' upshift_downshift_negative_linear_to_positive_thunkable_adjunction_data.
  Proof.
    use make_form_adjunction.
    - intro a.
      do 2 apply carrier_eq; cbn.
      unfold upshiftf.
      etrans; [apply delay_force_interpose|].
      rewrite assoc'_positive; [|apply downshift].
      etrans; [apply cancel_precomposition, wrap_unwrap_right|].
      apply force_delay_id.
    - intro a.
      do 2 apply carrier_eq; cbn.
      unfold downshiftf.
      etrans; [apply wrap_unwrap_interpose|].
      rewrite assoc_negative; [|apply upshift].
      etrans; [apply cancel_postcomposition, delay_force_left|].
      apply unwrap_wrap_id.
  Qed.

End restricted_shift_functors.

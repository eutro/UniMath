(********************************************************************************

 Two-Sorted/Split Duploids

 Author: B. Szilvasy
 January 2026

 A polarity mapping of a unital (pre)magmoid D is a function mapping objects to the booleans {⊕, ⊖},
 such that each object mapped to ⊕ is positive, and each mapped to ⊖ is negative.  A split
 (pre)duploid is simply a (pre)duploid with such a mapping.

 Contents:
 1. Definition of a split duploid
 2. Definition of a polarity-preserving functor
 3. Characterizations of polarity-preserving duploid functors
 4. The chosen-polarity subcategories of a split duploid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Functors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.ShiftFunctors.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.ShiftFacts.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

(** ** 1. Definition of a split duploid *)

Definition hpolarity : hSet := make_hSet bool isasetbool.

Notation "'⊕'" := true : duploid.
Notation "'⊖'" := false : duploid.
Section split_defs.
  (** *** Polarity mappings *)
  Definition polarity_mapping_data (D : unital_premagmoid) : UU := D -> hpolarity.
  Identity Coercion Id_polarity_mapping_data : polarity_mapping_data >-> Funclass.

  Definition is_polarity_mapping
    {D : unital_premagmoid} (mapping : polarity_mapping_data D) : UU
    := ∏ (a : D), if mapping a then is_positive a else is_negative a.

  Lemma polarity_mapping_positive'
    {D : unital_premagmoid} {mapping : polarity_mapping_data D}
    (Hmapping : is_polarity_mapping mapping) (a : D)
    : mapping a = ⊕ -> is_positive a.
  Proof.
    intro H.
    set (H' := Hmapping a); rewrite H in H'.
    exact H'.
  Qed.

  Lemma polarity_mapping_negative'
    {D : unital_premagmoid} {mapping : polarity_mapping_data D}
    (Hmapping : is_polarity_mapping mapping) (a : D)
    : mapping a = ⊖ -> is_negative a.
  Proof.
    intro H.
    set (H' := Hmapping a); rewrite H in H'.
    exact H'.
  Qed.

  Lemma decide_polarity' {D : unital_premagmoid} {mapping : polarity_mapping_data D}
    (Hmapping : is_polarity_mapping mapping) (a : D)
    : is_negative a ⨿ is_positive a.
  Proof.
    set (choice := mapping a).
    assert (Hchoice : mapping a = choice); [reflexivity|].
    induction choice.
    - constructor; apply (polarity_mapping_positive' Hmapping), Hchoice.
    - constructor; apply (polarity_mapping_negative' Hmapping), Hchoice.
  Defined.

  Lemma isaprop_is_polarity_mapping
    {D : unital_magmoid} (mapping : polarity_mapping_data D)
    : isaprop (is_polarity_mapping mapping).
  Proof.
    apply impred; intro a.
    induction (mapping a).
    - apply isaprop_is_positive.
    - apply isaprop_is_negative.
  Qed.

  Definition polarity_mapping (D : unital_premagmoid) : UU
    := ∑ (mapping : polarity_mapping_data D), is_polarity_mapping mapping.

  Definition make_polarity_mapping {D : unital_premagmoid}
    (mapping : polarity_mapping_data D)
    (H : is_polarity_mapping mapping)
    : polarity_mapping D
    := mapping,,H.

  Coercion polarity_mapping_to_data {D : unital_premagmoid}
    (mapping : polarity_mapping D) : polarity_mapping_data D
    := pr1 mapping.
  Coercion polarity_mapping_is_polarity_mapping {D : unital_premagmoid}
    (mapping : polarity_mapping D) : is_polarity_mapping mapping
    := pr2 mapping.

  Definition make_polarity_mapping' {D : unital_premagmoid}
    (mapping : ∏ (a : D), is_positive a ⨿ is_negative a)
    : polarity_mapping D.
  Proof.
    use make_polarity_mapping.
    - intro a; induction (mapping a).
      + exact ⊕.
      + exact ⊖.
    - abstract (intro a; induction (mapping a); assumption).
  Defined.

  Definition polarity_mapping_to_has_polarities {D : unital_premagmoid}
    (mapping : polarity_mapping D) : has_polarities D.
  Proof.
    intro a; apply hinhpr.
    use decide_polarity'; apply mapping.
  Defined.

  (** Polarity mapping from LEM, biased towards negative. *)
  Lemma polarity_mapping_from_LEM (D : preduploid)
    : LEM -> polarity_mapping D.
  Proof.
    intros lem.
    use make_polarity_mapping'.
    intro a.
    induction (lem (ish_negative a)) as [Hnegative | Hnotnegative].
    - exact (ii2 Hnegative).
    - apply ii1.
      apply (has_polarity_rec (polarity_of D a)).
      1: apply isaprop_is_positive.
      all: easy.
  Defined.

  Lemma polarity_mapping_from_LEM_iff_negative
    {D : preduploid} (lem : LEM) (a : D)
    : is_negative a ≃ polarity_mapping_from_LEM D lem a = ⊖.
  Proof.
    cbn.
    induction (lem (ish_negative a)) as [Hnegative' | Hnotnegative]; cbn.
    - use weqimplimpl.
      + easy.
      + easy.
      + apply isaprop_is_negative.
      + apply isasetbool.
    - apply weqempty.
      + assumption.
      + exact nopathstruetofalse.
  Qed.

  Lemma polarity_mapping_from_LEM_iff_not_negative
    {D : preduploid} (lem : LEM) (a : D)
    : ¬is_negative a ≃ polarity_mapping_from_LEM D lem a = ⊕.
  Proof.
    cbn.
    induction (lem (ish_negative a)) as [Hnegative | Hnotnegative']; cbn.
    - apply weqempty.
      + now apply todneg.
      + exact nopathsfalsetotrue.
    - use weqimplimpl.
      + easy.
      + easy.
      + apply isapropneg.
      + apply isasetbool.
  Qed.
  #[global] Opaque polarity_mapping_from_LEM.

  (** *** Split preduploid *)
  Definition split_preduploid : UU
    := ∑ (D : preduploid), polarity_mapping D.
  Definition make_split_preduploid (D : preduploid)
    (mapping : polarity_mapping D)
    : split_preduploid := D,,mapping.
  Coercion split_preduploid_to_preduploid (D : split_preduploid) : preduploid := pr1 D.
  Definition split_preduploid_polarity_mapping (D : split_preduploid) : polarity_mapping D := pr2 D.

  Definition chosen_polarity_of {D : split_preduploid} (a : D) : hpolarity
    := split_preduploid_polarity_mapping D a.

  Lemma polarity_mapping_positive {D : split_preduploid} (a : D)
    : chosen_polarity_of a = ⊕ -> is_positive a.
  Proof. apply polarity_mapping_positive', split_preduploid_polarity_mapping. Qed.

  Lemma polarity_mapping_negative {D : split_preduploid} (a : D)
    : chosen_polarity_of a = ⊖ -> is_negative a.
  Proof. apply polarity_mapping_negative', split_preduploid_polarity_mapping. Qed.

  Lemma decide_polarity {D : split_preduploid} (a : D) : is_negative a ⨿ is_positive a.
  Proof. use decide_polarity'; apply split_preduploid_polarity_mapping. Defined.

  Definition polarity_mapping_respects_shifts {D : duploid} (mapping : polarity_mapping D)
    : UU := (∏ (a : D), (mapping (⇓a) = ⊕)%logic) × (∏ (a : D), (mapping (⇑a) = ⊖)%logic).
  Definition downshift_polarity_mapping {D : duploid} {mapping : polarity_mapping D}
    (H : polarity_mapping_respects_shifts mapping) : ∏ (a : D), mapping (⇓a) = ⊕ := pr1 H.
  Definition upshift_polarity_mapping {D : duploid} {mapping : polarity_mapping D}
    (H : polarity_mapping_respects_shifts mapping) : ∏ (a : D), mapping (⇑a) = ⊖ := pr2 H.

  Lemma isaprop_polarity_mapping_respects_shifts {D : duploid} (mapping : polarity_mapping D)
    : isaprop (polarity_mapping_respects_shifts mapping).
  Proof. apply isapropdirprod; apply impred; intro; apply propproperty. Qed.

  (** *** Split duploid *)
  Definition split_duploid : UU
    := ∑ (D : duploid) (mapping : polarity_mapping D), polarity_mapping_respects_shifts mapping.
  Definition make_split_duploid (D : duploid)
    (mapping : polarity_mapping D)
    (Hmapping : polarity_mapping_respects_shifts mapping)
    : split_duploid := D,,mapping,,Hmapping.
  Coercion split_duploid_to_duploid (D : split_duploid) : duploid := pr1 D.
  Definition split_duploid_polarity_mapping (D : split_duploid) : polarity_mapping D := pr12 D.
  Coercion split_duploid_polarity_mapping_respects_shifts (D : split_duploid)
    : polarity_mapping_respects_shifts (split_duploid_polarity_mapping D) := pr22 D.

  Coercion split_duploid_to_split_preduploid (D : split_duploid) : split_preduploid
    := make_split_preduploid D (split_duploid_polarity_mapping D).

  Goal ∏ {D : split_duploid} (a : D), is_negative a ⨿ is_positive a.
  Proof.
    intros D a.
    (** Due to association, applying [decide_polarity] alone does not work at time of writing. *)
    (* Fail apply decide_polarity. *)
    (** Instead, specify D explicitly. *)
    apply (decide_polarity (D:=D) a).
  Qed.

  Lemma chosen_polarity_of_downshift {D : split_duploid} (a : D)
    : chosen_polarity_of (D:=D) (⇓a) = ⊕.
  Proof. apply (downshift_polarity_mapping D). Qed.
  Lemma chosen_polarity_of_upshift {D : split_duploid} (a : D)
    : chosen_polarity_of (D:=D) (⇑a) = ⊖.
  Proof. apply (upshift_polarity_mapping D). Qed.

End split_defs.

(** ** 2. Definition of a functor of a polarity-preserving functor

 [polarity_preserving_functor] is the notion of a functor of split preduploids
 presented in Munch-Maccagnoni's PhD thesis. *)

Section functor_defs.
  Context {D D' : split_preduploid}.

  Definition preserves_polarity_mapping (F : functor_data D D') : UU
    := ∏ (a : D), (chosen_polarity_of (F a) = chosen_polarity_of a)%logic.

  Lemma isaprop_preserves_polarity_mapping (F : functor_data D D')
    : isaprop (preserves_polarity_mapping F).
  Proof.
    apply impred; intro.
    apply propproperty.
  Qed.

  Lemma functor_chosen_polarity' {F : functor_data D D'}
    (H : preserves_polarity_mapping F) (a : D)
    : (chosen_polarity_of (F a) = chosen_polarity_of a)%logic.
  Proof. apply H. Qed.

  Definition polarity_preserving_functor : UU
    := ∑ (F : functor D D'), preserves_polarity_mapping F.

  Definition make_polarity_preserving_functor
    (F : functor D D')
    (H : preserves_polarity_mapping F)
    : polarity_preserving_functor := F,,H.

  Coercion polarity_preserving_functor_to_functor (F : polarity_preserving_functor)
    : functor D D' := pr1 F.
  Coercion polarity_preserving_functor_preserves_polarity_mapping (F : polarity_preserving_functor)
    : preserves_polarity_mapping F := pr2 F.

  Lemma functor_chosen_polarity (F : polarity_preserving_functor) (a : D)
    : (chosen_polarity_of (F a) = chosen_polarity_of a)%logic.
  Proof. apply functor_chosen_polarity', F. Qed.

End functor_defs.
Arguments polarity_preserving_functor : clear implicits.

Section functor_defs.

  Lemma preserves_polarity_mapping_identity
    (D : split_preduploid) : preserves_polarity_mapping (functor_identity D).
  Proof. now intro a. Qed.

  Lemma preserves_polarity_mapping_comp
    {D₁ D₂ D₃ : split_preduploid} (F : functor_data D₁ D₂) (G : functor_data D₂ D₃)
    (HF : preserves_polarity_mapping F) (HG : preserves_polarity_mapping G)
    : preserves_polarity_mapping (functor_composite_data F G).
  Proof. intro a; apply (HG (F a) @ HF a). Qed.

End functor_defs.

(** ** 3. Characterizations of polarity-preserving duploid functors

 There are three characterizations of a duploid functor presented in
 Munch-Maccagnoni's PhD thesis:

 1. A [polarity_preserving_functor] F such that [F (force a)] is linear and [F
    (wrap a)] is thunkable for all objects.
 2. A [polarity_preserving_functor] F such that [F delay], [F force], [F wrap]
    and [F unwrap] form a duploid structure in the image of F.
 3. A [functor_data D D'] F that [preserves_polarity_mapping], which restricts
    to functors [Fₜ : Dₜ ⟶ D'ₜ] and [Fₗ : Dₗ ⟶ D'ₗ] such that the transformation
    [F : D⟦a, b⟧ ↦ D'⟦Fₜ a, Fₗ b⟧] is natural in (a : Dₜ) and (b : Dₗ).

 A variant of the third is the definition [split_duploid_functor], noting that
 naturality amounts to the equation [#F(f · g · h) = #F f · #F g · #F h] for
 thunkable f and linear h, which ultimately corresponds to functoriality of F.
 See [make_split_duploid_functor_from_natural_prepostcomp].

 *)

Section functor_def.
  Context {D D' : split_preduploid}.

  (** *** Definition of [split_duploid_functor] *)
  Definition split_duploid_functor : UU
    := ∑ (F : duploid_functor D D'), preserves_polarity_mapping (D:=D) (D':=D') F.
  Definition make_split_duploid_functor
    (F : duploid_functor D D')
    (H : preserves_polarity_mapping (D:=D) (D':=D') F)
    : split_duploid_functor := F,,H.

  Coercion split_duploid_functor_to_duploid_functor
    (F : split_duploid_functor) : duploid_functor D D' := pr1 F.
  Coercion split_duploid_functor_preserves_polarity_mapping
    (F : split_duploid_functor) : preserves_polarity_mapping (D:=D) (D':=D') F := pr2 F.

End functor_def.
Arguments split_duploid_functor : clear implicits.

(*** *** Lemmas about split duploid functors *)

Definition split_duploid_functor_identity (M : split_preduploid) : split_duploid_functor M M
  := make_split_duploid_functor (duploid_functor_identity M) (preserves_polarity_mapping_identity _).

Definition split_duploid_functor_comp {M₁ M₂ M₃ : split_preduploid}
  (F : split_duploid_functor M₁ M₂) (G : split_duploid_functor M₂ M₃)
  : split_duploid_functor M₁ M₃
  := make_split_duploid_functor (duploid_functor_comp F G)
       (preserves_polarity_mapping_comp F G F G).

(** *** Characterisation #3 *)
Section functor_char3.
  Context {D D' : split_preduploid}.
  Context (F : functor_data D D').
  (* Identities are both linear and thunkable, so this comes from
     functoriality of either Fₗ or Fₜ. *)
  Hypothesis (HF_id : ∏ (a : D), #F (identity a) = identity (F a)).
  Hypothesis (HF_natural : ∏ (a b c d : D) (f : thunkable_mor a b) (g : D⟦b, c⟧) (h : linear_mor c d),
                 #F (f · g · h) = #F f · #F g · #F h).
  Hypothesis (Hpolarity : preserves_polarity_mapping (D:=D) (D':=D') F).
  Hypothesis (Hpreserves_linearity_and_thunkability : preserves_linearity_and_thunkability F).

  Local Lemma is_functor_F : is_functor F.
  Proof.
    use make_is_functor.
    - intro a; apply HF_id.
    - intros a b c f g.
      induction (decide_polarity b) as [Hb_negative | Hb_positive].
      + transparent assert (f' : (thunkable_mor a b)). {
          apply (make_thunkable_mor f),
            is_thunkable_of_negative, Hb_negative.
        }
        refine (_ @ HF_natural _ _ _ _ f' g (linear_identity c) @ _).
        * now cbn; rewrite magmoid_id_right.
        * now cbn; rewrite HF_id, magmoid_id_right.
      + transparent assert (g' : (linear_mor b c)). {
          apply (make_linear_mor g),
            is_linear_of_positive, Hb_positive.
        }
        refine (_ @ HF_natural _ _ _ _ (thunkable_identity a) f g' @ _).
        * now cbn; rewrite magmoid_id_left.
        * now cbn; rewrite HF_id, magmoid_id_left.
  Qed.

  Lemma make_split_duploid_functor_from_natural_prepostcomp : split_duploid_functor D D'.
  Proof.
    use (make_split_duploid_functor (make_duploid_functor (make_functor F _) _)).
    - apply is_functor_F.
    - assumption.
    - assumption.
  Defined.
End functor_char3.

(** ** 4. The chosen-polarity subcategories of a split duploid *)

Section split_chosen_subcategories.
  Context (D : split_preduploid).

  Definition chosen_positive_category : category
    := full_sub_category (positive_category D) (λ (a : positive_ob D),
           (chosen_polarity_of a = ⊕)%logic).
  Definition chosen_positive_thunkable_category : category
    := full_sub_category (positive_thunkable_category D) (λ (a : positive_ob D),
           (chosen_polarity_of a = ⊕)%logic).
  Definition chosen_negative_category : category
    := full_sub_category (negative_category D) (λ (a : negative_ob D),
           (chosen_polarity_of a = ⊖)%logic).
  Definition chosen_negative_linear_category : category
    := full_sub_category (negative_linear_category D) (λ (a : negative_ob D),
           (chosen_polarity_of a = ⊖)%logic).
End split_chosen_subcategories.

Notation "M '⁺ᶜ'" := (chosen_positive_category M) (at level 1) : duploid.
  (* type in Emacs using agda-input with \^c \^+ *)
Notation "M '⁻ᶜ'" := (chosen_negative_category M) (at level 1) : duploid.
  (* type in Emacs using agda-input with \^c \^- *)
Notation "M '⁺ᶜₜ'" := (chosen_positive_thunkable_category M) (at level 1) : duploid.
  (* type in Emacs using agda-input with \^c \^+ \_t *)
Notation "M '⁻ᶜₗ'" := (chosen_negative_linear_category M) (at level 1) : duploid.
  (* type in Emacs using agda-input with \^c \^- \_l *)

Section inclusion_functors.
  Context (D : split_preduploid).

  Definition chosen_positive_category_to_positive_category : D⁺ᶜ ⟶ D⁺
    := sub_precategory_inclusion _ _.
  Definition chosen_positive_thunkable_category_to_positive_thunkable_category : D⁺ᶜₜ ⟶ D⁺ₜ
    := sub_precategory_inclusion _ _.
  Definition chosen_negative_category_to_negative_category : D⁻ᶜ ⟶ D⁻
    := sub_precategory_inclusion _ _.
  Definition chosen_negative_linear_category_to_negative_linear_category : D⁻ᶜₗ ⟶ D⁻ₗ
    := sub_precategory_inclusion _ _.
End inclusion_functors.

Section inclusion_equivalences.
  (** In a split duploid, the above are equivalences *)
  Context (D : split_duploid).

  (** Equivalence between chosen positive and positive categories *)
  Lemma split_essentially_surjective_chosen_positive_category_to_positive_category
    : split_essentially_surjective (chosen_positive_category_to_positive_category D).
  Proof.
    intro a; cbn in a.
    use tpair; [exists (⇓a); apply chosen_polarity_of_downshift|].
    use make_z_iso.
    - refine (_,,tt).
      exists (unwrap a).
      apply is_linear_unwrap.
    - refine (_,,tt).
      exists (wrap a).
      apply is_linear_wrap_of_positive, a.
    - abstract (apply make_is_inverse_in_precat;
                do 2 apply carrier_eq;
                apply are_inverses_unwrap_wrap).
  Defined.

  Lemma split_essentially_surjective_chosen_positive_thunkable_category_to_positive_thunkable_category
    : split_essentially_surjective (chosen_positive_thunkable_category_to_positive_thunkable_category D).
  Proof.
    intro a; cbn in a.
    use tpair; [exists (⇓a); apply chosen_polarity_of_downshift|].
    use make_z_iso.
    - exact (unwrap a,,tt).
    - exact (wrap a,,tt).
    - abstract (apply make_is_inverse_in_precat;
                do 2 apply carrier_eq;
                apply are_inverses_unwrap_wrap).
  Defined.

  Lemma fully_faithful_chosen_positive_category_to_positive_category
    : fully_faithful (chosen_positive_category_to_positive_category D).
  Proof. apply fully_faithful_sub_precategory_inclusion. Defined.

  Lemma fully_faithful_chosen_positive_thunkable_category_to_positive_thunkable_category
    : fully_faithful (chosen_positive_thunkable_category_to_positive_thunkable_category D).
  Proof. apply fully_faithful_sub_precategory_inclusion. Defined.

  Lemma adj_equivalence_chosen_positive_to_positive
    : adj_equivalence_of_cats (chosen_positive_category_to_positive_category D).
  Proof.
    apply rad_equivalence_of_cats'.
    - apply fully_faithful_chosen_positive_category_to_positive_category.
    - apply split_essentially_surjective_chosen_positive_category_to_positive_category.
  Defined.

  Lemma adj_equivalence_chosen_positive_thunkable_to_positive_thunkable
    : adj_equivalence_of_cats (chosen_positive_thunkable_category_to_positive_thunkable_category D).
  Proof.
    apply rad_equivalence_of_cats'.
    - apply fully_faithful_chosen_positive_thunkable_category_to_positive_thunkable_category.
    - apply split_essentially_surjective_chosen_positive_thunkable_category_to_positive_thunkable_category.
  Defined.

  (** Equivalence between chosen negative and negative categories *)
  Lemma split_essentially_surjective_chosen_negative_category_to_negative_category
    : split_essentially_surjective (chosen_negative_category_to_negative_category D).
  Proof.
    intro a; cbn in a.
    use tpair; [exists (⇑a); apply chosen_polarity_of_upshift|].
    use make_z_iso.
    - refine (_,,tt).
      exists (force a).
      apply is_thunkable_force_of_negative, a.
    - refine (_,,tt).
      exists (delay a).
      apply is_thunkable_delay.
    - abstract (apply make_is_inverse_in_precat;
                do 2 apply carrier_eq;
                apply are_inverses_force_delay).
  Defined.

  Lemma split_essentially_surjective_chosen_negative_linear_category_to_negative_linear_category
    : split_essentially_surjective (chosen_negative_linear_category_to_negative_linear_category D).
  Proof.
    intro a; cbn in a.
    use tpair; [exists (⇑a); apply chosen_polarity_of_upshift|].
    use make_z_iso.
    - exact (force a,,tt).
    - exact (delay a,,tt).
    - abstract (apply make_is_inverse_in_precat;
                do 2 apply carrier_eq;
                apply are_inverses_force_delay).
  Defined.

  Lemma fully_faithful_chosen_negative_category_to_negative_category
    : fully_faithful (chosen_negative_category_to_negative_category D).
  Proof. apply fully_faithful_sub_precategory_inclusion. Defined.

  Lemma fully_faithful_chosen_negative_linear_category_to_negative_linear_category
    : fully_faithful (chosen_negative_linear_category_to_negative_linear_category D).
  Proof. apply fully_faithful_sub_precategory_inclusion. Defined.

  Lemma adj_equivalence_chosen_negative_to_negative
    : adj_equivalence_of_cats (chosen_negative_category_to_negative_category D).
  Proof.
    apply rad_equivalence_of_cats'.
    - apply fully_faithful_chosen_negative_category_to_negative_category.
    - apply split_essentially_surjective_chosen_negative_category_to_negative_category.
  Defined.

  Lemma adj_equivalence_chosen_negative_linear_to_negative_linear
    : adj_equivalence_of_cats (chosen_negative_linear_category_to_negative_linear_category D).
  Proof.
    apply rad_equivalence_of_cats'.
    - apply fully_faithful_chosen_negative_linear_category_to_negative_linear_category.
    - apply split_essentially_surjective_chosen_negative_linear_category_to_negative_linear_category.
  Defined.

End inclusion_equivalences.

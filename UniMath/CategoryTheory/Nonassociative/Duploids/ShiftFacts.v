(********************************************************************************

 Theorems About the Shifts of a Duploid

 Author: B. Szilvasy
 January 2026

 There is an alternate characterization of [positive_shift_axioms] and
 [negative_shift_axioms] given by the following universal properties:

 - A positive shift on a [unital_magmoid] M consists of, for every object [a :
   M], an object [⇓a : M] and a morphism [wrap a : a --> ⇓a] which
   [is_thunkable] and [is_epi], such that for every morphism [f : a --> b]
   there is a unique linear map [f† : ⇓a --> b] with [wrap a · f† = f].

 - A negative shift on a [unital_magmoid] M consists of, for every object [a :
   M], an object [⇑a : M] and a morphism [force a : ⇑a --> a] which
   [is_linear] and [is_monic], such that for every morphism [f : a --> b]
   there is a unique thunkable map [f† : a --> ⇑b] with [f† · force a = f].

 Contents:
 1. Universal properties of shifts
 1.1. Universal property of negative shifts
 1.2. [has_negative_shifts] has the universal property
 1.3. [has_negative_shifts] from UP
 1.4. Universal property of positive shifts
 1.5. [has_positive_shifts] has the universal property
 1.6. [has_positive_shifts] from UP
 2. Derived properties from the universal properties

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.EpisAndMonics.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

(** ** 1. Universal properties of shifts *)

Section negative_shifts_up.
  Context {M : unital_magmoid}.

  Context (Dnegative : negative_shift_data M).

  (** *** 1.1. Universal property of negative shifts *)
  Definition has_negative_shifts_up : UU
    := (∏ (a : M), is_linear (force' Dnegative a)) ×
         (∏ (a : M), is_monic (force' Dnegative a)) ×
         (∏ (a b : M) (f : a --> b),
           ∑ (f' : ∃! (f' : a --> upshift' Dnegative b),
                 f' · force' Dnegative b = f),
             is_thunkable (pr1 (iscontrpr1 f'))).

  Lemma isaprop_has_negative_shifts_up
    : isaprop has_negative_shifts_up.
  Proof.
    apply isapropdirprod.
    2: apply isapropdirprod.
    - apply impred; intro.
      apply isaprop_is_linear.
    - apply impred; intro.
      apply isaprop_is_monic', unital_magmoid_has_homsets.
    - do 3 (apply impred; intro).
      apply isaproptotal2.
      + intro; apply isaprop_is_thunkable.
      + intros; apply isapropiscontr.
  Qed.

  (** Uniqueness comes for free *)
  Definition make_negative_shifts_up
    (Hlinear : ∏ (a : M), is_linear (force' Dnegative a))
    (Hmonic : ∏ (a : M), is_monic (force' Dnegative a))
    (Hlift : ∏ (a b : M) (f : a --> b), a --> upshift' Dnegative b)
    (Hlift_thunkable : ∏ (a b : M) (f : a --> b), is_thunkable (Hlift a b f))
    (Hlift_factors : ∏ (a b : M) (f : a --> b), Hlift a b f · force' Dnegative b = f)
    : has_negative_shifts_up.
  Proof.
    use make_dirprod.
    2: use make_dirprod.
    - exact Hlinear.
    - exact Hmonic.
    - intros a b f.
      use tpair.
      + use (unique_exists (Hlift a b f)).
        2: intro g; apply unital_magmoid_has_homsets.
        * apply Hlift_factors.
        * abstract (intros f' Hf';
                    apply Hmonic;
                    refine (Hf' @ _);
                    apply pathsinv0, Hlift_factors).
      + apply Hlift_thunkable.
  Defined.

  (** *** 1.2. [has_negative_shifts] has the universal property *)

  Hypothesis (Hnegative : negative_shift_axioms Dnegative).

  Definition negative_lift' {a b : M} (f : a --> b) : a --> upshift' Dnegative b
    := f · delay' Hnegative b.

  Lemma negative_lift_factors' {a b : M} (f : a --> b)
    : negative_lift' f · force' Dnegative b = f.
  Proof.
    unfold negative_lift'.
    etrans; [apply (assoc'_linear _ (is_linear_force' Hnegative _))|].
    refine (_ @ magmoid_id_right f).
    apply cancel_precomposition.
    apply (is_inverse_in_precat2 (has_linear_inverse_force' Hnegative _)).
  Qed.

  Lemma is_monic_force' (a : M) : is_monic (force' Dnegative a).
  Proof.
    intros b f g H.
    refine (!magmoid_id_right f @ _ @ magmoid_id_right g).
    rewrite <- !(is_inverse_in_precat1 (has_linear_inverse_force' Hnegative a)).
    rewrite !(assoc_linear _ (delay' Hnegative a)).
    apply cancel_postcomposition, H.
  Qed.

  Lemma is_thunkable_negative_lift' {a b : M} (f : a --> b)
    : is_thunkable (negative_lift' f).
  Proof.
    apply is_thunkable_of_negative, (is_negative_upshift' Hnegative).
  Qed.

  Theorem has_negative_shifts_has_up : has_negative_shifts_up.
  Proof.
    use make_negative_shifts_up.
    - exact (is_linear_force' Hnegative).
    - exact is_monic_force'.
    - exact @negative_lift'.
    - exact @is_thunkable_negative_lift'.
    - exact @negative_lift_factors'.
  Defined.

  (** *** 1.3. [has_negative_shifts] from UP *)

  Context (Hnegative_up : has_negative_shifts_up).

  Definition is_linear_force_from_up (a : M)
    : is_linear (force' Dnegative a) := pr1 Hnegative_up a.
  Definition is_monic_force_from_up (a : M)
    : is_monic (force' Dnegative a) := pr12 Hnegative_up a.
  Definition negative_lift_from_up {a b : M} (f : a --> b)
    : a --> upshift' Dnegative b := pr1 (iscontrpr1 (pr1 (pr22 Hnegative_up a b f))).
  Definition is_thunkable_negative_lift_from_up {a b : M} (f : a --> b)
    : is_thunkable (negative_lift_from_up f) := pr2 (pr22 Hnegative_up a b f).
  Definition negative_lift_from_up_factors {a b : M} (f : a --> b)
    : negative_lift_from_up f · force' Dnegative b = f := pr2 (iscontrpr1 (pr1 (pr22 Hnegative_up a b f))).
  Definition negative_lift_from_up_unique {a b : M} (f : a --> b) (g : a --> upshift' Dnegative b)
    : g · force' Dnegative b = f ->
      g = negative_lift_from_up f
    := λ H, base_paths _ _ (iscontr_uniqueness (pr1 (pr22 Hnegative_up a b f)) (g,,H)).

  Lemma delay_from_up (a : M) : a --> upshift' Dnegative a.
  Proof. exact (negative_lift_from_up (identity a)). Defined.

  Lemma is_inverse_in_precat_force_delay_from_up (a : M)
    : is_inverse_in_precat (force' Dnegative a) (delay_from_up a).
  Proof.
    split; unfold delay_from_up; cbn; try apply negative_lift_from_up_factors.
    apply is_monic_force_from_up.
    refine (_ @ !magmoid_id_left _).
    etrans; [apply assoc'_linear, is_linear_force_from_up|].
    etrans; [apply cancel_precomposition, negative_lift_from_up_factors|].
    apply magmoid_id_right.
  Qed.

  Lemma is_linear_delay_from_up (a : M) : is_linear (delay_from_up a).
  Proof.
    intros b c g h; unfold delay_from_up.
    apply is_monic_force_from_up.
    rewrite !(assoc'_linear _ (is_linear_force_from_up a)).
    rewrite !negative_lift_from_up_factors.
    rewrite !magmoid_id_right.
    reflexivity.
  Qed.

  Lemma is_linear_and_thunkable_delay_from_up (a : M) : is_linear_and_thunkable (delay_from_up a).
  Proof.
    use make_is_linear_and_thunkable;
      first [ apply is_linear_delay_from_up
            | apply is_thunkable_negative_lift_from_up ].
  Qed.

  Lemma has_linear_and_thunkable_inverse_force_from_up (a : M)
    : has_linear_and_thunkable_inverse (force' Dnegative a).
  Proof.
    use make_has_linear_and_thunkable_inverse.
    - use (make_linear_and_thunkable_mor (delay_from_up a)).
      apply is_linear_and_thunkable_delay_from_up.
    - apply is_inverse_in_precat_force_delay_from_up.
  Defined.

  Lemma is_negative_upshift_from_up (a : M) : is_negative (upshift' Dnegative a).
  Proof.
    intros b f.
    rewrite (negative_lift_from_up_unique _ f (idpath _)).
    apply is_thunkable_negative_lift_from_up.
  Qed.

  Theorem negative_shift_axioms_from_up : negative_shift_axioms Dnegative.
  Proof.
    use make_negative_shift_axioms.
    - exact is_linear_force_from_up.
    - exact is_negative_upshift_from_up.
    - exact has_linear_and_thunkable_inverse_force_from_up.
  Defined.

End negative_shifts_up.

Corollary negative_shift_axioms_iff_has_negative_shifts_up
  (M : unital_magmoid) (Dnegative : negative_shift_data M)
  : negative_shift_axioms Dnegative ≃ has_negative_shifts_up Dnegative.
Proof.
  apply weqimplimpl.
  - apply has_negative_shifts_has_up.
  - apply negative_shift_axioms_from_up.
  - apply isaprop_negative_shift_axioms.
  - apply isaprop_has_negative_shifts_up.
Defined.

Section positive_shifts_up.
  Context {M : unital_magmoid}.

  Context (Dpositive : positive_shift_data M).

  (** *** 1.4. Universal property of positive shifts *)
  Definition has_positive_shifts_up : UU
    := (∏ (a : M), is_thunkable (wrap' Dpositive a)) ×
         (∏ (a : M), is_epi (wrap' Dpositive a)) ×
         (∏ (a b : M) (f : a <-- b),
           ∑ (f' : ∃! (f' : a <-- downshift' Dpositive b),
                 f' ∘ wrap' Dpositive b = f),
             is_linear (pr1 (iscontrpr1 f'))).

  Lemma isaprop_has_positive_shifts_up
    : isaprop has_positive_shifts_up.
  Proof.
    apply isapropdirprod.
    2: apply isapropdirprod.
    - apply impred; intro.
      apply isaprop_is_thunkable.
    - apply impred; intro.
      apply isaprop_is_epi', unital_magmoid_has_homsets.
    - do 3 (apply impred; intro).
      apply isaproptotal2.
      + intro; apply isaprop_is_linear.
      + intros; apply isapropiscontr.
  Qed.

  (** Uniqueness comes for free *)
  Definition make_positive_shifts_up
    (Hthunkable : ∏ (a : M), is_thunkable (wrap' Dpositive a))
    (Hepi : ∏ (a : M), is_epi (wrap' Dpositive a))
    (Hlift : ∏ (a b : M) (f : a <-- b), a <-- downshift' Dpositive b)
    (Hlift_linear : ∏ (a b : M) (f : a <-- b), is_linear (Hlift a b f))
    (Hlift_factors : ∏ (a b : M) (f : a <-- b), Hlift a b f ∘ wrap' Dpositive b = f)
    : has_positive_shifts_up.
  Proof.
    use make_dirprod.
    2: use make_dirprod.
    - exact Hthunkable.
    - exact Hepi.
    - intros a b f.
      use tpair.
      + use (unique_exists (Hlift a b f)).
        2: intro g; apply unital_magmoid_has_homsets.
        * apply Hlift_factors.
        * abstract (intros f' Hf';
                    apply Hepi;
                    refine (Hf' @ _);
                    apply pathsinv0, Hlift_factors).
      + apply Hlift_linear.
  Defined.

  (** *** 1.5. [has_positive_shifts] has the universal property *)

  Hypothesis (Hpositive : positive_shift_axioms Dpositive).

  Definition positive_lift' {a b : M} (f : a <-- b) : a <-- downshift' Dpositive b
    := f ∘ unwrap' Hpositive b.

  Lemma positive_lift_factors' {a b : M} (f : a <-- b)
    : positive_lift' f ∘ wrap' Dpositive b = f.
  Proof.
    unfold positive_lift'.
    etrans; [apply (assoc_thunkable _ (is_thunkable_wrap' Hpositive _))|].
    refine (_ @ magmoid_id_left f).
    apply cancel_postcomposition.
    apply (is_inverse_in_precat2 (has_thunkable_inverse_wrap' Hpositive _)).
  Qed.

  Lemma is_epi_wrap' (a : M) : is_epi (wrap' Dpositive a).
  Proof.
    intros b f g H.
    refine (!magmoid_id_left f @ _ @ magmoid_id_left g).
    rewrite <- !(is_inverse_in_precat1 (has_thunkable_inverse_wrap' Hpositive a)).
    rewrite !(assoc'_thunkable _ (unwrap' Hpositive a)).
    apply cancel_precomposition, H.
  Qed.

  Lemma is_linear_positive_lift' {a b : M} (f : a <-- b)
    : is_linear (positive_lift' f).
  Proof.
    apply is_linear_of_positive, (is_positive_downshift' Hpositive).
  Qed.

  Theorem has_positive_shifts_has_up : has_positive_shifts_up.
  Proof.
    use make_positive_shifts_up.
    - exact (is_thunkable_wrap' Hpositive).
    - exact is_epi_wrap'.
    - exact @positive_lift'.
    - exact @is_linear_positive_lift'.
    - exact @positive_lift_factors'.
  Defined.

  (** *** 1.6. [has_positive_shifts] from UP *)

  Context (Hpositive_up : has_positive_shifts_up).

  Definition is_thunkable_wrap_from_up (a : M)
    : is_thunkable (wrap' Dpositive a) := pr1 Hpositive_up a.
  Definition is_epi_wrap_from_up (a : M)
    : is_epi (wrap' Dpositive a) := pr12 Hpositive_up a.
  Definition positive_lift_from_up {a b : M} (f : a <-- b)
    : a <-- downshift' Dpositive b := pr1 (iscontrpr1 (pr1 (pr22 Hpositive_up a b f))).
  Definition is_linear_positive_lift_from_up {a b : M} (f : a <-- b)
    : is_linear (positive_lift_from_up f) := pr2 (pr22 Hpositive_up a b f).
  Definition positive_lift_from_up_factors {a b : M} (f : a <-- b)
    : positive_lift_from_up f ∘ wrap' Dpositive b = f := pr2 (iscontrpr1 (pr1 (pr22 Hpositive_up a b f))).
  Definition positive_lift_from_up_unique {a b : M} (f : a <-- b) (g : a <-- downshift' Dpositive b)
    : g ∘ wrap' Dpositive b = f ->
      g = positive_lift_from_up f
    := λ H, base_paths _ _ (iscontr_uniqueness (pr1 (pr22 Hpositive_up a b f)) (g,,H)).

  Lemma unwrap_from_up (a : M) : a <-- downshift' Dpositive a.
  Proof. exact (positive_lift_from_up (identity a)). Defined.

  Lemma is_inverse_in_precat_unwrap_wrap_from_up (a : M)
    : is_inverse_in_precat (wrap' Dpositive a) (unwrap_from_up a).
  Proof.
    split; unfold unwrap_from_up; cbn; try apply positive_lift_from_up_factors.
    apply is_epi_wrap_from_up.
    refine (_ @ !magmoid_id_right _).
    etrans; [apply assoc_thunkable, is_thunkable_wrap_from_up|].
    etrans; [apply cancel_postcomposition, positive_lift_from_up_factors|].
    apply magmoid_id_left.
  Qed.

  Lemma is_thunkable_unwrap_from_up (a : M) : is_thunkable (unwrap_from_up a).
  Proof.
    intros b c g h; unfold unwrap_from_up.
    apply is_epi_wrap_from_up.
    rewrite !(assoc_thunkable _ (is_thunkable_wrap_from_up a)).
    rewrite !positive_lift_from_up_factors.
    rewrite !magmoid_id_left.
    reflexivity.
  Qed.

  Lemma is_linear_and_thunkable_unwrap_from_up (a : M) : is_linear_and_thunkable (unwrap_from_up a).
  Proof.
    use make_is_linear_and_thunkable;
      first [ apply is_thunkable_unwrap_from_up
            | apply is_linear_positive_lift_from_up ].
  Qed.

  Lemma has_linear_and_thunkable_inverse_wrap_from_up (a : M)
    : has_linear_and_thunkable_inverse (wrap' Dpositive a).
  Proof.
    use make_has_linear_and_thunkable_inverse.
    - use (make_linear_and_thunkable_mor (unwrap_from_up a)).
      apply is_linear_and_thunkable_unwrap_from_up.
    - apply is_inverse_in_precat_unwrap_wrap_from_up.
  Defined.

  Lemma is_positive_downshift_from_up (a : M) : is_positive (downshift' Dpositive a).
  Proof.
    intros b f.
    rewrite (positive_lift_from_up_unique _ f (idpath _)).
    apply is_linear_positive_lift_from_up.
  Qed.

  Theorem positive_shift_axioms_from_up : positive_shift_axioms Dpositive.
  Proof.
    use make_positive_shift_axioms.
    - exact is_thunkable_wrap_from_up.
    - exact is_positive_downshift_from_up.
    - exact has_linear_and_thunkable_inverse_wrap_from_up.
  Defined.

End positive_shifts_up.

Corollary positive_shift_axioms_iff_has_positive_shifts_up
  (M : unital_magmoid) (Dpositive : positive_shift_data M)
  : positive_shift_axioms Dpositive ≃ has_positive_shifts_up Dpositive.
Proof.
  apply weqimplimpl.
  - apply has_positive_shifts_has_up.
  - apply positive_shift_axioms_from_up.
  - apply isaprop_positive_shift_axioms.
  - apply isaprop_has_positive_shifts_up.
Defined.

(** ** 2. Derived properties from the universal properties *)

Section derived_props.
  Context {D : duploid}.

  (** Accessors for negative lift UP in a duploid *)
  Definition negative_lift {a b : D} (f : a --> b) : thunkable_mor a (⇑b).
  Proof.
    use make_thunkable_mor.
    - apply (negative_lift' D D f).
    - apply is_thunkable_negative_lift'.
  Defined.

  Lemma negative_lift_factors {a b : D} (f : a --> b)
    : negative_lift f · force b = f.
  Proof.
    apply (negative_lift_factors' _ D).
  Qed.

  Lemma negative_lift_unique {a b : D} (f : a --> b) (g : a --> ⇑b)
    : g · force b = f ->
      g = negative_lift f.
  Proof.
    apply (negative_lift_from_up_unique _ (has_negative_shifts_has_up _ D)).
  Qed.

  Definition isweq_negative_lift (a b : D) : isweq (λ (f : a --> b), negative_lift f).
  Proof.
    intro f'.
    use unique_exists.
    3: intro; apply isaset_thunkable_mor.
    - apply (f' · force b).
    - abstract (now apply carrier_eq, pathsinv0, negative_lift_unique).
    - abstract (intros f H;
        apply base_paths in H;
        etrans; [|apply cancel_postcomposition, H];
        apply pathsinv0, negative_lift_factors).
  Defined.

  Lemma is_monic_delay (a : D) : is_monic (delay a).
  Proof.
    intros b f g H.
    refine (!negative_lift_factors f @ _ @ negative_lift_factors g).
    apply cancel_postcomposition.
    exact H.
  Qed.

  Definition is_linear_of_negative_lift {a b : D} (f : a --> b)
    : is_linear (negative_lift f) -> is_linear f.
  Proof.
    intros H c d g h.
    apply is_monic_delay.
    rewrite !(assoc'_linear _ (delay _)).
    apply (assoc'_linear _ H).
  Qed.

  Definition is_linear_iff_negative_lift {a b : D} (f : a --> b)
    : is_linear f ≃ is_linear (negative_lift f).
  Proof.
    apply weqimplimpl.
    - intro H.
      change (is_linear (f · delay b)).
      apply is_linear_compose; first [exact H | apply (delay _)].
    - apply is_linear_of_negative_lift.
    - apply isaprop_is_linear.
    - apply isaprop_is_linear.
  Defined.

  (** Accessors for positive lift UP in a duploid *)
  Definition positive_lift {a b : D} (f : a <-- b) : linear_mor (⇓b) a.
  Proof.
    use make_linear_mor.
    - apply (positive_lift' D D f).
    - apply is_linear_positive_lift'.
  Defined.

  Lemma positive_lift_factors {a b : D} (f : a <-- b)
    : positive_lift f ∘ wrap b = f.
  Proof.
    apply (positive_lift_factors' _ D).
  Qed.

  Lemma positive_lift_unique {a b : D} (f : a <-- b) (g : a <-- ⇓b)
    : g ∘ wrap b = f ->
      g = positive_lift f.
  Proof.
    apply (positive_lift_from_up_unique _ (has_positive_shifts_has_up _ D)).
  Qed.

  Definition isweq_positive_lift (a b : D) : isweq (λ (f : a <-- b), positive_lift f).
  Proof.
    intro f'.
    use unique_exists.
    3: intro; apply isaset_linear_mor.
    - apply (f' ∘ wrap b).
    - abstract (now apply carrier_eq, pathsinv0, positive_lift_unique).
    - abstract (intros f H;
        apply base_paths in H;
        etrans; [|apply cancel_precomposition, H];
        apply pathsinv0, positive_lift_factors).
  Defined.

  Lemma is_epi_unwrap (a : D) : is_epi (unwrap a).
  Proof.
    intros b f g H.
    refine (!positive_lift_factors f @ _ @ positive_lift_factors g).
    apply cancel_precomposition.
    exact H.
  Qed.

  Definition is_thunkable_of_positive_lift {a b : D} (f : a <-- b)
    : is_thunkable (positive_lift f) -> is_thunkable f.
  Proof.
    intros H c d g h.
    apply is_epi_unwrap.
    rewrite !(assoc_thunkable _ (unwrap _)).
    apply (assoc_thunkable _ H).
  Qed.

  Definition is_thunkable_iff_positive_lift {a b : D} (f : a <-- b)
    : is_thunkable f ≃ is_thunkable (positive_lift f).
  Proof.
    apply weqimplimpl.
    - intro H.
      change (is_thunkable (f ∘ unwrap b)).
      apply is_thunkable_compose; first [exact H | apply (unwrap _)].
    - apply is_thunkable_of_positive_lift.
    - apply isaprop_is_thunkable.
    - apply isaprop_is_thunkable.
  Defined.

End derived_props.

(********************************************************************************

 Definition of [pre]duploids.

 Contents:
 1. Polarity shifts
 2. Polarization choices
 3. Definition of a preduploid
 4. Definition of a duploid

 Author: B. Szilvasy
 January 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Duploids.Magmoids.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Declare Scope duploid.
Delimit Scope duploid with duploid.
Local Open Scope duploid.
Local Open Scope cat.

(** ** 1. Polarity shifts *)

Section shifts.

  (** Upshifts, or negative shifts. *)
  Definition negative_shift_data (M : unital_magmoid) : UU :=
    ∑ upshift : M -> M, ∏ a : M, upshift a --> a.
  Definition make_negative_shift_data {M : unital_magmoid}
    (upshift : M -> M) (force : ∏ (a : M), upshift a --> a)
    : negative_shift_data M :=
    upshift,,force.
  Definition upshift' {M : unital_magmoid} (D : negative_shift_data M) : M -> M := pr1 D.
  Definition force' {M : unital_magmoid} (D : negative_shift_data M) (a : M) : upshift' D a --> a := pr2 D a.

  Definition negative_shift_axioms {M : unital_magmoid} (D : negative_shift_data M) : UU
    := (∏ (a : M), is_linear (force' D a)) ×
         (∏ (a : M), is_negative (upshift' D a)) ×
         (∏ (a : M), has_linear_inverse (force' D a)).

  Definition make_negative_shift_axioms {M : unital_magmoid} {D : negative_shift_data M}
    (H1 : ∏ a : M, is_linear (force' D a))
    (H2 : ∏ a : M, is_negative (upshift' D a))
    (H3 : ∏ a : M, has_linear_inverse (force' D a))
    : negative_shift_axioms D
    := H1,,H2,,H3.

  Definition is_linear_force' {M : unital_magmoid} {D : negative_shift_data M}
    (H : negative_shift_axioms D) (a : M) : is_linear (force' D a) := pr1 H a.
  Definition is_negative_upshift' {M : unital_magmoid} {D : negative_shift_data M}
    (H : negative_shift_axioms D) (a : M) : is_negative (upshift' D a) := pr12 H a.
  Definition has_linear_inverse_force' {M : unital_magmoid} {D : negative_shift_data M}
    (H : negative_shift_axioms D) (a : M) : has_linear_inverse (force' D a) := pr22 H a.

  Lemma isaprop_negative_shift_axioms {M : unital_magmoid} (D : negative_shift_data M)
    : isaprop (negative_shift_axioms D).
  Proof.
    refine (isapropdirprod _ _ _ (isapropdirprod _ _ _ _));
      apply impred; intro a.
    - apply isaprop_is_linear.
    - apply isaprop_is_negative.
    - apply isaprop_has_linear_inverse.
  Qed.

  Definition has_negative_shifts (M : unital_magmoid) : UU
    := ∑ (D : negative_shift_data M), negative_shift_axioms D.
  Definition make_has_negative_shifts {M : unital_magmoid}
    (D : negative_shift_data M) (H : negative_shift_axioms D)
    : has_negative_shifts M := D,,H.
  Coercion has_negative_shifts_to_negative_shift_data (M : unital_magmoid)
    (H : has_negative_shifts M) : negative_shift_data M := pr1 H.
  Coercion has_negative_shifts_to_negative_shift_axioms (M : unital_magmoid)
    (H : has_negative_shifts M) : negative_shift_axioms H := pr2 H.

  (** Downshifts, or positive shifts. *)
  Definition positive_shift_data (M : unital_magmoid) : UU :=
    ∑ downshift : M -> M, ∏ a : M, downshift a <-- a.
  Definition make_positive_shift_data {M : unital_magmoid}
    (downshift : M -> M) (wrap : ∏ (a : M), downshift a <-- a)
    : positive_shift_data M :=
    downshift,,wrap.
  Definition downshift' {M : unital_magmoid} (D : positive_shift_data M) : M -> M := pr1 D.
  Definition wrap' {M : unital_magmoid} (D : positive_shift_data M) (a : M) : downshift' D a <-- a := pr2 D a.

  Definition positive_shift_axioms {M : unital_magmoid} (D : positive_shift_data M) : UU
    := (∏ (a : M), is_thunkable (wrap' D a)) ×
         (∏ (a : M), is_positive (downshift' D a)) ×
         (∏ (a : M), has_thunkable_inverse (wrap' D a)).

  Definition make_positive_shift_axioms {M : unital_magmoid} {D : positive_shift_data M}
    (H1 : ∏ a : M, is_thunkable (wrap' D a))
    (H2 : ∏ a : M, is_positive (downshift' D a))
    (H3 : ∏ a : M, has_thunkable_inverse (wrap' D a))
    : positive_shift_axioms D
    := H1,,H2,,H3.

  Definition is_thunkable_wrap' {M : unital_magmoid} {D : positive_shift_data M}
    (H : positive_shift_axioms D) (a : M) : is_thunkable (wrap' D a) := pr1 H a.
  Definition is_positive_downshift' {M : unital_magmoid} {D : positive_shift_data M}
    (H : positive_shift_axioms D) (a : M) : is_positive (downshift' D a) := pr12 H a.
  Definition has_thunkable_inverse_wrap' {M : unital_magmoid} {D : positive_shift_data M}
    (H : positive_shift_axioms D) (a : M) : has_thunkable_inverse (wrap' D a) := pr22 H a.

  Lemma isaprop_positive_shift_axioms {M : unital_magmoid} (D : positive_shift_data M)
    : isaprop (positive_shift_axioms D).
  Proof.
    refine (isapropdirprod _ _ _ (isapropdirprod _ _ _ _));
      apply impred; intro a.
    - apply isaprop_is_thunkable.
    - apply isaprop_is_positive.
    - apply isaprop_has_thunkable_inverse.
  Qed.

  Definition has_positive_shifts (M : unital_magmoid) : UU
    := ∑ (D : positive_shift_data M), positive_shift_axioms D.
  Definition make_has_positive_shifts {M : unital_magmoid}
    (D : positive_shift_data M) (H : positive_shift_axioms D)
    : has_positive_shifts M := D,,H.
  Coercion has_positive_shifts_to_positive_shift_data (M : unital_magmoid)
    (H : has_positive_shifts M) : positive_shift_data M := pr1 H.
  Coercion has_positive_shifts_to_positive_shift_axioms (M : unital_magmoid)
    (H : has_positive_shifts M) : positive_shift_axioms H := pr2 H.

  (** Combined shifts *)
  Definition has_polarity_shifts (M : unital_magmoid) : UU
    := has_negative_shifts M × has_positive_shifts M.
  Definition make_has_polarity_shifts {M : unital_magmoid}
    (H1 : has_negative_shifts M)
    (H2 : has_positive_shifts M)
    : has_polarity_shifts M := H1,,H2.
  Coercion has_polarity_shifts_to_has_negative_shifts {M : unital_magmoid}
    (H : has_polarity_shifts M) : has_negative_shifts M := pr1 H.
  Coercion has_polarity_shifts_to_has_positive_shifts {M : unital_magmoid}
    (H : has_polarity_shifts M) : has_positive_shifts M := pr2 H.

End shifts.

(** ** 2. Polarization choices *)

Section polarity.

  (* Property to say that a is negative, positive, or both. *)
  Definition has_polarity {M : unital_premagmoid} (a : M) : UU
    := ∥ is_negative a ⨿ is_positive a ∥.
  Definition make_has_negative_polarity {M : unital_premagmoid} (a : M)
    (H : is_negative a) : has_polarity a := hinhpr (inl H).
  Definition make_has_positive_polarity {M : unital_premagmoid} (a : M)
    (H : is_positive a) : has_polarity a := hinhpr (inr H).

  Lemma isaprop_has_polarity {M : unital_premagmoid} (a : M) : isaprop (has_polarity a).
  Proof. apply isapropishinh. Qed.

  Definition has_polarities (M : unital_premagmoid) : UU
    := ∏ (a : M), has_polarity a.
  Definition polarity_of {M : unital_premagmoid} (H : has_polarities M) (a : M)
    : has_polarity a := H a.

  Lemma isaprop_has_polarities (M : unital_premagmoid) : isaprop (has_polarities M).
  Proof. apply impred; intro a; apply isaprop_has_polarity. Qed.

  (* Non-dependent induction schemes for polarities. *)
  Lemma has_polarity_rec {M : unital_premagmoid}
    {a : M} (H : has_polarity a)
    {P : UU} (HP : isaprop P)
    (H1 : ∏ (negp : is_negative a), P)
    (H2 : ∏ (posp : is_positive a), P)
    : P.
  Proof.
    refine (factor_through_squash HP _ H).
    intro H'; induction H'.
    - now apply H1.
    - now apply H2.
  Defined.

End polarity.

(** ** 3. Definition of a preduploid *)
Definition preduploid : UU
  := ∑ (M : unital_magmoid), has_polarities M.
Definition make_preduploid (M : unital_magmoid)
  (H : has_polarities M) : preduploid := M,,H.
Coercion preduploid_to_unital_magmoid (D : preduploid) : unital_magmoid := pr1 D.
Coercion preduploid_has_polarities (D : preduploid) : has_polarities D := pr2 D.

(** ** 4. Definition of a duploid *)
Definition duploid : UU
  := ∑ (M : preduploid), has_polarity_shifts M.
Definition make_duploid (M : preduploid)
  (H : has_polarity_shifts M) : duploid := M,,H.
Coercion duploid_to_preduploid (D : duploid) : preduploid := pr1 D.
Coercion duploid_has_polarity_shifts (D : duploid) : has_polarity_shifts D := pr2 D.

(** Upshifts *)
Definition upshift {D : duploid} (a : D) : negative_ob D
  := make_negative_ob (upshift' D a) (is_negative_upshift' D a).
Notation "'⇑' a" := (upshift a) (at level 40) : duploid.
  (* type in Emacs using agda-input with \Uparrow *)
Definition force {D : duploid} (a : D) : linear_mor (⇑a) a
  := make_linear_mor (force' D a) (is_linear_force' D a).
Definition delay {D : duploid} (a : D) : linear_mor a (⇑a)
  := has_linear_inverse_force' D a.
Definition are_inverses_force_delay {D : duploid} (a : D)
  : is_inverse_in_precat (force a) (delay a)
  := has_linear_inverse_force' D a.

(** Downshifts *)
Definition downshift {D : duploid} (a : D) : positive_ob D
  := make_positive_ob (downshift' D a) (is_positive_downshift' D a).
Notation "'⇓' a" := (downshift a) (at level 40) : duploid.
  (* type in Emacs using agda-input with \Downarrow *)
Definition wrap {D : duploid} (a : D) : thunkable_mor a (⇓a)
  := make_thunkable_mor (wrap' D a) (is_thunkable_wrap' D a).
Definition unwrap {D : duploid} (a : D) : thunkable_mor (⇓a) a
  := has_thunkable_inverse_wrap' D a.
Definition are_inverses_wrap_unwrap {D : duploid} (a : D)
  : is_inverse_in_precat (wrap a) (unwrap a)
  := has_thunkable_inverse_wrap' D a.

Section shift_lemmas.
  Context {C : duploid}.

  (* [force] and [delay] lemmas. *)
  Lemma force_delay_id (a : C) : force a · delay a = identity (⇑a).
  Proof. apply is_inverse_in_precat1, are_inverses_force_delay. Defined.
  Lemma delay_force_id (a : C) : delay a · force a = identity a.
  Proof. apply is_inverse_in_precat2, are_inverses_force_delay. Defined.
  Lemma delay_force_right {a b : C} (f : a --> b) : (f · delay b) · force b = f.
  Proof. now rewrite (assoc'_linear _ (force b)), delay_force_id, magmoid_id_right. Qed.
  Lemma delay_force_left {a b : C} (f : a --> b) : delay a · (force a · f) = f.
  Proof. now rewrite (assoc_negative _ (⇑a)), delay_force_id, magmoid_id_left. Qed.
  Lemma delay_force_interpose {a b c : C} (f : a --> b) (g : b --> c)
    : (f · delay b) · (force b · g) = f · g.
  Proof. now rewrite (assoc_negative _ (⇑b)), delay_force_right. Qed.

  (* [wrap] and [unwrap] lemmas. *)
  Lemma wrap_unwrap_id (a : C) : wrap a · unwrap a = identity a.
  Proof. apply is_inverse_in_precat1, are_inverses_wrap_unwrap. Defined.
  Lemma unwrap_wrap_id (a : C) : unwrap a · wrap a = identity (⇓a).
  Proof. apply is_inverse_in_precat2, are_inverses_wrap_unwrap. Defined.
  Lemma wrap_unwrap_right {a b : C} (f : a <-- b) : (f · wrap a) · unwrap a = f.
  Proof. now rewrite (assoc'_positive _ (⇓a)), wrap_unwrap_id, magmoid_id_right. Qed.
  Lemma wrap_unwrap_left {a b : C} (f : a <-- b) : wrap b · (unwrap b · f) = f.
  Proof. now rewrite (assoc_thunkable _ (wrap b)), wrap_unwrap_id, magmoid_id_left. Qed.
  Lemma wrap_unwrap_interpose {a b c : C} (f : a --> b) (g : b --> c)
    : (f · wrap b) · (unwrap b · g) = f · g.
  Proof. now rewrite (assoc'_positive _ (⇓b)), wrap_unwrap_left. Qed.

  (** Characterisation of thunkable and linear morphisms *)

  Lemma is_thunkable_of_delay_wrap {a b : C} (f : a --> b)
    : f · (delay b · wrap (⇑b)) = (f · delay b) · wrap (⇑b) ->
      is_thunkable f.
  Proof.
    intros Hf.
    assert (H' : ∏ (d : C) (h : ⇑b --> d), f · (delay b · h) = (f · delay b) · h). {
      intros d h.
      rewrite <- (wrap_unwrap_interpose (delay b) h).
      rewrite (assoc_positive _ (⇓⇑b)), Hf.
      rewrite (assoc'_negative _ (⇑b)).
      now rewrite wrap_unwrap_left.
    }
    intros c d g h.
    intermediate_path (f · (delay b · (force b · g) · h)).
    1: now rewrite delay_force_left.
    rewrite (assoc'_negative _ (⇑b)), H'.
    rewrite (assoc_negative _ (⇑b)), <- H'.
    now rewrite delay_force_left.
  Qed.

  Lemma is_linear_of_force_unwrap {a b : C} (f : b --> a)
    : (force (⇓b) · unwrap b) · f = force (⇓b) · (unwrap b · f) ->
      is_linear f.
  Proof.
    intros Hf.
    assert (H' : ∏ (d : C) (h : d --> ⇓b), (h · unwrap b) · f = h · (unwrap b · f)). {
      intros d h.
      rewrite <- (delay_force_interpose h (unwrap b)).
      rewrite (assoc'_negative _ (⇑⇓b)), Hf.
      rewrite (assoc_positive _ (⇓b)).
      now rewrite delay_force_right.
    }
    intros c d g h.
    intermediate_path ((h · ((g · wrap b) · unwrap b)) · f).
    1: now rewrite wrap_unwrap_right.
    rewrite (assoc_positive _ (⇓b)), H'.
    rewrite (assoc'_positive _ (⇓b)), <- H'.
    now rewrite wrap_unwrap_right.
  Qed.
End shift_lemmas.

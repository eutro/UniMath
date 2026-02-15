(********************************************************************************

 [Pre]duploids

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Polarity shifts
 2. Polarization property
 3. Definition of a preduploid
 4. Definition of a duploid
 5. Lemmas about shifts

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.

Local Open Scope cat.
Local Open Scope unital_magmoid.

Declare Scope duploid.
Delimit Scope duploid with duploid.
Local Open Scope duploid.

(** ** 1. Polarity shifts *)

Section shifts.

  (** Upshifts, or negative shifts. *)
  Definition negative_shift_data (M : unital_magmoid) : UU :=
    ∏ a : M, ∑ upshift : M, upshift --> a.
  Definition make_negative_shift_data {M : unital_magmoid}
    (upshift : M -> M) (force : ∏ (a : M), upshift a --> a)
    : negative_shift_data M :=
    λ a, upshift a,,force a.
  Definition upshift' {M : unital_magmoid} (D : negative_shift_data M) : M -> M := λ a, pr1 (D a).
  Definition force' {M : unital_magmoid} (D : negative_shift_data M) (a : M) : upshift' D a --> a := pr2 (D a).

  Lemma negative_shift_data_eq {M : unital_magmoid} (D D' : negative_shift_data M)
    (H1 : ∏ a, upshift' D a = upshift' D' a)
    (H2 : ∏ a, transportf (λ u, u --> a) (H1 a) (force' D a) = force' D' a)
    : D = D'.
  Proof.
    apply funextsec; intro a.
    apply (total2_paths_f (H1 a) (H2 a)).
  Defined.

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
  Definition delay' {M : unital_magmoid} {D : negative_shift_data M}
    (H : negative_shift_axioms D) (a : M) : has_linear_inverse (force' D a) := pr22 H a.
  Definition has_linear_inverse_force' {M : unital_magmoid} {D : negative_shift_data M}
    (H : negative_shift_axioms D) (a : M) : is_inverse_in_precat (force' D a) (delay' H a) :=
    has_linear_inverse_is_inverse _ (delay' H a).

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

  Lemma upshift_unique_up_to_lt_iso (M : unital_magmoid)
    (U1 U2 : has_negative_shifts M) (a : M)
    : lt_iso (upshift' U1 a) (upshift' U2 a).
  Proof.
    use make_lt_iso; [|use make_is_lt_iso'].
    1,3: refine (force' _ a · delay' _ a); first [exact U2|exact U1].
    1,2: abstract (
             apply make_is_linear_and_thunkable;
             first [ apply is_thunkable_of_negative, is_negative_upshift'
                   | apply is_linear_compose; first [ apply is_linear_force' | apply linear_mor_is_linear ] ];
             first [apply U2|apply U1]).
    apply make_is_inverse_in_precat.
    all: abstract (
             etrans; [apply assoc_linear, linear_mor_is_linear|];
             etrans; [apply cancel_postcomposition, assoc'_linear, is_linear_force'; first [apply U2|apply U1]|];
             etrans; [apply cancel_postcomposition, cancel_precomposition, has_linear_inverse_is_inverse|];
             etrans; [apply cancel_postcomposition, magmoid_id_right|];
             apply has_linear_inverse_is_inverse).
  Defined.

  Lemma force_unique_up_to_lt_iso (M : unital_magmoid)
    (U1 U2 : has_negative_shifts M) (a : M)
    : upshift_unique_up_to_lt_iso M _ _ a · force' U2 a = force' U1 a.
  Proof.
    etrans; [apply assoc'_linear, is_linear_force', U2|].
    etrans; [apply cancel_precomposition, has_linear_inverse_is_inverse|].
    apply magmoid_id_right.
  Qed.

  (** Downshifts, or positive shifts. *)
  Definition positive_shift_data (M : unital_magmoid) : UU :=
    ∏ a : M, ∑ downshift : M, downshift <-- a.
  Definition make_positive_shift_data {M : unital_magmoid}
    (downshift : M -> M) (wrap : ∏ (a : M), downshift a <-- a)
    : positive_shift_data M :=
    λ a, downshift a,,wrap a.
  Definition downshift' {M : unital_magmoid} (D : positive_shift_data M) : M -> M := λ a, pr1 (D a).
  Definition wrap' {M : unital_magmoid} (D : positive_shift_data M) (a : M) : downshift' D a <-- a := pr2 (D a).

  Lemma positive_shift_data_eq {M : unital_magmoid} (D D' : positive_shift_data M)
    (H1 : ∏ a, downshift' D a = downshift' D' a)
    (H2 : ∏ a, transportf (λ u, u <-- a) (H1 a) (wrap' D a) = wrap' D' a)
    : D = D'.
  Proof.
    apply funextsec; intro a.
    apply (total2_paths_f (H1 a) (H2 a)).
  Defined.

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
  Definition unwrap' {M : unital_magmoid} {D : positive_shift_data M}
    (H : positive_shift_axioms D) (a : M) : has_thunkable_inverse (wrap' D a) := pr22 H a.
  Definition has_thunkable_inverse_wrap' {M : unital_magmoid} {D : positive_shift_data M}
    (H : positive_shift_axioms D) (a : M) : is_inverse_in_precat (unwrap' H a) (wrap' D a) :=
    has_thunkable_inverse_is_inverse _ (unwrap' H a).

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

  Lemma downshift_unique_up_to_lt_iso (M : unital_magmoid)
    (U1 U2 : has_positive_shifts M) (a : M)
    : lt_iso (downshift' U1 a) (downshift' U2 a).
  Proof.
    use make_lt_iso; [|use make_is_lt_iso'].
    1,3: refine (wrap' _ a ∘ unwrap' _ a); first [exact U2|exact U1].
    1,2: abstract (
             apply make_is_linear_and_thunkable;
             first [ apply is_linear_of_positive, is_positive_downshift'
                   | apply is_thunkable_compose; first [ apply is_thunkable_wrap' | apply thunkable_mor_is_thunkable ] ];
             first [apply U2|apply U1]).
    apply make_is_inverse_in_precat.
    all: abstract (
             etrans; [apply assoc'_thunkable, thunkable_mor_is_thunkable|];
             etrans; [apply cancel_precomposition, assoc_thunkable, is_thunkable_wrap'; first [apply U2|apply U1]|];
             etrans; [apply cancel_precomposition, cancel_postcomposition, has_thunkable_inverse_is_inverse|];
             etrans; [apply cancel_precomposition, magmoid_id_left|];
             apply has_thunkable_inverse_is_inverse).
  Defined.

  Lemma wrap_unique_up_to_lt_iso (M : unital_magmoid)
    (U1 U2 : has_positive_shifts M) (a : M)
    : downshift_unique_up_to_lt_iso M _ _ a ∘ wrap' U2 a = wrap' U1 a.
  Proof.
    etrans; [apply assoc_thunkable, is_thunkable_wrap', U2|].
    etrans; [apply cancel_postcomposition, has_thunkable_inverse_is_inverse|].
    apply magmoid_id_left.
  Qed.

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

(** ** 2. Polarization property *)

Section polarities.

  (** Property to say that a is negative, positive, or both. *)
  Definition has_polarity {M : unital_premagmoid} (a : M) : UU
    := ∥ is_negative a ⨿ is_positive a ∥.
  Definition make_has_polarity_negative {M : unital_premagmoid} (a : M)
    (H : is_negative a) : has_polarity a := hinhpr (ii1 H).
  Definition make_has_polarity_positive {M : unital_premagmoid} (a : M)
    (H : is_positive a) : has_polarity a := hinhpr (ii2 H).

  Lemma isaprop_has_polarity {M : unital_premagmoid} (a : M) : isaprop (has_polarity a).
  Proof. apply isapropishinh. Qed.

  Definition has_polarities (M : unital_premagmoid) : UU
    := ∏ (a : M), has_polarity a.
  Definition polarity_of {M : unital_premagmoid} (H : has_polarities M) (a : M)
    : has_polarity a := H a.

  Lemma isaprop_has_polarities (M : unital_premagmoid) : isaprop (has_polarities M).
  Proof. apply impred; intro a; apply isaprop_has_polarity. Qed.

  (** Non-dependent induction scheme for polarities. *)
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

  (** Dependent induction scheme for polarities. *)
  Lemma has_polarity_rec' {M : unital_premagmoid}
    {a : M} (H : has_polarity a)
    {P : has_polarity a -> UU}
    (HP : isPredicate P)
    (H1 : ∏ (negp : is_negative a), P (hinhpr (ii1 negp)))
    (H2 : ∏ (posp : is_positive a), P (hinhpr (ii2 posp)))
    : P H.
  Proof.
    apply (squash_rec (λ a, make_hProp (P a) (HP a))).
    intro H'; induction H'.
    - now apply H1.
    - now apply H2.
  Defined.

End polarities.

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
  := delay' D a.
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
  := unwrap' D a.
Definition are_inverses_unwrap_wrap {D : duploid} (a : D)
  : is_inverse_in_precat (unwrap a) (wrap a)
  := has_thunkable_inverse_wrap' D a.

(** ** 5. Lemmas about shifts *)

Section shift_lemmas.
  Context {D : duploid}.

  (* [force] and [delay] lemmas. *)
  Lemma force_delay_id (a : D) : force a · delay a = identity (⇑a).
  Proof. apply is_inverse_in_precat1, are_inverses_force_delay. Defined.
  Lemma delay_force_id (a : D) : delay a · force a = identity a.
  Proof. apply is_inverse_in_precat2, are_inverses_force_delay. Defined.
  Lemma delay_force_right {a b : D} (f : a --> b) : (f · delay b) · force b = f.
  Proof. now rewrite (assoc'_linear _ (force b)), delay_force_id, magmoid_id_right. Qed.
  Lemma delay_force_left {a b : D} (f : a --> b) : delay a · (force a · f) = f.
  Proof. now rewrite (assoc_negative _ (⇑a)), delay_force_id, magmoid_id_left. Qed.
  Lemma delay_force_interpose {a b c : D} (f : a --> b) (g : b --> c)
    : (f · delay b) · (force b · g) = f · g.
  Proof. now rewrite (assoc_negative _ (⇑b)), delay_force_right. Qed.

  (* [wrap] and [unwrap] lemmas. *)
  Lemma unwrap_wrap_id (a : D) : unwrap a · wrap a = identity (⇓a).
  Proof. apply is_inverse_in_precat1, are_inverses_unwrap_wrap. Defined.
  Lemma wrap_unwrap_id (a : D) : wrap a · unwrap a = identity a.
  Proof. apply is_inverse_in_precat2, are_inverses_unwrap_wrap. Defined.
  Lemma wrap_unwrap_right {a b : D} (f : a <-- b) : (f · wrap a) · unwrap a = f.
  Proof. now rewrite (assoc'_positive _ (⇓a)), wrap_unwrap_id, magmoid_id_right. Qed.
  Lemma wrap_unwrap_left {a b : D} (f : a <-- b) : wrap b · (unwrap b · f) = f.
  Proof. now rewrite (assoc_thunkable _ (wrap b)), wrap_unwrap_id, magmoid_id_left. Qed.
  Lemma wrap_unwrap_interpose {a b c : D} (f : a --> b) (g : b --> c)
    : (f · wrap b) · (unwrap b · g) = f · g.
  Proof. now rewrite (assoc'_positive _ (⇓b)), wrap_unwrap_left. Qed.

  (** Characterisation of thunkable and linear morphisms *)

  Lemma is_thunkable_of_delay_wrap {a b : D} (f : a --> b)
    : f · (delay b · wrap (⇑b)) = (f · delay b) · wrap (⇑b) ->
      is_thunkable f.
  Proof.
    intros Hf.
    assert (H' : ∏ (d : D) (h : ⇑b --> d), f · (delay b · h) = (f · delay b) · h). {
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

  Lemma is_thunkable_iff_delay_wrap {a b : D} (f : a --> b)
    : f · (delay b · wrap (⇑b)) = (f · delay b) · wrap (⇑b) <->
        is_thunkable f.
  Proof.
    split.
    - apply is_thunkable_of_delay_wrap.
    - intro H; apply assoc_thunkable, H.
  Qed.

  Lemma is_linear_of_force_unwrap {a b : D} (f : b --> a)
    : (force (⇓b) · unwrap b) · f = force (⇓b) · (unwrap b · f) ->
      is_linear f.
  Proof.
    intros Hf.
    assert (H' : ∏ (d : D) (h : d --> ⇓b), (h · unwrap b) · f = h · (unwrap b · f)). {
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

  Lemma is_linear_iff_force_unwrap {a b : D} (f : a <-- b)
    : (force (⇓b) · unwrap b) · f = force (⇓b) · (unwrap b · f) <->
        is_linear f.
  Proof.
    split.
    - apply is_linear_of_force_unwrap.
    - intro H; apply assoc'_linear, H.
  Qed.

  (** Characterisation of positive and negative objects *)

  (** For an object [a], the following statements are equivalent:
  1. [a] is positive
  2. [wrap a] is linear
  3. [wrap a] is a linear-and-thunkable isomorphism *)

  Lemma is_linear_unwrap (a : D) : is_linear (unwrap a).
  Proof. apply is_linear_of_positive, (⇓a). Qed.
  Lemma is_linear_and_thunkable_unwrap (a : D) : is_linear_and_thunkable (unwrap a).
  Proof. apply make_is_linear_and_thunkable; first [apply is_linear_unwrap|apply (unwrap a)]. Qed.
  (** 1 -> 2 *)
  Lemma is_linear_wrap_of_positive (a : D) (H : is_positive a) : is_linear (wrap a).
  Proof. apply is_linear_of_positive, H. Qed.
  Lemma is_linear_and_thunkable_wrap_of_positive (a : D) (H : is_positive a) : is_linear_and_thunkable (wrap a).
  Proof. apply make_is_linear_and_thunkable; first [apply is_linear_wrap_of_positive, H|apply (wrap a)]. Qed.

  (** 2 -> 3 *)
  Lemma is_lt_iso_wrap_of_linear (a : D) (H : is_linear (wrap a)) : is_lt_iso (wrap a).
  Proof.
    use make_is_lt_iso'.
    - abstract (apply make_is_linear_and_thunkable; first [exact H|apply (wrap a)]).
    - exact (unwrap a).
    - abstract (apply is_linear_and_thunkable_unwrap).
    - abstract (split; apply are_inverses_unwrap_wrap).
  Defined.

  (** 1 -> 3 *)
  Lemma is_lt_iso_wrap_of_positive (a : D) (H : is_positive a) : is_lt_iso (wrap a).
  Proof.
    apply is_lt_iso_wrap_of_linear.
    abstract (apply is_linear_of_positive, H).
  Defined.

  (** 2 -> 1 (via 3) *)
  Lemma is_positive_of_linear_wrap (a : D) (H : is_linear (wrap a)) : is_positive a.
  Proof.
    refine (is_positive_of_lt_iso _ (⇓a)).
    eapply lt_iso_inv, make_lt_iso, is_lt_iso_wrap_of_linear, H.
  Qed.

  Lemma is_positive_iff_linear_wrap (a : D) : is_linear (wrap a) <-> is_positive a.
  Proof.
    split.
    - apply is_positive_of_linear_wrap.
    - apply is_linear_wrap_of_positive.
  Qed.

  (** 3 *)
  Lemma lt_iso_downshift_of_positive (a : D) (H : is_positive a) : lt_iso a (⇓a).
  Proof.
    exact (make_lt_iso _ (is_lt_iso_wrap_of_positive a H)).
  Defined.

  Lemma is_lt_iso_unwrap_of_positive (a : D) (H : is_positive a) : is_lt_iso (unwrap a).
  Proof.
    exact (lt_iso_is_lt_iso (lt_iso_inv (lt_iso_downshift_of_positive a H))).
  Defined.

  Lemma is_lt_iso_unwrap_of_linear (a : D) (H : is_linear (wrap a)) : is_lt_iso (unwrap a).
  Proof.
    apply is_lt_iso_unwrap_of_positive, is_positive_of_linear_wrap, H.
  Defined.

  (** For an object [a], the following statements are equivalent:
  1. [a] is negative
  2. [force a] is thunkable
  3. [force a] is a thunkable-and-linear isomorphism *)

  Lemma is_thunkable_delay (a : D) : is_thunkable (delay a).
  Proof. apply is_thunkable_of_negative, (⇑a). Qed.
  Lemma is_linear_and_thunkable_delay (a : D) : is_linear_and_thunkable (delay a).
  Proof. apply make_is_linear_and_thunkable; first [apply is_thunkable_delay|apply (delay a)]. Qed.
  (** 1 -> 2 *)
  Lemma is_thunkable_force_of_negative (a : D) (H : is_negative a) : is_thunkable (force a).
  Proof. apply is_thunkable_of_negative, H. Qed.
  Lemma is_linear_and_thunkable_force_of_negative (a : D) (H : is_negative a) : is_linear_and_thunkable (force a).
  Proof. apply make_is_linear_and_thunkable; first [apply is_thunkable_force_of_negative, H|apply (force a)]. Qed.

  (** 2 -> 3 *)
  Lemma is_lt_iso_force_of_thunkable (a : D) (H : is_thunkable (force a)) : is_lt_iso (force a).
  Proof.
    use make_is_lt_iso'.
    - abstract (apply make_is_linear_and_thunkable; first [exact H|apply (force a)]).
    - exact (delay a).
    - abstract (apply is_linear_and_thunkable_delay).
    - abstract (apply are_inverses_force_delay).
  Defined.

  (** 1 -> 3 *)
  Lemma is_lt_iso_force_of_negative (a : D) (H : is_negative a) : is_lt_iso (force a).
  Proof.
    apply is_lt_iso_force_of_thunkable.
    abstract (apply is_thunkable_of_negative, H).
  Defined.

  (** 2 -> 1 (via 3) *)
  Lemma is_negative_of_thunkable_force (a : D) (H : is_thunkable (force a)) : is_negative a.
  Proof.
    refine (is_negative_of_lt_iso _ (⇑a)).
    eapply make_lt_iso, is_lt_iso_force_of_thunkable, H.
  Qed.

  Lemma is_negative_iff_thunkable_force (a : D) : is_thunkable (force a) <-> is_negative a.
  Proof.
    split.
    - apply is_negative_of_thunkable_force.
    - apply is_thunkable_force_of_negative.
  Qed.

  (** 3 *)
  Lemma lt_iso_upshift_of_negative (a : D) (H : is_negative a) : lt_iso (⇑a) a.
  Proof.
    exact (make_lt_iso _ (is_lt_iso_force_of_negative a H)).
  Defined.

  Lemma is_lt_iso_delay_of_negative (a : D) (H : is_negative a) : is_lt_iso (delay a).
  Proof.
    exact (lt_iso_is_lt_iso (lt_iso_inv (lt_iso_upshift_of_negative a H))).
  Defined.

  Lemma is_lt_iso_delay_of_thunkable (a : D) (H : is_thunkable (force a)) : is_lt_iso (delay a).
  Proof.
    apply is_lt_iso_delay_of_negative, is_negative_of_thunkable_force, H.
  Defined.

End shift_lemmas.

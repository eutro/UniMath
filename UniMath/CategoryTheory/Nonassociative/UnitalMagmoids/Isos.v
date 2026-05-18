(********************************************************************************

 Isomorphisms in Unital Magmoids

 Contents:
 1. Inverses in wide submagmoids
 2. Specific inverses and when they are unique
 3. Composition of inverses when they exist
 4. Linear-and-thunkable (and other) isomorphisms [lt_iso]
 5. Lemmas about isomorphisms

 Author: B. Szilvasy
 January 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Opposite.

Local Open Scope cat.

(** ** 1. Inverses in wide submagmoids *)

Lemma isaprop_is_inverse_in_precat_of_magmoid
  {M : unital_magmoid} {a b : M} (f : a --> b) (g : a <-- b) : isaprop (is_inverse_in_precat f g).
Proof. apply isapropdirprod; apply unital_magmoid_has_homsets. Qed.
Definition ish_inverse_in_unital_magmoid
  {M : unital_magmoid} {a b : M} (f : a --> b) (g : a <-- b)
  : hProp
  := make_hProp (is_inverse_in_precat f g) (isaprop_is_inverse_in_precat_of_magmoid f g).

Lemma is_inverse_in_precat_identity_of_magmoid {M : unital_magmoid} (a : M)
  : is_inverse_in_precat (identity a) (identity a).
Proof.
  apply make_is_inverse_in_precat.
  1, 2: apply magmoid_id_left.
Qed.

Section wide_submagmoid_inverses.
  Context {M : unital_magmoid} (P : wide_submagmoid M).

  Definition has_submm_inverse'
    {a b : M} (f : a --> b) : UU
    := ∑ (g : a <-- b), P _ _ g ∧ ish_inverse_in_unital_magmoid f g.
  Definition has_submm_inverse
    {a b : M} (f : a --> b) : UU
    := ∑ (g : P b a), ish_inverse_in_unital_magmoid f (pr1carrier _ g).
  Definition weq_has_submm_inverse'
    {a b : M} (f : a --> b)
    : has_submm_inverse' f ≃ has_submm_inverse f
    := totalAssociativity _.

  Definition submm_inverse'_mor
    {a b : M} {f : a --> b} (g : has_submm_inverse' f)
    : a <-- b := pr1 g.
  Definition submm_inverse'_property
    {a b : M} {f : a --> b} (g : has_submm_inverse' f)
    : P _ _ (submm_inverse'_mor g) := pr12 g.
  Coercion has_submm_inverse'_is_inverse
    {a b : M} {f : a --> b} (g : has_submm_inverse' f)
    : is_inverse_in_precat f (submm_inverse'_mor g) := pr22 g.
  Coercion has_submm_inverse'_to_is_z_isomorphism
    {a b : M} {f : a --> b} (g : has_submm_inverse' f)
    : is_z_isomorphism f
    := make_is_z_isomorphism _ (submm_inverse'_mor g) g.
  Definition make_has_submm_inverse'
    {a b : M} (f : a --> b) (g : a <-- b)
    (Hf : P _ _ g) (Hfg : ish_inverse_in_unital_magmoid f g)
    : has_submm_inverse' f
    := g,, Hf,, Hfg.

  Definition submm_inverse_to_submm
    {a b : M} {f : a --> b} (g : has_submm_inverse f)
    : P b a := pr1 g.
  Definition submm_inverse_mor
    {a b : M} {f : a --> b} (g : has_submm_inverse f)
    : a <-- b := pr1carrier _ (submm_inverse_to_submm g).
  Definition submm_inverse_property
    {a b : M} {f : a --> b} (g : has_submm_inverse f)
    : P _ _ (submm_inverse_mor g)
    := pr2 (submm_inverse_to_submm g).
  Coercion has_submm_inverse_is_inverse
    {a b : M} {f : a --> b} (g : has_submm_inverse f)
    : is_inverse_in_precat f (submm_inverse_mor g) := pr2 g.
  Coercion has_submm_inverse_to_is_z_isomorphism
    {a b : M} {f : a --> b} (g : has_submm_inverse f)
    : is_z_isomorphism f
    := make_is_z_isomorphism _ (submm_inverse_mor g) g.
  Definition make_has_submm_inverse
    {a b : M} (f : a --> b) (g : P b a)
    (Hfg : ish_inverse_in_unital_magmoid f (pr1carrier _ g))
    : has_submm_inverse f
    := g,, Hfg.

  Definition is_submm_iso
    {a b : M} (f : a --> b)
    := P _ _ f × has_submm_inverse f.

  Definition is_submm_iso_property
    {a b : M} {f : a --> b} (g : is_submm_iso f)
    : P _ _ f := pr1 g.
  Coercion is_submm_iso_to_has_submm_inverse
    {a b : M} {f : a --> b} (g : is_submm_iso f)
    : has_submm_inverse f
    := pr2 g.

  Definition submm_iso' (a b : M) : UU
    := ∑ (f : a --> b), is_submm_iso f.
  Definition submm_iso (a b : M) : UU
    := ∑ (f : P a b), has_submm_inverse (pr1carrier _ f).
  Definition weq_submm_iso' (a b : M)
    : submm_iso' a b ≃ submm_iso a b
    := totalAssociativity _.
  Definition weq_submm_iso (a b : M)
    : submm_iso a b ≃ submm_iso' a b
    := invweq (weq_submm_iso' a b).

  Coercion submm_iso'_mor
    {a b : M} (f : submm_iso' a b)
    : a --> b := pr1 f.
  Definition submm_iso'_property
    {a b : M} (f : submm_iso' a b)
    : P _ _ f := pr12 f.
  Coercion submm_iso'_has_submm_inverse
    {a b : M} (f : submm_iso' a b)
    : has_submm_inverse f := pr22 f.
  Definition make_submm_iso' {a b : M}
    (f : a --> b) (Hf : P _ _ f)
    (g : has_submm_inverse f)
    : submm_iso' a b
    := f,, Hf,, g.

  Definition submm_iso_to_submagmoid
    {a b : M} (f : submm_iso a b)
    : P a b := pr1 f.
  Coercion submm_iso_mor
    {a b : M} (f : submm_iso a b)
    : a --> b := pr1carrier _ (submm_iso_to_submagmoid f).
  Definition submm_iso_property
    {a b : M} (f : submm_iso a b)
    : P _ _ f := pr2 (submm_iso_to_submagmoid f).
  Coercion submm_iso_has_submm_inverse
    {a b : M} (f : submm_iso a b)
    : has_submm_inverse f := pr2 f.
  Definition make_submm_iso {a b : M}
    (f : P a b) (g : has_submm_inverse (pr1carrier _ f))
    : submm_iso a b
    := f,, g.

  Definition make_submm_iso_2 {a b : M}
    (f : P a b) (g : P b a)
    (Hfg : is_inverse_in_precat (pr1carrier _ f) (pr1carrier _ g))
    := make_submm_iso f (make_has_submm_inverse _ g Hfg).

  Lemma isincl_submm_iso'_mor (a b : M)
    (H : ∏ (f : submm_iso' a b), isaprop (is_submm_iso f))
    : isincl (@submm_iso'_mor a b).
  Proof.
    apply isinclpr1.
    intro f.
    apply isaprop_assume_it_is.
    intro Hf.
    apply (H (make_submm_iso' f (pr1 Hf) (pr2 Hf))).
  Defined.

  Corollary isaset_submm_iso' (a b : M)
    (H : ∏ (f : submm_iso' a b), isaprop (is_submm_iso f))
    : isaset (submm_iso' a b).
  Proof.
    apply (isasetsubset (@submm_iso'_mor a b)).
    - apply unital_magmoid_has_homsets.
    - apply isincl_submm_iso'_mor, H.
  Qed.

  Lemma isincl_submm_iso_mor (a b : M)
    (H : ∏ (f : submm_iso a b), isaprop (is_submm_iso f))
    : isincl (@submm_iso_mor a b).
  Proof.
    use isofhlevelfhomot.
    - intro f.
      apply submm_iso'_mor.
      apply (weq_submm_iso _ _ f).
    - easy.
    - apply isinclgtogw.
      apply isincl_submm_iso'_mor.
      intro f.
      apply (H (weq_submm_iso' _ _ f)).
  Defined.

  Corollary isaset_submm_iso (a b : M)
    (H : ∏ (f : submm_iso a b), isaprop (is_submm_iso f))
    : isaset (submm_iso a b).
  Proof.
    apply (isasetsubset (@submm_iso_mor a b)).
    - apply unital_magmoid_has_homsets.
    - apply isincl_submm_iso_mor, H.
  Qed.

  Definition submm_iso_inv {a b : M}
    (f : submm_iso a b)
    : submm_iso b a.
  Proof.
    use make_submm_iso_2.
    - apply (submm_inverse_to_submm f).
    - apply (submm_iso_to_submagmoid f).
    - apply is_inverse_in_precat_inv.
      exact f.
  Defined.

  Definition submm_iso'_inv {a b : M}
    (f : submm_iso' a b)
    : submm_iso' b a
    := weq_submm_iso _ _
         (submm_iso_inv
            (weq_submm_iso' _ _ f)).

  Definition is_submm_iso_identity (a : M)
    : is_submm_iso (identity a).
  Proof.
    split.
    - apply wide_submagmoid_identity_holds.
    - use make_has_submm_inverse.
      + exact (wide_submagmoid_identity _ a).
      + apply is_inverse_in_precat_identity_of_magmoid.
  Defined.

  Definition submm_iso_identity (a : M)
    : submm_iso a a.
  Proof.
    use make_submm_iso.
    - exact (wide_submagmoid_identity _ a).
    - exact (is_submm_iso_identity a).
  Defined.

  Definition submm_iso_compose {a b c : M}
    (f : submm_iso a b) (g : submm_iso b c)
    (Hassoc : ∏ (a b c d : M) (f : P a b) (g : P b c) (h : P c d),
                pr1carrier _ f · (pr1carrier _ g · pr1carrier _ h)
                = (pr1carrier _ f · pr1carrier _ g) · pr1carrier _ h)
    : submm_iso a c.
  Proof.
    pose (p := wide_submagmoid_compose _ (submm_iso_to_submagmoid f) (submm_iso_to_submagmoid g)).
    pose (q := wide_submagmoid_compose _ (submm_inverse_to_submm g) (submm_inverse_to_submm f)).
    exists p, q.
    split.
    - abstract (
          etrans; [apply (Hassoc _ _ _ _ p)|];
          etrans; [apply cancel_postcomposition, pathsinv0, Hassoc|];
          etrans; [refine (maponpaths (λ f, _ · f · _) _);
                   apply (is_inverse_in_precat1 g)|];
          rewrite magmoid_id_right;
          apply (is_inverse_in_precat1 f)).
    - abstract (
          etrans; [apply (Hassoc _ _ _ _ q)|];
          etrans; [apply cancel_postcomposition, pathsinv0, Hassoc|];
          etrans; [refine (maponpaths (λ f, _ · f · _) _);
                   apply (is_inverse_in_precat2 f)|];
          rewrite magmoid_id_right;
          apply (is_inverse_in_precat2 g)).
  Defined.

  Definition submm_iso'_identity (a : M)
    : submm_iso' a a
    := weq_submm_iso _ _ (submm_iso_identity a).

  Definition id_to_submm_iso (a b : M) (p : a = b)
    : submm_iso a b.
  Proof.
    induction p; apply submm_iso_identity.
  Defined.

  Definition id_to_submm_iso' (a b : M) (p : a = b)
    : submm_iso' a b.
  Proof.
    induction p; apply submm_iso'_identity.
  Defined.

End wide_submagmoid_inverses.

(** ** 2. Specific inverses and when they are unique *)

Section inverses.
  Context {M : unital_magmoid} {a b : M} (f : a --> b).

  (* Linear inverses are unique *)
  Lemma inverse_unique_linear
    (g g' : a <-- b) (H : is_linear g)
    (Hg : is_inverse_in_precat f g)
    (Hg' : is_inverse_in_precat f g')
    : g = g'.
  Proof.
    refine (!magmoid_id_left _ @ _ @ magmoid_id_right _).
    now rewrite <- (is_inverse_in_precat1 Hg),
      <- (is_inverse_in_precat2 Hg'), (assoc_linear _ H).
  Qed.

  Definition has_linear_inverse : UU
    := ∑ (g : linear_mor b a), is_inverse_in_precat f g.
  Definition make_has_linear_inverse
    (g : linear_mor b a) (H : is_inverse_in_precat f g)
    : has_linear_inverse := g,,H.
  Coercion has_linear_inverse_mor (I : has_linear_inverse) : linear_mor b a := pr1 I.
  Definition has_linear_inverse_is_inverse (I : has_linear_inverse) : is_inverse_in_precat f I := pr2 I.

  Lemma isaprop_has_linear_inverse : isaprop has_linear_inverse.
  Proof.
    apply (isofhlevelweqf 1 (weq_has_submm_inverse' (isw_linear M) f)).
    apply invproofirrelevance; intros g g'.
    apply carrier_eq, inverse_unique_linear.
    - apply g.
    - apply g.
    - apply g'.
  Qed.

  (* Thunkable inverses are unique *)
  Lemma inverse_unique_thunkable
    (g g' : a <-- b) (H : is_thunkable g)
    (Hg : is_inverse_in_precat g f)
    (Hg' : is_inverse_in_precat g' f)
    : g = g'.
  Proof.
    refine (!magmoid_id_right _ @ _ @ magmoid_id_left _).
    now rewrite <- (is_inverse_in_precat1 Hg),
      <- (is_inverse_in_precat2 Hg'), (assoc_thunkable _ H).
  Qed.

  Definition has_thunkable_inverse : UU
    := ∑ (g : thunkable_mor b a), is_inverse_in_precat g f.
  Definition make_has_thunkable_inverse
    (g : thunkable_mor b a) (H : is_inverse_in_precat g f)
    : has_thunkable_inverse := g,,H.
  Coercion has_thunkable_inverse_mor (I : has_thunkable_inverse) : thunkable_mor b a := pr1 I.
  Definition has_thunkable_inverse_is_inverse (I : has_thunkable_inverse) : is_inverse_in_precat I f := pr2 I.

  Lemma isaprop_has_thunkable_inverse : isaprop has_thunkable_inverse.
  Proof.
    apply (isofhlevelweqf 1 (X:=∑ g, ish_thunkable g ∧ ish_inverse_in_unital_magmoid g f)
             (totalAssociativity _)).
    apply invproofirrelevance; intros g g'.
    apply carrier_eq, inverse_unique_thunkable.
    - apply g.
    - apply g.
    - apply g'.
  Qed.

  (* Thunkable-and-linear inverses are of course unique *)
  Definition has_linear_and_thunkable_inverse : UU
    := has_submm_inverse (isw_linear_and_thunkable M) f.
  Definition make_has_linear_and_thunkable_inverse
    (g : linear_and_thunkable_mor b a) (H : is_inverse_in_precat f g)
    : has_linear_and_thunkable_inverse := g,,H.
  Coercion has_linear_and_thunkable_inverse_mor (I : has_linear_and_thunkable_inverse)
    : linear_and_thunkable_mor b a := pr1 I.
  Definition has_linear_and_thunkable_inverse_is_inverse (I : has_linear_and_thunkable_inverse)
    : is_inverse_in_precat f I := pr2 I.
  Coercion has_linear_and_thunkable_inverse_to_has_linear_inverse (I : has_linear_and_thunkable_inverse)
    : has_linear_inverse := make_has_linear_inverse I (has_linear_and_thunkable_inverse_is_inverse I).
  Coercion has_linear_and_thunkable_inverse_to_has_thunkable_inverse (I : has_linear_and_thunkable_inverse)
    : has_thunkable_inverse := make_has_thunkable_inverse I (is_inverse_in_precat_inv (has_linear_and_thunkable_inverse_is_inverse I)).

  Lemma isaprop_has_linear_and_thunkable_inverse : isaprop has_linear_and_thunkable_inverse.
  Proof.
    apply invproofirrelevance; intros g g'.
    apply subtypePath'.
    2: apply isaprop_is_inverse_in_precat_of_magmoid.
    apply carrier_eq.
    set (H := proofirrelevance _ isaprop_has_linear_inverse g g').
    do 2 apply base_paths in H.
    apply H.
  Qed.

  (* If a morphism is intermediate then its inverses are unique. *)
  Lemma inverse_unique_intermediate
    (g g' : a <-- b) (H : is_intermediate f)
    (Hg : is_inverse_in_precat f g)
    (Hg' : is_inverse_in_precat f g')
    : g = g'.
  Proof.
    refine (!magmoid_id_right _ @ _ @ magmoid_id_left _).
    now rewrite <- (is_inverse_in_precat2 Hg),
      <- (is_inverse_in_precat1 Hg'), (assoc_intermediate _ H).
  Qed.

End inverses.

Goal ∏ (M : unital_magmoid) (a b : M) (f : a --> b),
  has_thunkable_inverse (M:=opp_magmoid M) f = has_linear_inverse f.
  reflexivity.
Qed.

Definition opp_magmoid_has_linear_and_thunkable_inverse {M : unital_magmoid} {a b : M} (f : a --> b)
  : has_linear_and_thunkable_inverse (M:=opp_magmoid M) f -> has_linear_and_thunkable_inverse f.
Proof.
  intro H.
  use make_has_linear_and_thunkable_inverse.
  - apply opp_magmoid_linear_and_thunkable_mor; exact H.
  - apply is_inverse_in_precat_inv, (has_linear_and_thunkable_inverse_is_inverse _ H).
Defined.

Lemma isweq_opp_magmoid_has_linear_and_thunkable_inverse {M : unital_magmoid} {a b : M} (f : a --> b)
  : isweq (opp_magmoid_has_linear_and_thunkable_inverse f).
Proof. opp_magmoid_involution. Defined.

(** ** 3. Composition of inverses when they exist *)

Section composition.
  Context {M : unital_magmoid}.

  (** Linear or thunkable inverses have identities. *)

  Definition has_linear_inverse_identity (a : M)
    : has_linear_inverse (identity a).
  Proof.
    use make_has_linear_inverse.
    - apply linear_identity.
    - apply is_inverse_in_precat_identity_of_magmoid.
  Defined.

  Definition has_thunkable_inverse_identity (a : M)
    : has_thunkable_inverse (identity a).
  Proof.
    use make_has_thunkable_inverse.
    - apply thunkable_identity.
    - apply is_inverse_in_precat_identity_of_magmoid.
  Defined.

  Definition has_linear_and_thunkable_inverse_identity (a : M)
    : has_linear_and_thunkable_inverse (identity a).
  Proof.
    use make_has_linear_and_thunkable_inverse.
    - apply linear_and_thunkable_identity.
    - apply is_inverse_in_precat_identity_of_magmoid.
  Defined.

  (** There are multiple ways in which linearity and thunkability permit
      composition of inverses. *)

  Lemma is_inverse_in_magmoid_comp_2linear {a b c : M}
    (f : a --> b) (g : a <-- b) (f' : b --> c) (g' : b <-- c)
    (Hg : is_linear g) (Hg' : is_linear g')
    (H1 : f · g = identity a) (H2 : f' · g' = identity b)
    : (f · f') · (g' · g) = identity a.
  Proof.
    refine (assoc_linear _ Hg _ _ @ _ @ H1).
    apply cancel_postcomposition.
    refine (assoc'_linear _ Hg' _ _ @ _ @ magmoid_id_right f).
    apply cancel_precomposition, H2.
  Qed.

  Lemma is_inverse_in_magmoid_comp_2thunkable {a b c : M}
    (f : a <-- b) (g : a --> b) (f' : b <-- c) (g' : b --> c)
    (Hg : is_thunkable g) (Hg' : is_thunkable g')
    (H1 : f ∘ g = identity a) (H2 : f' ∘ g' = identity b)
    : (f ∘ f') ∘ (g' ∘ g) = identity a.
  Proof.
    refine (assoc'_thunkable _ Hg _ _ @ _ @ H1).
    apply cancel_precomposition.
    refine (assoc_thunkable _ Hg' _ _ @ _ @ magmoid_id_left f).
    apply cancel_postcomposition, H2.
  Qed.

  (** Linear-and-thunkable inverses compose. *)
  Lemma has_linear_and_thunkable_inverse_compose {a b c : M}
    (f : a --> b) (g : has_linear_and_thunkable_inverse f)
    (f' : b --> c) (g' : has_linear_and_thunkable_inverse f')
    : has_linear_and_thunkable_inverse (f · f').
  Proof.
    use make_has_linear_and_thunkable_inverse.
    - apply (linear_and_thunkable_compose g' g).
    - use make_is_inverse_in_precat.
      + apply is_inverse_in_magmoid_comp_2linear.
        * apply (g : linear_mor _ _).
        * apply (g' : linear_mor _ _).
        * apply (is_inverse_in_precat1 (has_linear_and_thunkable_inverse_is_inverse _ g)).
        * apply (is_inverse_in_precat1 (has_linear_and_thunkable_inverse_is_inverse _ g')).
      + apply is_inverse_in_magmoid_comp_2thunkable.
        * apply (g' : thunkable_mor _ _).
        * apply (g : thunkable_mor _ _).
        * apply (is_inverse_in_precat2 (has_linear_and_thunkable_inverse_is_inverse _ g')).
        * apply (is_inverse_in_precat2 (has_linear_and_thunkable_inverse_is_inverse _ g)).
  Defined.

  (** Linear inverses of linear maps compose -- but this is just the linear
      category. *)
  Lemma has_linear_inverse_compose {a b c : M}
    (f : linear_mor a b) (g : has_linear_inverse f)
    (f' : linear_mor b c) (g' : has_linear_inverse f')
    : has_linear_inverse (f · f').
  Proof.
    use make_has_linear_inverse.
    - apply (linear_compose g' g).
    - use make_is_inverse_in_precat.
      + apply is_inverse_in_magmoid_comp_2linear.
        * apply (g : linear_mor _ _).
        * apply (g' : linear_mor _ _).
        * apply (is_inverse_in_precat1 (has_linear_inverse_is_inverse _ g)).
        * apply (is_inverse_in_precat1 (has_linear_inverse_is_inverse _ g')).
      + apply is_inverse_in_magmoid_comp_2linear.
        * apply (f' : linear_mor _ _).
        * apply (f : linear_mor _ _).
        * apply (is_inverse_in_precat2 (has_linear_inverse_is_inverse _ g')).
        * apply (is_inverse_in_precat2 (has_linear_inverse_is_inverse _ g)).
  Defined.

  (** Thunkable inverses of thunkable maps compose -- but this is just the
      thunkable category. *)
  Lemma has_thunkable_inverse_compose {a b c : M}
    (f : thunkable_mor a b) (g : has_thunkable_inverse f)
    (f' : thunkable_mor b c) (g' : has_thunkable_inverse f')
    : has_thunkable_inverse (f · f').
  Proof.
    use make_has_thunkable_inverse.
    - apply (thunkable_compose g' g).
    - use make_is_inverse_in_precat.
      + apply is_inverse_in_magmoid_comp_2thunkable.
        * apply (g' : thunkable_mor _ _).
        * apply (g : thunkable_mor _ _).
        * apply (is_inverse_in_precat1 (has_thunkable_inverse_is_inverse _ g')).
        * apply (is_inverse_in_precat1 (has_thunkable_inverse_is_inverse _ g)).
      + apply is_inverse_in_magmoid_comp_2thunkable.
        * apply (f : thunkable_mor _ _).
        * apply (f' : thunkable_mor _ _).
        * apply (is_inverse_in_precat2 (has_thunkable_inverse_is_inverse _ g)).
        * apply (is_inverse_in_precat2 (has_thunkable_inverse_is_inverse _ g')).
  Defined.

End composition.

(** ** 4. Linear-and-thunkable (and other) isomorphisms [lt_iso] *)

Section isos.
  Context {M : unital_magmoid}.

  Definition is_lt_iso {a b : M} (f : a --> b) : UU
    := is_submm_iso (isw_linear_and_thunkable M) f.

  Definition make_is_lt_iso {a b : M} {f : a --> b}
    (H1 : is_linear_and_thunkable f)
    (g : has_linear_and_thunkable_inverse f)
    : is_lt_iso f
    := H1,, g.

  Definition make_is_lt_iso' {a b : M} {f : a --> b}
    (Hf : is_linear_and_thunkable f)
    (g : b --> a)
    (Hg : is_linear_and_thunkable g)
    (Hfg : is_inverse_in_precat f g)
    : is_lt_iso f
    := make_is_lt_iso Hf
         (make_has_linear_and_thunkable_inverse _
            (make_linear_and_thunkable_mor g Hg)
            Hfg).

  Definition is_lt_iso_to_is_linear_and_thunkable {a b : M} (f : a --> b) (H : is_lt_iso f)
    : is_linear_and_thunkable f := is_submm_iso_property _ H.
  Coercion is_lt_iso_to_has_linear_and_thunkable_inverse {a b : M} (f : a --> b) (H : is_lt_iso f)
    : has_linear_and_thunkable_inverse f := is_submm_iso_to_has_submm_inverse _ H.
  Definition isaprop_is_lt_iso {a b : M} (f : a --> b)
    : isaprop (is_lt_iso f).
  Proof.
    apply isapropdirprod.
    - apply propproperty.
    - apply (isaprop_has_linear_and_thunkable_inverse f).
  Qed.

  Lemma is_lt_iso_identity (a : M) : is_lt_iso (identity a).
  Proof. apply is_submm_iso_identity. Defined.

  Lemma is_lt_iso_compose {a b c : M} (f : a --> b) (g : b --> c)
    (Hf : is_lt_iso f) (Hg : is_lt_iso g) : is_lt_iso (f · g).
  Proof.
    use make_is_lt_iso.
    - apply is_linear_and_thunkable_compose;
        apply is_lt_iso_to_is_linear_and_thunkable;
        [apply Hf | apply Hg].
    - apply has_linear_and_thunkable_inverse_compose;
        [apply Hf | apply Hg].
  Qed.

  Definition is_lt_iso_to_is_z_isomorphism {a b : M} (f : a --> b) (g : is_lt_iso f) : is_z_isomorphism f
    := g : is_submm_iso _ _.

  Definition lt_iso (a b : M) : UU
    := submm_iso' (isw_linear_and_thunkable M) a b.
  Definition make_lt_iso {a b : M}
    (f : a --> b) (H : is_lt_iso f)
    : lt_iso a b := f,, H.
  Coercion lt_iso_mor {a b : M} (f : lt_iso a b) : a --> b := pr1 f.
  Coercion lt_iso_is_linear_and_thunkable {a b : M} (f : lt_iso a b) : is_linear_and_thunkable f := pr12 f.
  Definition lt_iso_to_lt_mor {a b : M} (f : lt_iso a b)
    : linear_and_thunkable_mor a b := make_linear_and_thunkable_mor _ f.
  Definition lt_iso_is_lt_iso {a b : M} (f : lt_iso a b) : is_lt_iso f := pr2 f.
  Definition lt_iso_inverse {a b : M} (f : lt_iso a b)
    : linear_and_thunkable_mor b a := lt_iso_is_lt_iso f.
  Definition lt_iso_is_inverse {a b : M} (f : lt_iso a b)
    : is_inverse_in_precat f (lt_iso_inverse f)
    := has_linear_and_thunkable_inverse_is_inverse _ _.

  Coercion lt_iso_to_z_iso {a b : M} (f : lt_iso a b) : z_iso a b
    := make_z_iso' f (is_lt_iso_to_is_z_isomorphism _ (lt_iso_is_lt_iso f)).

  Definition make_lt_iso' {a b : M}
    (f : linear_and_thunkable_mor a b)
    (g : linear_and_thunkable_mor b a)
    (H : is_inverse_in_precat f g)
    : lt_iso a b
    := make_lt_iso _
         (make_is_lt_iso f
            (make_has_linear_and_thunkable_inverse f g H)).

  Lemma lt_iso_eq {a b : M} (f g : lt_iso a b)
    (H : lt_iso_mor f = lt_iso_mor g)
    : f = g.
  Proof. apply (subtypePath' H), isaprop_is_lt_iso. Defined.

  Lemma isaset_lt_iso (a b : M)
    : isaset (lt_iso a b).
  Proof.
    apply isaset_submm_iso'.
    intro; apply isaprop_is_lt_iso.
  Qed.

  Definition lt_iso_inv {a b : M} (f : lt_iso a b) : lt_iso b a.
  Proof.
    use make_lt_iso'.
    - exact (lt_iso_inverse f).
    - exact (lt_iso_to_lt_mor f).
    - apply is_inverse_in_precat_inv, lt_iso_is_inverse.
  Defined.

  Definition lt_iso_inv_lt_iso_inv {a b : M} (f : lt_iso a b)
    : lt_iso_inv (lt_iso_inv f) = f.
  Proof. apply idpath. Defined.

  Definition lt_iso_identity (a : M) : lt_iso a a
    := submm_iso'_identity _ a.

  Definition lt_iso_compose {a b c : M} (f : lt_iso a b) (g : lt_iso b c) : lt_iso a c.
  Proof.
    use make_lt_iso.
    - apply (linear_and_thunkable_compose (lt_iso_to_lt_mor f) (lt_iso_to_lt_mor g)).
    - apply is_lt_iso_compose;
        [ apply (lt_iso_is_lt_iso f)
        | apply (lt_iso_is_lt_iso g) ].
  Defined.

  Definition is_lt_iso_idtomor {a b : M} (p : a = b) : is_lt_iso (idtomor _ _ p).
  Proof.
    induction p.
    apply is_lt_iso_identity.
  Defined.

  Definition id_to_lt_iso {a b : M} (p : a = b) : lt_iso a b
    := id_to_submm_iso' _ _ _ p.

  (** Intermediate variant *)
  Definition is_i_iso {a b : M} (f : a --> b)
    : UU := is_submm_iso (isw_intermediate M) f.
  Identity Coercion Id_is_i_iso : is_i_iso >-> is_submm_iso.
  Lemma isaprop_is_i_iso {a b : M} (f : a --> b) : isaprop (is_i_iso f).
  Proof.
    apply invproofirrelevance; intros g g'.
    apply dirprod_paths; [apply proofirrelevance, propproperty|].
    do 2 apply carrier_eq.
    apply (inverse_unique_intermediate f).
    - exact (is_submm_iso_property _ g).
    - exact g.
    - exact g'.
  Qed.

  Definition i_iso (a b : M) : UU := submm_iso (isw_intermediate M) a b.
  Identity Coercion Id_i_iso : i_iso >-> submm_iso.

  Lemma isaset_i_iso {a b : M} : isaset (i_iso a b).
  Proof.
    apply isaset_submm_iso.
    intro; apply isaprop_is_i_iso.
  Qed.

  Definition i_iso_eq {a b : M} (f g : i_iso a b)
    (H : submm_iso_mor _ f = submm_iso_mor _ g)
    : f = g.
  Proof.
    refine (invmaponpathsincl (submm_iso_mor _) _ _ _ H).
    apply isincl_submm_iso_mor.
    intro; apply isaprop_is_i_iso.
  Qed.

  Definition isw_linear_and_thunkable_and_intermediate : wide_submagmoid M
    := wide_submagmoid_intersection
         (isw_linear_and_thunkable M)
         (isw_intermediate M).

  Definition is_lti_iso {a b : M} (f : a --> b)
    : UU
    := is_submm_iso isw_linear_and_thunkable_and_intermediate f.
  Identity Coercion Id_is_lti_iso : is_lti_iso >-> is_submm_iso.
  Lemma isaprop_is_lti_iso {a b : M} (f : a --> b) : isaprop (is_lti_iso f).
  Proof.
    apply invproofirrelevance; intros g g'.
    apply dirprod_paths; [apply proofirrelevance, propproperty|].
    do 2 apply carrier_eq.
    apply (inverse_unique_intermediate f).
    - exact (pr2 (is_submm_iso_property _ g)).
    - exact g.
    - exact g'.
  Qed.

  Definition lti_iso (a b : M) : UU
    := submm_iso isw_linear_and_thunkable_and_intermediate a b.
  Identity Coercion Id_lti_iso : lti_iso >-> submm_iso.

  Coercion lti_iso_to_lt_iso {a b : M} (f : lti_iso a b) : lt_iso a b.
  Proof.
    use make_lt_iso'.
    - apply (make_linear_and_thunkable_mor f).
      abstract exact (pr1 (submm_iso_property _ f)).
    - apply (make_linear_and_thunkable_mor (submm_inverse_mor _ f)).
      abstract exact (pr1 (submm_inverse_property _ f)).
    - exact f.
  Defined.

  Definition lti_iso_compose {a b c : M}
    (f : lti_iso a b) (g : lti_iso b c)
    : lti_iso a c.
  Proof.
    apply (submm_iso_compose _ f g).
    clear a b c f g.
    abstract (intros a b c d f g h;
              apply assoc_intermediate, (pr2 g)).
  Defined.

  Definition lti_iso_to_i_iso {a b : M} (f : lti_iso a b) : i_iso a b.
  Proof.
    use make_submm_iso_2.
    - apply (make_carrier _ (submm_iso_mor _ f)).
      exact (pr2 (submm_iso_property _ f)).
    - apply (make_carrier _ (submm_inverse_mor _ f)).
      exact (pr2 (submm_inverse_property _ f)).
    - exact f.
  Defined.

  Lemma isaset_lti_iso {a b : M} : isaset (lti_iso a b).
  Proof.
    apply isaset_submm_iso.
    intro; apply isaprop_is_lti_iso.
  Qed.

  Definition lti_iso_eq {a b : M} (f g : lti_iso a b)
    (H : submm_iso_mor _ f = submm_iso_mor _ g)
    : f = g.
  Proof.
    refine (invmaponpathsincl (submm_iso_mor _) _ _ _ H).
    apply isincl_submm_iso_mor.
    intro; apply isaprop_is_lti_iso.
  Qed.

  Corollary isincl_lti_iso_to_lt_iso (a b : M)
    : isincl (@lti_iso_to_lt_iso a b).
  Proof.
    apply isinclbetweensets.
    - apply isaset_lti_iso.
    - apply isaset_lt_iso.
    - intros f g H.
      apply lti_iso_eq.
      apply base_paths in H.
      exact H.
  Qed.

  Definition lti_iso_from_intermediate_lt_iso {a b : M}
    (f : lt_iso a b)
    (Hf : is_intermediate f)
    (Hfinv : is_intermediate (lt_iso_inverse f))
    : lti_iso a b.
  Proof.
    use make_submm_iso_2.
    - exists f.
      split.
      + apply lt_iso_is_linear_and_thunkable.
      + exact Hf.
    - exists (lt_iso_inverse f).
      split.
      + apply linear_and_thunkable_mor_is_linear_and_thunkable.
      + exact Hfinv.
    - exact (has_linear_and_thunkable_inverse_is_inverse f (lt_iso_is_lt_iso f)).
  Defined.

End isos.

Lemma opp_magmoid_is_lt_iso {M : unital_magmoid} {a b : M} (f : a --> b)
  : is_lt_iso (M:=opp_magmoid M) f -> is_lt_iso f.
Proof.
  intro H.
  use make_is_lt_iso.
  - apply opp_magmoid_is_linear_and_thunkable,
      (is_lt_iso_to_is_linear_and_thunkable _ H).
  - apply opp_magmoid_has_linear_and_thunkable_inverse,
      (is_lt_iso_to_has_linear_and_thunkable_inverse _ H).
Defined.

Lemma isweq_opp_magmoid_is_lt_iso {M : unital_magmoid} {a b : M} (f : a --> b)
  : isweq (opp_magmoid_is_lt_iso f).
Proof. opp_magmoid_involution. Defined.

Lemma opp_magmoid_lt_iso {M : unital_magmoid} (a b : M)
  : lt_iso (M:=opp_magmoid M) a b -> lt_iso a b.
Proof.
  intro f.
  use make_lt_iso.
  - exact (lt_iso_inverse f).
  - apply opp_magmoid_is_lt_iso, (lt_iso_inv f).
Defined.

Lemma isweq_opp_magmoid_lt_iso {M : unital_magmoid} (a b : M)
  : isweq (opp_magmoid_lt_iso a b).
Proof. opp_magmoid_involution. Defined.

(** ** 5. Lemmas about isomorphisms *)

Section isos_facts.
  Context {M : unital_magmoid}.

  (** Rewriting lemmas *)

  Lemma lt_iso_lt_iso_inverse_id {a b : M} (p : lt_iso a b)
    : p · lt_iso_inverse p = identity a.
  Proof. apply lt_iso_is_inverse. Qed.

  Lemma lt_iso_inverse_lt_iso_id {a b : M} (p : lt_iso a b)
    : lt_iso_inverse p · p = identity b.
  Proof. apply lt_iso_is_inverse. Qed.

  Lemma lt_iso_left {a b c : M}
    (p : lt_iso a b) (f : b --> c)
    : lt_iso_inverse p · (p · f) = f.
  Proof.
    refine (assoc_thunkable _ _ _ _ @ _ @ magmoid_id_left f).
    - apply linear_and_thunkable_mor_is_linear_and_thunkable.
    - apply cancel_postcomposition.
      apply lt_iso_inverse_lt_iso_id.
  Qed.

  Lemma lt_iso_inverse_right {a b c : M}
    (p : lt_iso a b) (f : b <-- c)
    : (f · lt_iso_inverse p) · p = f.
  Proof.
    refine (assoc'_linear _ _ _ _ @ _ @ magmoid_id_right f).
    - apply lt_iso_is_linear_and_thunkable.
    - apply cancel_precomposition.
      apply lt_iso_inverse_lt_iso_id.
  Qed.

  Lemma lt_iso_inverse_left {a b c : M}
    (p : lt_iso b a) (f : b --> c)
    : p · (lt_iso_inverse p · f) = f.
  Proof.
    change (lt_iso_inverse (lt_iso_inv p) · (lt_iso_inverse (lt_iso_inv (lt_iso_inv p)) · f) = f).
    apply lt_iso_left.
  Qed.

  Lemma lt_iso_right {a b c : M}
    (p : lt_iso b a) (f : b <-- c)
    : (f · p) · lt_iso_inverse p = f.
  Proof.
    change ((f · (lt_iso_inverse (lt_iso_inv p))) · lt_iso_inverse (lt_iso_inv (lt_iso_inv p)) = f).
    apply lt_iso_inverse_right.
  Qed.

  Lemma cancel_lt_iso_left {a b c : M}
    (p : lt_iso a b) (f g : b --> c)
    : p · f = p · g -> f = g.
  Proof.
    intro H.
    eapply cancel_precomposition in H.
    refine (!lt_iso_left _ _ @ H @ lt_iso_left _ _).
  Qed.

  Lemma cancel_lt_iso_right {a b c : M}
    (p : lt_iso b a) (f g : b <-- c)
    : p ∘ f = p ∘ g -> f = g.
  Proof.
    intro H.
    eapply cancel_postcomposition in H.
    refine (!lt_iso_right _ _ @ H @ lt_iso_right _ _).
  Qed.

  (** Any [i_iso] can be "interposed", putting it in the middle. *)

  Lemma i_iso_interpose {a b b' c : M}
    (p : i_iso b b') (f : a --> b) (g : b --> c)
    : (f · p) · (submm_inverse_mor _ p · g) = f · g.
  Proof.
    rewrite (assoc'_intermediate _ (submm_iso_property _ p)).
    rewrite (assoc_intermediate _ (submm_inverse_property _ p)).
    now rewrite (is_inverse_in_precat1 p), magmoid_id_left.
  Qed.

  Lemma is_intermediate_from_interpose {b b' : M}
    (p : b --> b')
    (pinv : has_thunkable_inverse p)
    (Hp : ∏ (a c : M) (f : a --> b) (g : b --> c),
        (f · p) · (pinv · g) = f · g)
    : is_intermediate p.
  Proof.
    intros a c f g.
    intermediate_path ((f · p) · (pinv · (p · g))). {
      apply pathsinv0, Hp.
    }
    rewrite (assoc_thunkable _ pinv).
    rewrite (is_inverse_in_precat1
               (has_thunkable_inverse_is_inverse
                  p pinv)).
    now rewrite magmoid_id_left.
  Qed.

  Lemma lt_iso_i_from_interpose {b b' : M}
    (p : lt_iso b b')
    (Hp : ∏ (a c : M) (f : a --> b) (g : b --> c),
        (f · p) · (lt_iso_inverse p · g) = f · g)
    : is_i_iso p.
  Proof.
    simple refine (_,,((_,,_),,_,,_)).
    - apply (is_intermediate_from_interpose p (lt_iso_is_lt_iso p)).
      apply Hp.
    - exact (lt_iso_inverse p).
    - apply (is_intermediate_from_interpose _ (lt_iso_is_lt_iso (lt_iso_inv p))).
      intros a c f g.
      etrans; [apply pathsinv0, Hp|]; cbn.
      now rewrite lt_iso_inverse_right, lt_iso_left.
    - apply lt_iso_lt_iso_inverse_id.
    - apply lt_iso_inverse_lt_iso_id.
  Qed.

  Lemma is_intermediate_idtomor {a b : M} (p : a = b) : is_intermediate (idtomor _ _ p).
  Proof. induction p; apply is_intermediate_identity. Qed.

  (** [lt_iso]s preserve polarities *)

  Lemma is_positive_of_lt_iso {a b : M}
    (p : lt_iso a b) (H : is_positive a) : is_positive b.
  Proof.
    intros c f.
    rewrite <- (lt_iso_left p f).
    apply is_linear_compose.
    - apply linear_and_thunkable_mor_is_linear_and_thunkable.
    - apply is_linear_of_positive, H.
  Qed.

  Lemma is_negative_of_lt_iso {a b : M}
    (p : lt_iso a b) (H : is_negative a) : is_negative b.
  Proof.
    intros c f.
    rewrite <- (lt_iso_inverse_right p f).
    apply is_thunkable_compose.
    - apply is_thunkable_of_negative, H.
    - apply lt_iso_is_linear_and_thunkable.
  Qed.

  (** Precomposition with an [lt_iso] is a weq. *)
  Lemma is_iso_of_lt_iso {a b : M} (p : lt_iso a b) : is_iso p.
  Proof.
    intro c.
    use isweq_iso.
    - intro f; exact (lt_iso_inv p · f).
    - intro f; apply lt_iso_left.
    - intro f; apply lt_iso_inverse_left.
  Defined.

  Definition lt_iso_to_iso {a b : M} (p : lt_iso a b) : iso a b
    := make_iso p (is_iso_of_lt_iso p).

  (** If anything is polarized, [lt_iso]s and [lti_iso]s merge. *)
  Lemma lt_iso_is_intermediate_from_polarized
    {a b : M}
    (p : lt_iso a b)
    (H : is_negative a ∨ is_positive a)
    : is_intermediate p.
  Proof.
    isaprop_goal Hprop; [apply isaprop_is_intermediate|].
    apply (squash_to_prop H Hprop).
    clear H; intro H; induction H as [Hnegative | Hpositive].
    - apply is_intermediate_of_negative, Hnegative.
    - apply is_intermediate_of_positive.
      apply (is_positive_of_lt_iso p Hpositive).
  Qed.

  Lemma transport_polarized_across_lt_iso {a b : M}
    (p : lt_iso a b)
    (H : is_negative a ∨ is_positive a)
    : is_negative b ∨ is_positive b.
  Proof.
    revert H; apply hinhfun; intro H.
    induction H as [Hnegative | Hpositive].
    - apply ii1, (is_negative_of_lt_iso p Hnegative).
    - apply ii2, (is_positive_of_lt_iso p Hpositive).
  Qed.

  Lemma lt_iso_is_intermediate_from_polarized'
    {a b : M}
    (p : lt_iso a b)
    (H : is_negative b ∨ is_positive b)
    : is_intermediate p.
  Proof.
    apply lt_iso_is_intermediate_from_polarized.
    apply (transport_polarized_across_lt_iso (lt_iso_inv p) H).
  Qed.

  Lemma isweq_lti_iso_to_lt_iso_from_polarized (a b : M)
    (H : is_negative a ∨ is_positive a)
    : isweq (@lti_iso_to_lt_iso M a b).
  Proof.
    apply (isweqinclandsurj _ (isincl_lti_iso_to_lt_iso _ _)).
    intro f; apply hinhpr.
    use make_hfiber.
    - apply (lti_iso_from_intermediate_lt_iso f).
      + apply lt_iso_is_intermediate_from_polarized, H.
      + apply (lt_iso_is_intermediate_from_polarized' (lt_iso_inv f)), H.
    - now apply lt_iso_eq.
  Defined.

  Definition weq_lti_iso_to_lt_iso_from_polarized (a b : M)
    (H : is_negative a ∨ is_positive a)
    : lti_iso a b ≃ lt_iso a b
    := make_weq _ (isweq_lti_iso_to_lt_iso_from_polarized _ _ H).

End isos_facts.

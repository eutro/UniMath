(********************************************************************************

 Contents:
 1. Inverses and when they are unique
 2. Linear and thunkable isomorphisms

 Author: B. Szilvasy
 January 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.

Local Open Scope cat.

(** ** 1. Inverses and when they are unique *)
Section inverses.
  Context {M : unital_magmoid} {a b : M} (f : a --> b).

  Lemma isaprop_is_inverse_in_precat_of_magmoid (g : a <-- b) : isaprop (is_inverse_in_precat f g).
  Proof. apply isapropdirprod; apply unital_magmoid_has_homsets. Qed.

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
  Coercion has_linear_inverse_to_mor (I : has_linear_inverse) : linear_mor b a := pr1 I.
  Coercion has_linear_inverse_is_inverse (I : has_linear_inverse) : is_inverse_in_precat f I := pr2 I.

  Lemma isaprop_has_linear_inverse : isaprop has_linear_inverse.
  Proof.
    apply invproofirrelevance; intros g g'.
    apply subtypePath'.
    2: apply isaprop_is_inverse_in_precat_of_magmoid.
    apply carrier_eq, inverse_unique_linear.
    - apply (has_linear_inverse_to_mor g).
    - apply g.
    - apply g'.
  Qed.

  (* Thunkable inverses are unique *)
  Lemma inverse_unique_thunkable
    (g g' : a <-- b) (H : is_thunkable g)
    (Hg : is_inverse_in_precat f g)
    (Hg' : is_inverse_in_precat f g')
    : g = g'.
  Proof.
    refine (!magmoid_id_right _ @ _ @ magmoid_id_left _).
    now rewrite <- (is_inverse_in_precat2 Hg),
      <- (is_inverse_in_precat1 Hg'), (assoc_thunkable _ H).
  Qed.

  Definition has_thunkable_inverse : UU
    := ∑ (g : thunkable_mor b a), is_inverse_in_precat f g.
  Definition make_has_thunkable_inverse
    (g : thunkable_mor b a) (H : is_inverse_in_precat f g)
    : has_thunkable_inverse := g,,H.
  Coercion has_thunkable_inverse_to_mor (I : has_thunkable_inverse) : thunkable_mor b a := pr1 I.
  Coercion has_thunkable_inverse_is_inverse (I : has_thunkable_inverse) : is_inverse_in_precat f I := pr2 I.

  Lemma isaprop_has_thunkable_inverse : isaprop has_thunkable_inverse.
  Proof.
    apply invproofirrelevance; intros g g'.
    apply subtypePath'.
    2: apply isaprop_is_inverse_in_precat_of_magmoid.
    apply carrier_eq, inverse_unique_thunkable.
    - apply (has_thunkable_inverse_to_mor g).
    - apply g.
    - apply g'.
  Qed.

  (* Thunkable and linear inverses are of course unique *)
  Definition has_linear_and_thunkable_inverse : UU
    := ∑ (g : linear_and_thunkable_mor b a), is_inverse_in_precat f g.
  Definition make_has_linear_and_thunkable_inverse
    (g : linear_and_thunkable_mor b a) (H : is_inverse_in_precat f g)
    : has_linear_and_thunkable_inverse := g,,H.
  Coercion has_linear_and_thunkable_inverse_to_mor (I : has_linear_and_thunkable_inverse)
    : linear_and_thunkable_mor b a := pr1 I.
  Coercion has_linear_and_thunkable_inverse_is_inverse (I : has_linear_and_thunkable_inverse)
    : is_inverse_in_precat f I := pr2 I.
  Coercion has_linear_and_thunkable_inverse_to_has_linear_inverse (I : has_linear_and_thunkable_inverse)
    : has_linear_inverse := make_has_linear_inverse I I.
  Coercion has_linear_and_thunkable_inverse_to_has_thunkable_inverse (I : has_linear_and_thunkable_inverse)
    : has_thunkable_inverse := make_has_thunkable_inverse I I.

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

End inverses.

(** ** 2. Linear and thunkable isomorphisms *)

Section iso.
  Context {M : unital_magmoid}.

  Lemma is_inverse_in_precat_identity_of_magmoid (a : M)
    : is_inverse_in_precat (identity a) (identity a).
  Proof.
    apply make_is_inverse_in_precat.
    1, 2: apply magmoid_id_left.
  Qed.

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
        * apply (is_inverse_in_precat1 g).
        * apply (is_inverse_in_precat1 g').
      + apply is_inverse_in_magmoid_comp_2thunkable.
        * apply (g' : thunkable_mor _ _).
        * apply (g : thunkable_mor _ _).
        * apply (is_inverse_in_precat2 g').
        * apply (is_inverse_in_precat2 g).
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
        * apply (is_inverse_in_precat1 g).
        * apply (is_inverse_in_precat1 g').
      + apply is_inverse_in_magmoid_comp_2linear.
        * apply (f' : linear_mor _ _).
        * apply (f : linear_mor _ _).
        * apply (is_inverse_in_precat2 g').
        * apply (is_inverse_in_precat2 g).
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
        * apply (f : thunkable_mor _ _).
        * apply (f' : thunkable_mor _ _).
        * apply (is_inverse_in_precat1 g).
        * apply (is_inverse_in_precat1 g').
      + apply is_inverse_in_magmoid_comp_2thunkable.
        * apply (g' : thunkable_mor _ _).
        * apply (g : thunkable_mor _ _).
        * apply (is_inverse_in_precat2 g').
        * apply (is_inverse_in_precat2 g).
  Defined.

  (** Linear-and-thunkable isomorphisms. *)

  Definition is_lt_iso {a b : M} (f : linear_and_thunkable_mor a b) : UU
    := has_linear_and_thunkable_inverse f.
  Identity Coercion Id_is_lt_iso : is_lt_iso >-> has_linear_and_thunkable_inverse.

  Definition lt_iso (a b : M) : UU :=
    ∑ (f : linear_and_thunkable_mor a b), is_lt_iso f.
  Definition make_lt_iso {a b : M}
    (f : linear_and_thunkable_mor a b)
    (g : has_linear_and_thunkable_inverse f)
    : lt_iso a b := f,,g.
  Coercion lt_iso_mor {a b : M} (f : lt_iso a b) : linear_and_thunkable_mor a b := pr1 f.
  Definition lt_iso_is_lt_iso {a b : M} (f : lt_iso a b) : is_lt_iso f := pr2 f.
  Definition lt_iso_inverse {a b : M} (f : lt_iso a b)
    : linear_and_thunkable_mor b a := lt_iso_is_lt_iso f.
  Definition lt_iso_is_inverse {a b : M} (f : lt_iso a b)
    : is_inverse_in_precat f (lt_iso_inverse f) := lt_iso_is_lt_iso f.

  Definition make_lt_iso' {a b : M}
    (f : linear_and_thunkable_mor a b)
    (g : linear_and_thunkable_mor b a)
    (H : is_inverse_in_precat f g)
    : lt_iso a b
    := make_lt_iso _ (make_has_linear_and_thunkable_inverse f g H).

  Definition inv_lt_iso {a b : M} (f : lt_iso a b) : lt_iso b a.
  Proof.
    use make_lt_iso'.
    - exact (lt_iso_inverse f).
    - exact f.
    - apply is_inverse_in_precat_inv, lt_iso_is_inverse.
  Defined.

  Definition lt_iso_identity (a : M) : lt_iso a a.
  Proof.
    use make_lt_iso'.
    1, 2: apply linear_and_thunkable_identity.
    apply is_inverse_in_precat_identity_of_magmoid.
  Defined.

  Definition lt_iso_compose {a b c : M} (f : lt_iso a b) (g : lt_iso b c) : lt_iso a c.
  Proof.
    use make_lt_iso.
    - apply (linear_and_thunkable_compose f g).
    - apply has_linear_and_thunkable_inverse_compose.
      + apply (lt_iso_is_lt_iso f).
      + apply (lt_iso_is_lt_iso g).
  Defined.

  Definition id_to_lt_iso {a b : M} (p : a = b) : lt_iso a b.
  Proof.
    induction p.
    exact (lt_iso_identity a).
  Defined.

  Lemma id_to_lt_iso_idtomor {a b : M} (p : a = b) :
    (id_to_lt_iso p : M⟦a, b⟧) = idtomor _ _ p.
  Proof. now induction p. Defined.

  Definition unital_magmoid_is_univalent
    := ∏ (a b : M), isweq (λ (p : a = b), id_to_lt_iso p).

End iso.

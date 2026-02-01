(********************************************************************************

 Isomorphisms in Unital Magmoids

 Contents:
 1. Definitions of inverses and when they are unique
 2. Composition of inverses when they exist
 3. Linear-and-thunkable isomorphisms [lt_iso]
 4. Lemmas about linear-and-thunkable isomorphisms

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

  (* Thunkable-and-linear inverses are of course unique *)
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

(** ** 2. Composition of inverses when they exist *)

Section composition.
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
End composition.

(** ** 3. Linear-and-thunkable isomorphisms [lt_iso] *)

Section isos.
  Context {M : unital_magmoid}.

  Definition is_lt_iso {a b : M} (f : a --> b) : UU
    := is_linear_and_thunkable f × has_linear_and_thunkable_inverse f.

  Definition make_is_lt_iso {a b : M} {f : a --> b}
    (H1 : is_linear_and_thunkable f)
    (g : has_linear_and_thunkable_inverse f)
    := H1,,g.

  Definition make_is_lt_iso' {a b : M} {f : a --> b}
    (Hf : is_linear_and_thunkable f)
    (g : b --> a)
    (Hg : is_linear_and_thunkable g)
    (Hfg : is_inverse_in_precat f g)
    := make_is_lt_iso Hf
         (make_has_linear_and_thunkable_inverse _
            (make_linear_and_thunkable_mor g Hg)
            Hfg).

  Definition is_lt_iso_to_is_linear_and_thunkable {a b : M} (f : a --> b) (H : is_lt_iso f)
    : is_linear_and_thunkable f := pr1 H.
  Coercion is_lt_iso_to_has_linear_and_thunkable_inverse {a b : M} (f : a --> b) (H : is_lt_iso f)
    : has_linear_and_thunkable_inverse f := pr2 H.
  Definition isaprop_is_lt_iso {a b : M} (f : linear_and_thunkable_mor a b)
    : isaprop (is_lt_iso f).
  Proof.
    apply isofhleveldirprod.
    - apply isaprop_is_linear_and_thunkable.
    - apply isaprop_has_linear_and_thunkable_inverse.
  Qed.

  Lemma is_lt_iso_identity (a : M) : is_lt_iso (identity a).
  Proof.
    use make_is_lt_iso'.
    2: apply (identity a).
    1, 2: apply is_linear_and_thunkable_identity.
    apply is_inverse_in_precat_identity_of_magmoid.
  Qed.

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

  Definition is_lt_iso_to_is_z_isomorphism {a b : M} (f : a --> b) (g : is_lt_iso f) : is_z_isomorphism f.
  Proof.
    exists g; cbn.
    apply has_linear_and_thunkable_inverse_is_inverse.
  Defined.

  Definition lt_iso (a b : M) : UU :=
    ∑ f : a --> b, is_lt_iso f.
  Definition make_lt_iso {a b : M}
    (f : a --> b) (H : is_lt_iso f)
    : lt_iso a b := f,,H.
  Coercion lt_iso_mor {a b : M} (f : lt_iso a b) : a --> b := pr1 f.
  Coercion lt_iso_is_linear_and_thunkable {a b : M} (f : lt_iso a b) : is_linear_and_thunkable f := pr12 f.
  Definition lt_iso_to_lt_mor {a b : M} (f : lt_iso a b)
    : linear_and_thunkable_mor a b := make_linear_and_thunkable_mor _ f.
  Definition lt_iso_is_lt_iso {a b : M} (f : lt_iso a b) : is_lt_iso f := pr2 f.
  Definition lt_iso_inverse {a b : M} (f : lt_iso a b)
    : linear_and_thunkable_mor b a := lt_iso_is_lt_iso f.
  Definition lt_iso_is_inverse {a b : M} (f : lt_iso a b)
    : is_inverse_in_precat f (lt_iso_inverse f) := lt_iso_is_lt_iso f.

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

  Definition lt_iso_identity (a : M) : lt_iso a a.
  Proof.
    use make_lt_iso.
    - apply identity.
    - apply is_lt_iso_identity.
  Defined.

  Definition lt_iso_compose {a b c : M} (f : lt_iso a b) (g : lt_iso b c) : lt_iso a c.
  Proof.
    use make_lt_iso.
    - apply (linear_and_thunkable_compose (lt_iso_to_lt_mor f) (lt_iso_to_lt_mor g)).
    - apply is_lt_iso_compose;
        [ apply (lt_iso_is_lt_iso f)
        | apply (lt_iso_is_lt_iso g) ].
  Defined.

End isos.

(** ** 4. Lemmas about linear-and-thunkable isomorphisms *)

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
    change ((lt_iso_inv (lt_iso_inv p)) · (lt_iso_inverse (lt_iso_inv (lt_iso_inv p)) · f) = f).
    apply lt_iso_left.
  Qed.

  Lemma lt_iso_right {a b c : M}
    (p : lt_iso b a) (f : b <-- c)
    : (f · p) · lt_iso_inverse p = f.
  Proof.
    change ((f · (lt_iso_inv (lt_iso_inv p))) · lt_iso_inverse (lt_iso_inv (lt_iso_inv p)) = f).
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

  (** Any [z_iso] can be "interposed", putting it in the middle, so long as it is an
      intermediate morphism. *)

  Lemma intermediate_z_iso_interpose {a b b' c : M}
    (p : z_iso b b') (f : a --> b) (g : b --> c)
    (Hp : is_intermediate p) (Hpinv : is_intermediate (inv_from_z_iso p))
    : (f · p) · (inv_from_z_iso p · g) = f · g.
  Proof.
    rewrite (assoc'_intermediate _ Hp), (assoc_intermediate _ Hpinv).
    now rewrite (is_inverse_in_precat1 p), magmoid_id_left.
  Qed.

  Lemma intermediate_z_iso_inv_interpose {a b b' c : M}
    (p : z_iso b' b) (f : a --> b) (g : b --> c)
    (Hp : is_intermediate p) (Hpinv : is_intermediate (inv_from_z_iso p))
    : (f · inv_from_z_iso p) · (p · g) = f · g.
  Proof.
    apply (intermediate_z_iso_interpose (z_iso_inv p)); assumption.
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

End isos_facts.

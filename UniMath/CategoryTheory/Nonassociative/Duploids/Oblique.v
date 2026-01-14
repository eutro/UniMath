(********************************************************************************

 The Duploid arising from an Adjunction

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Definition of oblique duploid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope duploid.

(** ** 1. Definition of oblique duploid *)

Context {C₁ C₂ : category} (θ : adjunction C₂ C₁).
Let F : functor C₂ C₁ := left_functor θ.
Let G : functor C₁ C₂ := right_functor θ.
Let H : are_adjoints F G := θ.
Let η : nat_trans (functor_identity C₂) (F ∙ G) := unit_from_are_adjoints H.
Let ε : nat_trans (G ∙ F) (functor_identity C₁) := counit_from_are_adjoints H.

Definition oblique_ob := C₁ ⨿ C₂.

Definition oblique_negativise (a : oblique_ob) : C₁.
Proof. induction a as [n | p]. exact n. exact (F p). Defined.
Definition oblique_positivise (a : oblique_ob) : C₂.
Proof. induction a as [n | p]. exact (G n). exact p. Defined.

Notation "a '⁻'" := (oblique_negativise a) : duploid.
Notation "a '⁺'" := (oblique_positivise a) : duploid.

Definition oblique_mor (a b : oblique_ob) := C₁⟦F (a⁺), b⁻⟧.

Lemma isaset_oblique_mor (a b : oblique_ob) : isaset (oblique_mor a b).
Proof. apply C₁. Qed.

Definition oblique_identity (a : oblique_ob) : oblique_mor a a.
Proof.
  induction a.
  + apply (φ_adj_inv H), identity.
  + apply identity.
Defined.

Definition oblique_compose {a b c : oblique_ob}
  (f : oblique_mor a b) (g : oblique_mor b c)
  : oblique_mor a c.
Proof.
  induction b.
  + exact (φ_adj_inv H (φ_adj H f · φ_adj H g)).
  + exact (f · g).
Defined.

Lemma oblique_left_id {a b : oblique_ob} (f : oblique_mor a b) :
  oblique_compose (oblique_identity a) f = f.
Proof.
  induction a; simpl.
  + rewrite φ_adj_after_φ_adj_inv, id_left.
    apply φ_adj_inv_after_φ_adj.
  + apply id_left.
Qed.

Lemma oblique_right_id {a b : oblique_ob} (f : oblique_mor a b) :
  oblique_compose f (oblique_identity b) = f.
Proof.
  induction b; simpl.
  + rewrite φ_adj_after_φ_adj_inv, id_right.
    apply φ_adj_inv_after_φ_adj.
  + apply id_right.
Qed.

Definition oblique_quasiduploid : quasiduploid.
Proof.
  use make_quasiduploid.
  - use make_precategory_data.
    + exact (make_precategory_ob_mor oblique_ob oblique_mor).
    + exact oblique_identity.
    + intros a b c f g. exact (oblique_compose f g).
  - intros a b. apply isaset_oblique_mor.
  - use make_is_quasiduploid.
    + intros a b f. apply oblique_left_id.
    + intros a b f. apply oblique_right_id.
Defined.

Definition oblique_negative (a : C₁) : oblique_quasiduploid := inl a.
Definition oblique_positive (a : C₂) : oblique_quasiduploid := inr a.

Lemma is_negative_of_adj_left (a : C₁) : is_negative (oblique_negative a).
Proof.
  intros b f c d g h.
  induction c as [m | q]; unfold compose; simpl.
  + do 2 rewrite φ_adj_after_φ_adj_inv.
    now rewrite assoc.
  + rewrite φ_adj_natural_postcomp, assoc.
    now rewrite φ_adj_inv_natural_postcomp.
Qed.

Lemma is_positive_of_adj_right (a : C₂) : is_positive (oblique_positive a).
Proof.
  intros b f c d g h.
  induction c as [m | q]; unfold compose; simpl.
  + rewrite φ_adj_natural_postcomp, assoc.
    now rewrite φ_adj_inv_natural_postcomp.
  + apply assoc'.
Qed.

Lemma is_polarized_oblique_quasiduploid : is_polarized oblique_quasiduploid.
Proof.
  intro a.
  apply hinhpr.
  induction a as [n | p].
  - right; apply is_negative_of_adj_left.
  - left; apply is_positive_of_adj_right.
Qed.

Definition oblique_preduploid : preduploid :=
  make_preduploid is_polarized_oblique_quasiduploid.

Definition oblique_upshift (a : oblique_preduploid) : oblique_preduploid.
Proof.
  induction a as [n | p]; apply oblique_negative.
  - exact n.
  - exact (F p).
Defined.

Definition oblique_force (a : oblique_preduploid) : oblique_upshift a --> a.
Proof.
  induction a as [n | p].
  + apply identity.
  + apply (φ_adj_inv H), identity.
Defined.

Definition oblique_delay (a : oblique_preduploid) : a --> oblique_upshift a.
Proof.
  induction a as [n | p].
  + apply identity.
  + apply (identity (F p)).
Defined.

Definition oblique_downshift (a : oblique_preduploid) : oblique_preduploid.
Proof.
  induction a as [n | p]; apply oblique_positive.
  + exact (G n).
  + exact p.
Defined.

Definition oblique_wrap (a : oblique_preduploid) : a --> oblique_downshift a.
Proof.
  induction a as [n | p].
  + apply (identity (F (G n))).
  + apply identity.
Defined.

Definition oblique_unwrap (a : oblique_preduploid) : oblique_downshift a --> a.
Proof.
  induction a as [n | p].
  + apply (φ_adj_inv H), identity.
  + apply identity.
Defined.

Lemma is_negative_oblique_upshift (a : oblique_preduploid)
  : is_negative (oblique_upshift a).
Proof. induction a; apply is_negative_of_adj_left. Qed.

Lemma is_positive_oblique_downshift (a : oblique_preduploid)
  : is_positive (oblique_downshift a).
Proof. induction a; apply is_positive_of_adj_right. Qed.

Lemma is_linear_oblique_force (a : oblique_preduploid)
  : is_linear (oblique_force a).
Proof.
  induction a as [n | p].
  1: apply is_linear_identity.
  intros b c f g.
  induction b as [m | q].
  1: now rewrite (assoc'_negative _ (is_negative_of_adj_left _)).
  unfold compose; simpl.
  rewrite φ_adj_after_φ_adj_inv.
  now do 2 rewrite id_right, φ_adj_inv_after_φ_adj.
Qed.

Definition is_thunkable_oblique_wrap (a : oblique_preduploid)
  : is_thunkable (oblique_wrap a).
Proof.
  induction a as [n | p].
  2: apply is_thunkable_identity.
  intros b c f g.
  induction b as [m | q].
  2: now rewrite (assoc'_positive _ (is_positive_of_adj_right _)).
  unfold compose; simpl.
  now do 2 rewrite id_left.
Qed.

Lemma is_linear_oblique_delay (a : oblique_preduploid)
  : is_linear (oblique_delay a).
Proof.
  induction a as [n | p].
  2: apply is_linear_of_positive, is_positive_of_adj_right.
  intros b c f g.
  induction b as [m | q].
  1: apply assoc'_negative, is_negative_of_adj_left.
  cbn.
  rewrite φ_adj_natural_postcomp.
  rewrite φ_adj_after_φ_adj_inv.
  do 2 rewrite id_right.
  rewrite φ_adj_inv_natural_postcomp.
  now do 2 rewrite φ_adj_inv_after_φ_adj.
Qed.

Lemma is_thunkable_oblique_unwrap (a : oblique_preduploid)
  : is_thunkable (oblique_unwrap a).
Proof.
  induction a as [n | p].
  1: apply is_thunkable_of_negative, is_negative_of_adj_left.
  intros b c f g.
  induction b as [m | q].
  2: apply assoc_positive, is_positive_of_adj_right.
  cbn.
  now do 2 rewrite id_left.
Qed.

Definition is_inverse_in_precat_oblique_force_delay (a : oblique_preduploid)
  : is_inverse_in_precat (oblique_force a) (oblique_delay a).
Proof.
  induction a as [n | p]; simpl; split; unfold identity, compose; simpl;
    fold (identity (C:=C₂)); fold (identity (C:=C₁)).
  - now rewrite φ_adj_after_φ_adj_inv, id_left.
  - now rewrite φ_adj_after_φ_adj_inv, id_left.
  - now rewrite id_right.
  - now rewrite φ_adj_after_φ_adj_inv, id_right, φ_adj_inv_after_φ_adj.
Qed.

Definition is_inverse_in_precat_oblique_wrap_unwrap (a : oblique_preduploid)
  : is_inverse_in_precat (oblique_wrap a) (oblique_unwrap a).
Proof.
  induction a as [n | p]; simpl; split; unfold identity, compose; simpl;
    fold (identity (C:=C₂)); fold (identity (C:=C₁)).
  - now rewrite id_left.
  - now rewrite φ_adj_after_φ_adj_inv, id_left, φ_adj_inv_after_φ_adj.
  - apply id_left.
  - apply id_left.
Qed.

Definition oblique_duploid_data : duploid_data oblique_preduploid.
Proof.
  apply make_duploid_data.
  - exact (make_duploid_force_data oblique_upshift oblique_force).
  - exact (make_duploid_wrap_data oblique_downshift oblique_wrap).
Defined.

Definition oblique_duploid_axioms : duploid_axioms oblique_duploid_data.
Proof.
  apply make_duploid_axioms.
  - use make_duploid_force_axioms.
    + apply is_negative_oblique_upshift.
    + apply is_linear_oblique_force.
    + apply oblique_delay.
    + apply is_inverse_in_precat_oblique_force_delay.
  - use make_duploid_wrap_axioms.
    + apply is_positive_oblique_downshift.
    + apply is_thunkable_oblique_wrap.
    + apply oblique_unwrap.
    + apply is_inverse_in_precat_oblique_wrap_unwrap.
Defined.

(* The oblique duploid is the duploid arising from an adjunction,
   where objects are objects in either category, and morphisms
   are the morphisms C₁⟦F a⁺, b⁻⟧ (equivalently C₂⟦a⁻, G b⁺⟧). *)
Definition oblique_duploid : duploid
  := make_duploid oblique_duploid_data oblique_duploid_axioms.

Lemma is_linear_of_oblique_counit_precompose {n : C₁} {a : oblique_duploid}
  (f : oblique_negative n --> a)
  : #(G ∙ F) (ε n) · f = ε ((G ∙ F) n) · f ->
    is_linear f.
Proof.
  intro Hf.
  apply (is_linear_of_force_unwrap (C:=oblique_duploid)).
  unfold force, unwrap, compose; simpl.
  rewrite φ_adj_natural_postcomp, φ_adj_inv_natural_precomp.
  do 2 rewrite φ_adj_after_φ_adj_inv, id_left, φ_adj_inv_after_φ_adj.
  unfold φ_adj_inv; fold ε.
  do 2 rewrite functor_id, id_left.
  exact Hf.
Qed.

Lemma is_thunkable_of_oblique_unit_postcompose {a : oblique_duploid} {p : C₂}
  (f : a --> oblique_positive p)
  : φ_adj H f · #(F ∙ G) (η p) = φ_adj H f · η ((F ∙ G) p) ->
    is_thunkable f.
Proof.
  intro Hf.
  apply (is_thunkable_of_delay_wrap (C:=oblique_duploid)).
  eenough (H' : φ_adj_inv H (φ_adj H _) = φ_adj_inv H (φ_adj H _)). {
    do 2 rewrite φ_adj_inv_after_φ_adj in H'.
    exact H'.
  }
  apply maponpaths.
  unfold delay, wrap, compose; simpl.
  do 2 rewrite φ_adj_natural_postcomp, φ_adj_inv_natural_precomp.
  rewrite φ_adj_inv_after_φ_adj, functor_id.
  do 2 rewrite id_right.
  rewrite functor_comp, functor_id, φ_adj_natural_precomp.
  do 2 rewrite φ_adj_identity. fold η.
  exact Hf.
Qed.

Corollary is_precategory_of_oblique_idempotent_adjunction
  (H1 : post_whisker ε (G ∙ F) = pre_whisker (G ∙ F) ε)
  : is_precategory oblique_duploid.
Proof.
  use is_precategory_of_quasiduploid.
  intros a b c d f g h.
  apply assoc_linear.
  induction c as [n | p].
  2: apply is_linear_of_positive, is_positive_of_adj_right.
  apply is_linear_of_oblique_counit_precompose.
  intermediate_path (post_whisker ε (G ∙ F) n · h).
    apply idpath.
  now rewrite H1.
Qed.

(********************************************************************************

 Assemble a family of left-universal arrows into a pseudofunctor.

 This file largely follows the proofs of Fiore 2006, "Pseudo Limits, Biadjoints,
 and Pseudo Algebras: Categorical Foundations of Conformal Field
 Theory". However, they are generalized to bicategories.

 Author: B. Szilvasy
 July 2026

 Contents:
 TODO

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.

Local Open Scope cat.

Section psfunctor_from_LUA.
  Context {A B : bicat} (R : psfunctor B A) (LUR : left_universal_arrow R).

  Let L : A -> B := pr1 LUR.
  Let η : ∏ (x : A), x --> R (L x) := pr12 LUR.
  Let ϕ (x : A) (y : B) : hom (L x) y ⟶ hom x (R y) := left_universal_arrow_functor R x y η.

  Let Hη : ∏ (x : A) (y : B), adj_equivalence_of_cats (ϕ x y) := pr22 LUR.
  Let ψ (x : A) (y : B) : hom x (R y) ⟶ hom (L x) y := adj_equivalence_inv (Hη x y).
  Let Hηadj (x : A) (y : B) : are_adjoints (ϕ x y) (ψ x y) := pr2 (Hη x y : is_left_adjoint _).
  Let μ (x : A) (y : B) : nat_z_iso (ψ x y ∙ ϕ x y) (functor_identity (hom x (R y)))
      := counit_nat_z_iso_from_adj_equivalence_of_cats (Hη x y).
  Let δ (x : A) (y : B) : nat_z_iso (functor_identity (hom (L x) y)) (ϕ x y ∙ ψ x y)
      := unit_nat_z_iso_from_adj_equivalence_of_cats (Hη x y).

  Local Definition μ_f {x : A} {y : B}
    (g : L x --> y) (f : x --> R y)
    (ν : ϕ x y g ==> f)
    : g ==> ψ x y f
    := δ x y g • # (ψ x y) ν.
  (* ≡ φ_adj (Hηadj _ _) ν *)
  Local Definition μ_f' {x : A} {y : B}
    (g : L x --> y) (f : x --> R y)
    (ν : g ==> ψ x y f)
    : ϕ x y g ==> f
    := (η x ◃ ##R ν) • μ x y f.
  (* ≡ φ_adj_inv (Hηadj _ _) ν *)

  Local Lemma isweq_μ_f' {x : A} {y : B}
    (g : L x --> y) (f : x --> R y)
    : isweq (μ_f' g f).
  Proof.
    use isweq_iso.
    - exact (μ_f g f).
    - intros ν'; exact (φ_adj_after_φ_adj_inv (Hηadj _ _) ν').
    - intros ν'; exact (φ_adj_inv_after_φ_adj (Hηadj _ _) ν').
  Defined.
  Local Lemma isweq_μ_f {x : A} {y : B}
    (g : L x --> y) (f : x --> R y)
    : isweq (μ_f g f).
  Proof.
    exact (isweqinvmap (make_weq _ (isweq_μ_f' g f))).
  Defined.

  Local Lemma μ_f_inv {x : A} {y : B}
    (g : L x --> y) (f : x --> R y)
    (ν : ϕ x y g ==> f)
    (Hν : is_invertible_2cell ν)
    : is_invertible_2cell (μ_f g f ν).
  Proof.
    unfold μ_f.
    is_iso.
    + exact (pr2_nat_z_iso (δ x y) g).
    + exact (functor_on_is_z_isomorphism (ψ x y) Hν).
  Defined.

  Local Lemma psfunctor_is_invertible_2cell
    {C D : bicat}
    (F : psfunctor C D)
    {a b : C}
    {f g : C⟦a,b⟧}
    (α : f ==> g)
    (Hα : is_invertible_2cell α)
    : is_invertible_2cell (##F α).
  Proof.
    exact (psfunctor_is_iso F (α,, Hα)).
  Defined.

  Local Lemma μ_f'_inv {x : A} {y : B}
    (g : L x --> y) (f : x --> R y)
    (ν : g ==> ψ x y f)
    (Hν : is_invertible_2cell ν)
    : is_invertible_2cell (μ_f' g f ν).
  Proof.
    unfold μ_f'.
    is_iso.
    + exact (psfunctor_is_invertible_2cell R ν Hν).
    + exact (pr2_nat_z_iso (μ x y) f).
  Defined.

  Definition psfunctor_from_left_universal_arrow_on_1cells
    {x y : A} (f : x --> y)
    : L x --> L y
    := ψ x (L y) (f · η y).
  Local Notation "#L" := psfunctor_from_left_universal_arrow_on_1cells.

  Definition psfunctor_from_left_universal_arrow_on_2cells
    {x y : A} {f g : x --> y} (α : f ==> g)
    : #L f ==> #L g
    := # (ψ x (L y)) (α ▹ η y).
  Local Notation "##L" := psfunctor_from_left_universal_arrow_on_2cells.

  Local Lemma is_invertible_2cell_is_z_isomorphism_in_hom
    {C : bicat} {x y : C} {f g : x --> y}
    (α : f ==> g)
    : is_z_isomorphism (C:=hom x y) α ≃ is_invertible_2cell α.
  Proof. apply idweq. Defined.

  Definition psfunctor_from_left_universal_arrow_identitor (x : A)
    : id₁ (L x) ==> #L (id₁ x)
    := μ_f (id₁ (L x)) (id₁ x · η x)
         ((η x ◃ (psfunctor_id R (L x))^-1)
            • runitor (η x) • linvunitor (η x)).
  Local Notation identitor := psfunctor_from_left_universal_arrow_identitor.

  Definition psfunctor_from_left_universal_arrow_identitor_inv (x : A)
    : is_invertible_2cell (identitor x).
  Proof. apply μ_f_inv; is_iso. Defined.
  Local Notation identitor_inv := psfunctor_from_left_universal_arrow_identitor_inv.

  Definition psfunctor_from_left_universal_arrow_compositor
    {a b c : A} (f : a --> b) (g : b --> c)
    : #L f ·  #L g ==> #L (f · g)
    := μ_f _ _
         (((η a ◃ (psfunctor_comp R _ _)^-1)
             • lassociator (η a) (#R _) (#R _)
             • (μ _ _ (f · η b) ▹ #R _)
             • rassociator f (η b) (#R _)
             • (f ◃ μ _ _ (g · η c))
             • lassociator f g (η c))).
  Local Notation compositor := psfunctor_from_left_universal_arrow_compositor.
  Definition psfunctor_from_left_universal_arrow_compositor_inv
    {a b c : A} (f : a --> b) (g : b --> c)
    : is_invertible_2cell (compositor f g).
  Proof.
    apply μ_f_inv; is_iso.
    + exact (pr2_nat_z_iso (μ _ _) _).
    + exact (pr2_nat_z_iso (μ _ _) _).
  Defined.
  Local Notation compositor_inv := psfunctor_from_left_universal_arrow_compositor_inv.

  Definition psfunctor_from_left_universal_arrow_data : psfunctor_data A B.
  Proof.
    use make_psfunctor_data.
    - exact L.
    - exact @psfunctor_from_left_universal_arrow_on_1cells.
    - exact @psfunctor_from_left_universal_arrow_on_2cells.
    - intro x; exact (identitor x).
    - intros x y z f g; exact (compositor f g).
  Defined.

  Definition psfunctor_id2_from_left_universal_arrow
    : psfunctor_id2_law psfunctor_from_left_universal_arrow_data.
  Proof.
    intros a b f; cbn.
    etrans; [exact (maponpaths # (ψ _ _) (id2_rwhisker _ (η _)))|].
    exact (functor_id (ψ _ _) _).
  Qed.

  Definition psfunctor_vcomp2_from_left_universal_arrow
    : psfunctor_vcomp2_law psfunctor_from_left_universal_arrow_data.
  Proof.
    intros a b f g h γ φ; cbn.
    etrans; [exact (maponpaths # (ψ _ _) (!rwhisker_vcomp (η _) _ _))|].
    exact (functor_comp (ψ _ _) _ _).
  Qed.

  Definition psfunctor_lunitor_from_left_universal_arrow
    : psfunctor_lunitor_law psfunctor_from_left_universal_arrow_data.
  Proof.
    intros a b f; cbn.
    use vcomp_move_L_Mp. {
      is_iso.
      refine (functor_on_is_z_isomorphism (ψ _ _)
                (_ : is_invertible_2cell (lunitor f ▹ η b))).
      is_iso.
    }
    change (lunitor (#L f) • ##L (linvunitor f) = (identitor a ▹ #L f) • compositor (id₁ a) f).
    use vcomp_move_L_pM. { is_iso; apply identitor_inv. }
    cbn -[identitor_inv].
    apply (Injectivity (μ_f' _ _)).
    { apply isweqonpathsincl, isinclweq, isweq_μ_f'. }
    etrans; [|apply pathsinv0, (φ_adj_inv_after_φ_adj (Hηadj _ _))].
    fold (#L f) (#L (id₁ a)).
    unfold μ_f'.
    etrans.
    2: {
      apply pathsinv0.
      assert (Heq : lunitor _ • rinvunitor _ • (η a ◃ psfunctor_id R (L a))
                    = (nat_z_iso_inv (μ a (L a)) (id₁ a · η a))
                        • ((η a ◃ ## R (identitor_inv a) ^-1))). {
        intermediate_path (μ_f'_inv _ _ _ (identitor_inv a))^-1.
        - etrans; [|apply id2_left].
          use vcomp_move_L_Mp. { is_iso. }
          use vcomp_move_R_pM. { is_iso; apply property_from_invertible_2cell. }
          etrans; [|apply pathsinv0, id2_right].
          etrans; [|apply vassocl].
          exact (φ_adj_inv_after_φ_adj (Hηadj _ _) _).
        - reflexivity.
      }
      etrans. {
        refine (maponpaths (λ α, (((α • _) • _) • _) • _) _).
        etrans. {
          refine (maponpaths (λ α, (_ ◃ α) • _) _).
          instantiate (1 := ##R ((identitor_inv a)^-1 ▹ #L f) •
                              (psfunctor_comp R _ _)^-1 •
                              (##R (identitor a) ▹ #R(#L f))).
          use vcomp_move_L_pM.
          { is_iso; apply psfunctor_is_invertible_2cell; is_iso. }
          use vcomp_move_R_Mp. { is_iso. }
          apply psfunctor_rwhisker.
        }
        etrans. {
          rewrite <- !lwhisker_vcomp.
          refine (maponpaths (λ α, _ • (_ ◃ α) • _ • _) _).
          instantiate (1 := ##R (lunitor (#L f)) •
                              linvunitor (#R(#L f)) •
                              (psfunctor_id R (L a) ▹ #R(#L f))).
          use vcomp_move_L_pM.
          { is_iso; apply psfunctor_is_invertible_2cell; is_iso. }
          use vcomp_move_R_Mp. { is_iso. }
          use vcomp_move_R_Mp. { apply psfunctor_is_invertible_2cell; is_iso. }
          exact (psfunctor_lunitor R (#L f)).
        }
        rewrite <- !lwhisker_vcomp, !vassocl.
        etrans. {
          refine (maponpaths (λ α, _ • (_ • (_ • α))) _).
          now rewrite rwhisker_lwhisker, vassocr, rwhisker_lwhisker.
        }
        etrans. {
          rewrite !vassocl.
          refine (maponpaths (λ α, _ • (_ • α)) _).
          etrans; [apply vassocr|].
          refine (maponpaths (λ α, α • _) _).
          instantiate (1 := rinvunitor (η a) ▹ #R(#L f)).
          use vcomp_move_R_pM. { is_iso. }
          use vcomp_move_L_Mp. { is_iso. }
          apply runitor_rwhisker.
        }
        etrans. {
          refine (maponpaths (λ α, _ • (_ • α)) _).
          rewrite !rwhisker_vcomp.
          apply maponpaths.
          instantiate (1 := linvunitor (η a) • nat_z_iso_inv (μ a (L a)) (id₁ a · η a)).
          use vcomp_move_L_pM. { is_iso. }
          rewrite !vassocr.
          use vcomp_move_R_Mp. { is_iso; apply psfunctor_is_invertible_2cell, identitor_inv. }
          exact Heq.
        }
        reflexivity.
      }
      etrans. {
        refine (maponpaths (λ α, ((α • _) • _) • _) _).
        rewrite <- rwhisker_vcomp, !vassocl.
        refine (maponpaths (λ α, _ • (_ • (_ • α))) _).
        rewrite rwhisker_vcomp.
        etrans. {
          apply maponpaths.
          exact (pr22 (pr2_nat_z_iso (μ a (L a)) _)).
        }
        apply id2_rwhisker.
      }
      rewrite id2_right.
      reflexivity.
    }
    rewrite !psfunctor_vcomp, <- !lwhisker_vcomp, !vassocl.
    refine (maponpaths (λ α, _ • (_ • α)) _).
    refine (nat_trans_ax (μ a (L b)) _ _ _ @ _).
    apply pathsinv0.
    rewrite !vassocr.
    etrans. {
      refine (maponpaths (λ α, (α • _) • _) _).
      instantiate (1 := linvunitor _).
      use vcomp_move_R_Mp. { is_iso. }
      use vcomp_move_L_pM. { is_iso. }
      use vcomp_move_R_Mp. { is_iso. }
      apply lunitor_assoc.
    }
    etrans. {
      refine (maponpaths (λ α, α • _) _).
      instantiate (1 := μ a (L b) (f · η b) • linvunitor (f · η b)).
      use vcomp_move_L_Mp. { is_iso. }
      rewrite vassocl.
      use vcomp_move_R_pM. { is_iso. }
      apply vcomp_lunitor.
    }
    rewrite linvunitor_assoc, !vassocl.
    etrans. {
      do 2 apply maponpaths.
      apply rassociator_lassociator.
    }
    rewrite id2_right.
    reflexivity.
  Qed.

  Definition psfunctor_runitor_from_left_universal_arrow
    : psfunctor_runitor_law psfunctor_from_left_universal_arrow_data.
  Proof.
    intros a b f; cbn.
    use vcomp_move_L_Mp. {
      is_iso.
      refine (functor_on_is_z_isomorphism (ψ _ _)
                (_ : is_invertible_2cell (runitor f ▹ η b))).
      is_iso.
    }
    change (runitor (#L f) • ##L (rinvunitor f) = (#L f ◃ identitor b) • compositor f (id₁ b)).
    use vcomp_move_L_pM. { is_iso; apply identitor_inv. }
    cbn -[identitor_inv].
    apply (Injectivity (μ_f' _ _)).
    { apply isweqonpathsincl, isinclweq, isweq_μ_f'. }
    etrans; [|apply pathsinv0, (φ_adj_inv_after_φ_adj (Hηadj _ _))].
    fold (#L f) (#L (id₁ b)).
    unfold μ_f'.
    etrans.
    2: {
      apply pathsinv0.
      etrans. {
        refine (maponpaths (λ α, (((α • _) • _) • _) • _) _).
        etrans. {
          refine (maponpaths (λ α, (_ ◃ α) • _) _).
          instantiate (1 := ##R (#L f ◃ (identitor_inv b)^-1) •
                              (psfunctor_comp R _ _)^-1 •
                              (#R(#L f) ◃ ##R (identitor b))).
          use vcomp_move_L_pM.
          { is_iso; apply psfunctor_is_invertible_2cell; is_iso. }
          use vcomp_move_R_Mp. { is_iso. }
          apply psfunctor_lwhisker.
        }
        etrans. {
          rewrite <- !lwhisker_vcomp.
          refine (maponpaths (λ α, _ • (_ ◃ α) • _ • _) _).
          instantiate (1 := ##R (runitor (#L f)) •
                              rinvunitor (#R(#L f)) •
                              (#R(#L f) ◃ psfunctor_id R (L b))).
          use vcomp_move_L_pM.
          { is_iso; apply psfunctor_is_invertible_2cell; is_iso. }
          use vcomp_move_R_Mp. { is_iso. }
          use vcomp_move_R_Mp. { apply psfunctor_is_invertible_2cell; is_iso. }
          exact (psfunctor_runitor R (#L f)).
        }
        rewrite <- !lwhisker_vcomp, !vassocl.
        etrans. {
          refine (maponpaths (λ α, _ • (_ • (_ • α))) _).
          now rewrite lwhisker_lwhisker, vassocr, lwhisker_lwhisker.
        }
        etrans. {
          rewrite !vassocl.
          refine (maponpaths (λ α, _ • (_ • α)) _).
          etrans; [apply vassocr|].
          refine (maponpaths (λ α, α • _) _).
          instantiate (1 := rinvunitor (η a · #R(#L f))).
          use vcomp_move_R_pM. { is_iso. }
          use vcomp_move_L_Mp. { is_iso. }
          apply pathsinv0, left_unit_assoc.
        }
        etrans. {
          refine (maponpaths (λ α, _ • (_ • α)) _).
          rewrite !lwhisker_vcomp.
          admit.
        }
  Admitted.

  Definition psfunctor_lassociator_from_left_universal_arrow
    : psfunctor_lassociator_law psfunctor_from_left_universal_arrow_data.
  Proof.
    intros a b c d f g h; cbn.
  Admitted.

  Definition psfunctor_lwhisker_from_left_universal_arrow
    : psfunctor_lwhisker_law psfunctor_from_left_universal_arrow_data.
  Proof.
    intros a b c f g₁ g₂ β.
    apply (Injectivity (μ_f' _ _)).
    { apply isweqonpathsincl, isinclweq, isweq_μ_f'. }
    unfold μ_f'.
    rewrite !psfunctor_vcomp, <- !lwhisker_vcomp, !vassocl.
    etrans. {
      etrans. {
        apply maponpaths.
        instantiate (1 := μ a (L c) (f · g₁ · η c) • ((f ◃ β) ▹ η c)).
        exact (nat_trans_ax (μ a (L c)) _ _ _).
      }
      rewrite vassocr.
      apply maponpaths_2.
      exact (φ_adj_inv_after_φ_adj (Hηadj _ _) _).
    }
    apply pathsinv0.
    etrans. {
      apply maponpaths.
      exact (φ_adj_inv_after_φ_adj (Hηadj _ _) _).
    }
    rewrite !vassocl, !vassocr.
    etrans. {
      do 5 apply maponpaths_2.
      rewrite lwhisker_vcomp.
      apply maponpaths.
      instantiate (1 := (psfunctor_comp R _ _)^-1 • (#R(#L f) ◃ ##R(##L β))).
      use vcomp_move_R_Mp. { apply is_invertible_2cell_inv. }
      rewrite vassocl.
      use vcomp_move_L_pM. { apply is_invertible_2cell_inv. }
      exact (psfunctor_lwhisker R _ _).
    }
    rewrite <- lwhisker_vcomp.
    etrans. {
      do 4 apply maponpaths_2.
      now rewrite vassocl, lwhisker_lwhisker, vassocr.
    }
    etrans. {
      do 3 apply maponpaths_2.
      rewrite vassocl.
      apply maponpaths.
      instantiate (1 := ((μ a (L b) (f · η b) ▹ # R (#L g₁)) • ((f · η b) ◃ ## R (##L β)))).
      apply pathsinv0, vcomp_whisker.
    }
    etrans. {
      rewrite vassocr.
      do 2 apply maponpaths_2.
      rewrite vassocl.
      apply maponpaths, pathsinv0, lwhisker_lwhisker_rassociator.
    }
    etrans. {
      rewrite vassocr.
      etrans; [apply maponpaths_2, vassocl|].
      rewrite vassocl, lwhisker_vcomp.
      apply maponpaths.
      etrans. {
        apply maponpaths_2, maponpaths.
        instantiate (1 := μ b (L c) (g₁ · η c) • (β ▹ η c)).
        exact (nat_trans_ax (μ b (L c)) _ _ _).
      }
      rewrite <- lwhisker_vcomp, vassocl.
      apply maponpaths, rwhisker_lwhisker.
    }
    rewrite !vassocr.
    reflexivity.
  Qed.

  Definition psfunctor_rwhisker_from_left_universal_arrow
    : psfunctor_rwhisker_law psfunctor_from_left_universal_arrow_data.
  Proof.
    intros a b c f₁ f₂ g α.
    apply (Injectivity (μ_f' _ _)).
    { apply isweqonpathsincl, isinclweq, isweq_μ_f'. }
    unfold μ_f'.
    rewrite !psfunctor_vcomp, <- !lwhisker_vcomp, !vassocl.
    etrans. {
      etrans. {
        apply maponpaths.
        instantiate (1 := μ a (L c) (f₁ · g · η c) • ((α ▹ g) ▹ η c)).
        exact (nat_trans_ax (μ a (L c)) _ _ _).
      }
      rewrite vassocr.
      apply maponpaths_2.
      exact (φ_adj_inv_after_φ_adj (Hηadj _ _) _).
    }
    apply pathsinv0.
    etrans. {
      apply maponpaths.
      exact (φ_adj_inv_after_φ_adj (Hηadj _ _) _).
    }
    rewrite !vassocl, !vassocr.
    etrans. {
      do 5 apply maponpaths_2.
      rewrite lwhisker_vcomp.
      apply maponpaths.
      instantiate (1 := (psfunctor_comp R _ _)^-1 • (##R(##L α) ▹ #R(#L g))).
      use vcomp_move_R_Mp. { apply is_invertible_2cell_inv. }
      rewrite vassocl.
      use vcomp_move_L_pM. { apply is_invertible_2cell_inv. }
      exact (psfunctor_rwhisker R _ _).
    }
    rewrite <- lwhisker_vcomp.
    etrans. {
      do 4 apply maponpaths_2.
      now rewrite vassocl, rwhisker_lwhisker, vassocr.
    }
    etrans. {
      do 3 apply maponpaths_2.
      rewrite vassocl, rwhisker_vcomp.
      do 2 apply maponpaths.
      instantiate (1 := μ a (L b) (f₁ · η b) • (α ▹ η b)).
      exact (nat_trans_ax (μ a (L b)) _ _ _).
    }
    etrans. {
      rewrite <- rwhisker_vcomp, vassocr.
      do 2 apply maponpaths_2.
      rewrite vassocl.
      apply maponpaths, rwhisker_rwhisker_alt.
    }
    etrans. {
      rewrite vassocr.
      apply maponpaths_2.
      rewrite vassocl.
      apply maponpaths.
      instantiate (1 := (f₁ ◃ μ b (L c) (g · η c)) • (α ▹ (g · η c))).
      apply vcomp_whisker.
    }
    etrans. {
      rewrite vassocr, vassocl.
      apply maponpaths, pathsinv0, rwhisker_rwhisker.
    }
    rewrite vassocr.
    reflexivity.
  Qed.

  Definition psfunctor_from_left_universal_arrow_laws
    : psfunctor_laws psfunctor_from_left_universal_arrow_data.
  Proof.
    split7; red; cbn -[identitor compositor].
    - exact psfunctor_id2_from_left_universal_arrow.
    - exact psfunctor_vcomp2_from_left_universal_arrow.
    - exact psfunctor_lunitor_from_left_universal_arrow.
    - exact psfunctor_runitor_from_left_universal_arrow.
    - exact psfunctor_lassociator_from_left_universal_arrow.
    - exact psfunctor_lwhisker_from_left_universal_arrow.
    - exact psfunctor_rwhisker_from_left_universal_arrow.
  Qed.

  Definition psfunctor_from_left_universal_arrow_invertible_cells
    : invertible_cells psfunctor_from_left_universal_arrow_data.
  Proof.
    split.
    - exact identitor_inv.
    - exact @compositor_inv.
  Defined.

  Definition psfunctor_from_left_universal_arrow : psfunctor A B
    := make_psfunctor
         psfunctor_from_left_universal_arrow_data
         psfunctor_from_left_universal_arrow_laws
         psfunctor_from_left_universal_arrow_invertible_cells.

End psfunctor_from_LUA.

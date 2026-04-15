(********************************************************************************

 The action of a pseudofunctor on an adjunction.

 Given a pseudofunctor [F : C → D], an adjunction [f ⊣ g : b -> a] in [C] gives
 rise to an adunction [Ff ⊣ Fg : Fb -> Fa] in D.

 Contents:
 1. Pseudofunctors preserve adjunctions.

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Algebra.GaussianElimination.Auxiliary.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Export UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Import PseudoFunctor.Notations.

Local Open Scope bicategory_scope.
Local Open Scope cat.

(** 1. Pseudofunctors preserve adjunctions. *)

Definition map_left_adjoint_data {C D : bicat} (F : psfunctor C D)
  {a b : C} (f : a --> b) (adj : left_adjoint_data f)
  : left_adjoint_data (#F f).
Proof.
  exists (#F (left_adjoint_right_adjoint adj)).
  split.
  - exact (psfunctor_id F a • ##F (left_adjoint_unit adj) • (psfunctor_comp F _ _)^-1).
  - exact (psfunctor_comp F _ _ • ##F (left_adjoint_counit adj) • (psfunctor_id F _)^-1).
Defined.

Lemma map_left_adjoint_data_id {C : bicat}
  {a b : C} (f : a --> b) (adj : left_adjoint_data f)
  : map_left_adjoint_data (id_psfunctor C) f adj = adj.
Proof.
  use pair_path_in2.
  abstract (use dirprod_paths; cbn;
            now rewrite id2_left, id2_right).
Defined.

Lemma map_left_adjoint_data_comp {C D E : bicat}
  (G : psfunctor D E) (F : psfunctor C D)
  {a b : C} (f : a --> b) (adj : left_adjoint_data f)
  : map_left_adjoint_data (comp_psfunctor G F) f adj
    = map_left_adjoint_data G _ (map_left_adjoint_data F f adj).
Proof.
  use pair_path_in2.
  use dirprod_paths.
  - abstract (
        pose (η := left_adjoint_unit adj);
        pose (ε := left_adjoint_counit adj);
        pose (g := left_adjoint_right_adjoint adj);
        change (
            psfunctor_id G (F a) • ##G (psfunctor_id F a) • ##G (##F η)
              • (##G (psfunctor_comp F f g)^-1 • (psfunctor_comp G (#F f) (# F g))^-1)
            = psfunctor_id G (F a) • ##G ((psfunctor_id F a • ##F η) • (psfunctor_comp F f g)^-1)
                • (psfunctor_comp G (#F f) (#F g))^-1
          );
        rewrite !(psfunctor_vcomp G);
        now rewrite !vassocr).
  - abstract (
        pose (η := left_adjoint_unit adj);
        pose (ε := left_adjoint_counit adj);
        pose (g := left_adjoint_right_adjoint adj);
        change (
            psfunctor_comp G (#F g) (#F f) • ##G (psfunctor_comp F g f) • ## G (## F ε)
              • (## G (psfunctor_id F b)^-1 • (psfunctor_id G (F b))^-1)
            = psfunctor_comp G (# F g) (# F f)
                • ## G ((psfunctor_comp F g f • ## F ε) • (psfunctor_id F b)^-1)
                • (psfunctor_id G (F b))^-1
          );
        rewrite !(psfunctor_vcomp G);
        now rewrite !vassocr).
Defined.

Definition map_left_adjoint_axioms {C D : bicat} (F : psfunctor C D)
  {a b : C} (f : a --> b) (adj : left_adjoint_data f) (Hadj : left_adjoint_axioms adj)
  : left_adjoint_axioms (map_left_adjoint_data F f adj).
Proof.
  unfold left_adjoint_axioms.
  unfold left_adjoint_unit, left_adjoint_counit, left_adjoint_right_adjoint.
  unfold map_left_adjoint_data; cbn delta iota.
  set (g := left_adjoint_right_adjoint adj).
  set (η := left_adjoint_unit adj).
  set (ε := left_adjoint_counit adj).
  split.
  - (* https://q.uiver.app/#q=WzAsMTgsWzAsMywiRmYiXSxbMCwyLCIxX3tGYX07RmYiXSxbMSwyLCJGMV9hO0ZmIl0sWzIsMiwiRihmO2cpO0ZmIl0sWzMsMiwiKEZmO0ZnKTtGZiJdLFs0LDIsIkZmOyhGZztGZikiXSxbNCwzLCJGZjtGKGc7ZikiXSxbNCw1LCJGZjtGMV9iIl0sWzAsNSwiRmY7MV97RmJ9Il0sWzAsMCwiZiJdLFsxLDAsIjFfYTtmIl0sWzIsMCwiKGY7Zyk7ZiJdLFszLDAsImY7KGc7ZikiXSxbMywxLCJmOzFfYiJdLFsxLDMsIkYoMV9hO2YpIl0sWzIsMywiRigoZjtnKTtmKSJdLFszLDMsIkYoZjsoZztmKSkiXSxbMyw0LCJGKGY7MV9iKSJdLFswLDEsIlxcbGFtYmRhXnstMX1fe0ZmfSIsMCx7ImNvbG91ciI6WzAsNjAsNDBdfSxbMCw2MCw0MCwxXV0sWzEsMiwiXFxpb3RhXkZfYTtGZiIsMCx7ImNvbG91ciI6WzAsNjAsNDBdfSxbMCw2MCw0MCwxXV0sWzIsMywiRlxcZXRhO0ZmIiwwLHsiY29sb3VyIjpbMzAsNjAsNDBdfSxbMzAsNjAsNDAsMV1dLFszLDQsIlxcZ2FtbWFee0YtMX1fe2csZn0gO0ZmIiwwLHsiY29sb3VyIjpbMTIwLDYwLDMwXX0sWzEyMCw2MCwzMCwxXV0sWzQsNSwiXFxhbHBoYV97RmYsRmcsRmZ9IiwwLHsiY29sb3VyIjpbMTIwLDYwLDMwXX0sWzEyMCw2MCwzMCwxXV0sWzUsNiwiRmY7XFxnYW1tYV57Rn1fe2csZn0iLDAseyJjb2xvdXIiOlsxMjAsNjAsMzBdfSxbMTIwLDYwLDMwLDFdXSxbNiw3LCJGZjtGXFxlcHNpbG9uIiwwLHsiY29sb3VyIjpbMTgwLDYwLDQwXX0sWzE4MCw2MCw0MCwxXV0sWzcsOCwiRmY7XFxpb3RhXntGLTF9X2IiLDAseyJjb2xvdXIiOlsyNDAsNjAsMjBdfSxbMjQwLDYwLDIwLDFdXSxbOSwxMCwiXFxsYW1iZGFeey0xfV9mIl0sWzEwLDExLCJcXGV0YTtmIl0sWzExLDEyLCJcXGFscGhhX3tmLGcsZn0iXSxbMTIsMTMsImY7XFxlcHNpbG9uIl0sWzEzLDksIlxccmhvX2IiLDAseyJjdXJ2ZSI6LTJ9XSxbOCwwLCJcXHJob157LTF9X3tGZn0iLDAseyJjb2xvdXIiOlsyNDAsNjAsMjBdfSxbMjQwLDYwLDIwLDFdXSxbMCwxNCwiRlxcbGFtYmRhXnstMX1fZiIsMCx7ImNvbG91ciI6WzAsNjAsNjBdfSxbMCw2MCw2MCwxXV0sWzE0LDIsIlxcZ2FtbWFee0YtMX1fezFfYTtmfSIsMCx7ImNvbG91ciI6WzAsNjAsNjBdfSxbMCw2MCw2MCwxXV0sWzE1LDMsIlxcZ2FtbWFee0YtMX1feyhmO2cpLGZ9IiwwLHsiY29sb3VyIjpbMzAsNjAsNjBdfSxbMzAsNjAsNjAsMV1dLFsxNCwxNSwiRihcXGV0YTtmKSIsMCx7ImNvbG91ciI6WzMwLDYwLDYwXX0sWzMwLDYwLDYwLDFdXSxbMTUsMTYsIkZcXGFscGhhX3tmLGcsZn0iLDAseyJjb2xvdXIiOlsxMjAsNjAsNjBdfSxbMTIwLDYwLDYwLDFdXSxbMTYsNiwiXFxnYW1tYV57Ri0xfV97ZiwoZztmKX0iLDAseyJjb2xvdXIiOlsxMjAsNjAsNjBdfSxbMTIwLDYwLDYwLDFdXSxbMTYsMTcsIkYoZjtcXGVwc2lsb24pIiwwLHsiY29sb3VyIjpbMTgwLDYwLDYwXX0sWzE4MCw2MCw2MCwxXV0sWzE3LDcsIlxcZ2FtbWFeRl97ZiwxX2J9IiwwLHsiY29sb3VyIjpbMTgwLDYwLDYwXX0sWzE4MCw2MCw2MCwxXV0sWzE3LDAsIkZcXHJob19mIiwwLHsiY3VydmUiOi0yLCJjb2xvdXIiOlsyNDAsNjAsNjBdfSxbMjQwLDYwLDYwLDFdXV0= *)
    etrans. {
      (* Red square *)
      do 3 apply maponpaths_2.
      rewrite <- !rwhisker_vcomp, !vassocr.
      do 2 apply maponpaths_2.
      instantiate (1:=##F (linvunitor f) • (psfunctor_comp F (id₁ a) f)^-1).
      use vcomp_move_L_Vp.
      use pathsinv0.
      use psfunctor_linvunitor.
    }
    etrans. {
      (* Orange square *)
      do 4 apply maponpaths_2.
      rewrite vassocl.
      apply maponpaths.
      instantiate (1:=##F (η ▹ f) • (psfunctor_comp F (f · g) f)^-1).
      use vcomp_move_L_Vp.
      rewrite vassocl.
      use pathsinv0.
      use vcomp_move_L_pV.
      use psfunctor_rwhisker.
    }
    etrans. {
      (* Green square *)
      apply maponpaths_2.
      rewrite <- !lwhisker_vcomp, !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      do 2 apply maponpaths.
      instantiate (1:=##F (rassociator f g f) • (psfunctor_comp F f (g · f))^-1).
      use vcomp_move_L_Vp.
      rewrite vassocl.
      use pathsinv0.
      use vcomp_move_L_pV.
      rewrite !vassocl.
      use vcomp_move_L_pM; [is_iso|].
      rewrite !vassocr.
      use psfunctor_rassociator.
    }
    etrans. {
      (* Blue square *)
      rewrite !vassocl.
      do 3 apply maponpaths.
      rewrite vassocr.
      apply maponpaths_2.
      instantiate (1:=##F (f ◃ ε) • (psfunctor_comp F f (id₁ b))^-1).
      use vcomp_move_L_Vp.
      rewrite vassocl.
      use pathsinv0.
      use vcomp_move_L_pV.
      use psfunctor_lwhisker.
    }
    etrans. {
      (* Violet square *)
      do 3 apply maponpaths.
      rewrite vassocl.
      apply maponpaths.
      instantiate (1:=##F (runitor f)).
      use pathsinv0.
      use vcomp_move_L_pV.
      use vcomp_move_L_pM; [is_iso|].
      rewrite vassocr.
      use pathsinv0.
      use psfunctor_runitor.
    }
    etrans. {
      (* Rainbow *)
      rewrite <- !psfunctor_vcomp.
      apply maponpaths.
      instantiate (1:=id₂ f).
      rewrite !vassocr.
      exact (pr1 Hadj).
    }
    use psfunctor_id2.
  - etrans. {
      (* Red square *)
      do 3 apply maponpaths_2.
      rewrite <- !lwhisker_vcomp, !vassocr.
      do 2 apply maponpaths_2.
      instantiate (1:=##F (rinvunitor g) • (psfunctor_comp F g (id₁ a))^-1).
      use vcomp_move_L_Vp.
      use pathsinv0.
      use psfunctor_rinvunitor.
    }
    etrans. {
      (* Orange square *)
      do 4 apply maponpaths_2.
      rewrite vassocl.
      apply maponpaths.
      instantiate (1:=##F (g ◃ η) • (psfunctor_comp F g (f · g))^-1).
      use vcomp_move_L_Vp.
      rewrite vassocl.
      use pathsinv0.
      use vcomp_move_L_pV.
      use psfunctor_lwhisker.
    }
    etrans. {
      (* Green square *)
      apply maponpaths_2.
      rewrite <- !rwhisker_vcomp, !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      do 2 apply maponpaths.
      instantiate (1:=##F (lassociator g f g) • (psfunctor_comp F _ _)^-1).
      use vcomp_move_L_Vp.
      rewrite vassocl.
      use pathsinv0.
      use vcomp_move_L_pV.
      rewrite !vassocl.
      use vcomp_move_L_pM; [is_iso|].
      rewrite !vassocr.
      use psfunctor_lassociator.
    }
    etrans. {
      (* Blue square *)
      rewrite !vassocl.
      do 3 apply maponpaths.
      rewrite vassocr.
      apply maponpaths_2.
      instantiate (1:=##F (ε ▹ g) • (psfunctor_comp F (id₁ b) g)^-1).
      use vcomp_move_L_Vp.
      rewrite vassocl.
      use pathsinv0.
      use vcomp_move_L_pV.
      use psfunctor_rwhisker.
    }
    etrans. {
      (* Violet square *)
      do 3 apply maponpaths.
      rewrite vassocl.
      apply maponpaths.
      instantiate (1:=##F (lunitor g)).
      use pathsinv0.
      use vcomp_move_L_pV.
      use vcomp_move_L_pM; [is_iso|].
      rewrite vassocr.
      use pathsinv0.
      use psfunctor_lunitor.
    }
    etrans. {
      (* Rainbow *)
      rewrite <- !psfunctor_vcomp.
      apply maponpaths.
      rewrite !vassocr.
      exact (pr2 Hadj).
    }
    use psfunctor_id2.
Qed.

Definition map_left_adjoint {C D : bicat} (F : psfunctor C D)
  {a b : C} (f : a --> b) (adj : left_adjoint f)
  : left_adjoint (#F f).
Proof.
  exists (map_left_adjoint_data F f adj).
  apply (map_left_adjoint_axioms F f adj adj).
Defined.

Lemma map_left_adjoint_id {C : bicat}
  {a b : C} (f : a --> b) (adj : left_adjoint f)
  : map_left_adjoint (id_psfunctor C) f adj = adj.
Proof.
  use subtypePath'; [|use isapropdirprod; use cellset_property].
  use map_left_adjoint_data_id.
Defined.

Lemma map_left_adjoint_comp {C D E : bicat}
  (G : psfunctor D E) (F : psfunctor C D)
  {a b : C} (f : a --> b) (adj : left_adjoint f)
  : map_left_adjoint (comp_psfunctor G F) f adj
    = map_left_adjoint G _ (map_left_adjoint F f adj).
Proof.
  use subtypePath'; [|use isapropdirprod; use cellset_property].
  use map_left_adjoint_data_comp.
Defined.

Definition map_adjunction {C D : bicat} (F : psfunctor C D)
  {a b : C} (adj : adjunction a b)
  : adjunction (F a) (F b)
  := _,,map_left_adjoint F _ (pr2 adj).

Lemma map_adjunction_id {C : bicat}
  {a b : C} (adj : adjunction a b)
  : map_adjunction (id_psfunctor C) adj = adj.
Proof.
  use pair_path_in2.
  use map_left_adjoint_id.
Defined.

Lemma map_adjunction_comp {C D E : bicat}
  (G : psfunctor D E) (F : psfunctor C D)
  {a b : C} (adj : adjunction a b)
  : map_adjunction (comp_psfunctor G F) adj
    = map_adjunction G (map_adjunction F adj).
Proof.
  use pair_path_in2.
  use map_left_adjoint_comp.
Defined.

(********************************************************************************

 Epis and Monics in a Unital Magmoid

 Author: B. Szilvasy
 January 2026

 This development is analogous to that of [Epi] and [Monic] for categories, but relaxing
 associativity constraints as much as possible.

 Contents:
 TODO

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Opposite.

Local Open Scope cat.
Local Open Scope unital_magmoid.

Section epis_monics_defs.
  Context {M : precategory_data}.
  Hypothesis hs : has_homsets M.

  (** Epis *)
  Definition is_epi {a b : M} (f : a --> b) : UU
    := ∏ (c : M) (g h : b --> c), f · g = f · h -> g = h.

  Lemma isaprop_is_epi' {a b : M} (f : a --> b) : isaprop (is_epi f).
  Proof. do 4 (apply impred; intro). apply hs. Qed.

  Definition epi (a b : M) : UU := ∑ f : M⟦a, b⟧, is_epi f.
  Definition make_epi {a b : M} (f : M⟦a, b⟧) (H : is_epi f)
    : epi a b := f,,H.

  Coercion epi_mor {a b : M} (f : epi a b) : M⟦a, b⟧ := pr1 f.
  Coercion epi_is_epi {a b : M} (f : epi a b) : is_epi f := pr2 f.

  (** Monics *)
  Definition is_monic {a b : M} (f : a --> b) : UU
    := ∏ (c : M) (g h : c --> a), f ∘ g = f ∘ h -> g = h.

  Lemma isaprop_is_monic' {a b : M} (f : a --> b) : isaprop (is_monic f).
  Proof. do 4 (apply impred; intro). apply hs. Qed.

  Definition monic (a b : M) : UU := ∑ f : M⟦a, b⟧, is_monic f.
  Definition make_monic {a b : M} (f : M⟦a, b⟧) (H : is_monic f)
    : monic a b := f,,H.

  Coercion monic_mor {a b : M} (f : monic a b) : M⟦a, b⟧ := pr1 f.
  Coercion monic_is_monic {a b : M} (f : monic a b) : is_monic f := pr2 f.

End epis_monics_defs.

Section epis_monics_lemmas.
  (** *** Epi Lemmas *)

  (** Composition with an epi is injective *)
  Lemma precomp_with_epi_isincl {M : precategory_data} (hs : has_homsets M)
    {a b : M} {f : a --> b} :
    is_epi f -> ∏ c, isincl (@precomp_with _ _ _ f c).
  Proof.
    intros Hf c g.
    apply invproofirrelevance.
    intros z w.
    apply subtypePath'; [|apply hs].
    apply (Hf _ (hfiberpr1 _ _ z) (hfiberpr1 _ _ w)).
    exact (hfiberpr2 _ _ z @ !hfiberpr2 _ _ w).
  Qed.

  (** Composing two epis is an epi so long as [f] is thunkable. *)
  Lemma is_epi_comp {M : precategory_data} {a b c : M} (f : a --> b) (g : b --> c)
    (Hthunkable : is_thunkable f)
    : is_epi f -> is_epi g -> is_epi (f · g).
  Proof.
    intros Hf Hg d h h' Heq.
    apply Hg, Hf.
    etrans; [apply (assoc_thunkable _ Hthunkable)|].
    etrans; [|apply (assoc'_thunkable _ Hthunkable)].
    exact Heq.
  Defined.

  (** If precomposition of [g] with [f] is an epi, and [f] is thunkable, then [g] is an epi. *)
  Lemma is_epi_precomp {M : precategory_data} {a b c : M} (f : a --> b) (g : b --> c)
    (Hthunkable : is_thunkable f)
    : is_epi (f · g) -> is_epi g.
  Proof.
    intros Hfg d h h' Heq.
    apply Hfg.
    etrans; [apply (assoc'_thunkable _ Hthunkable)|].
    etrans; [|apply (assoc_thunkable _ Hthunkable)].
    apply cancel_precomposition.
    exact Heq.
  Defined.

  (** Identities are epi *)
  Lemma is_epi_identity {M : unital_premagmoid} (a : M) : is_epi (identity a).
  Proof.
    intros b f g Hf.
    exact (!magmoid_id_left f @ Hf @ magmoid_id_left g).
  Defined.

  (** *** Monic Lemmas *)

  (** Composition with an epi is injective *)
  Lemma postcomp_with_monic_isincl {M : precategory_data} (hs : has_homsets M)
    {a b : M} {f : a <-- b} :
    is_monic f -> ∏ c, isincl (@postcomp_with _ _ _ f c).
  Proof.
    intros Hf c g.
    apply invproofirrelevance.
    intros z w.
    apply subtypePath'; [|apply hs].
    apply (Hf _ (hfiberpr1 _ _ z) (hfiberpr1 _ _ w)).
    exact (hfiberpr2 _ _ z @ !hfiberpr2 _ _ w).
  Qed.

  (** Composing two monics is an monic so long as [f] is linear. *)
  Lemma is_monic_comp {M : precategory_data} {a b c : M} (f : a <-- b) (g : b <-- c)
    (Hlinear : is_linear f)
    : is_monic f -> is_monic g -> is_monic (f ∘ g).
  Proof.
    intros Hf Hg d h h' Heq.
    apply Hg, Hf.
    etrans; [apply (assoc'_linear _ Hlinear)|].
    etrans; [|apply (assoc_linear _ Hlinear)].
    exact Heq.
  Defined.

  (** If postcomposition of [g] with [f] is an monic, and [f] is linear, then [g] is an monic. *)
  Lemma is_monic_postcomp {M : precategory_data} {a b c : M} (f : a <-- b) (g : b <-- c)
    (Hlinear : is_linear f)
    : is_monic (f ∘ g) -> is_monic g.
  Proof.
    intros Hfg d h h' Heq.
    apply Hfg.
    etrans; [apply (assoc_linear _ Hlinear)|].
    etrans; [|apply (assoc'_linear _ Hlinear)].
    apply cancel_postcomposition.
    exact Heq.
  Defined.

  (** Identities are monic *)
  Lemma is_monic_identity {M : unital_premagmoid} (a : M) : is_monic (identity a).
  Proof.
    intros b f g Hf.
    exact (!magmoid_id_right f @ Hf @ magmoid_id_right g).
  Defined.
End epis_monics_lemmas.

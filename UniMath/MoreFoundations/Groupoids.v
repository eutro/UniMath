(** Elimination from [ishinh] into groupoids.

 Based on "The General Universal Property of the Propositional Truncation" by Kraus,
 Nicolai. 2015. https://doi.org/10.4230/LIPICS.TYPES.2014.111)
 *)

Require Export UniMath.MoreFoundations.Propositions.

(** Orthogonal types. *)
Section orthogonal.
  Definition are_orthogonal (A B : UU) : UU
    := isweq (λ (x : B) (_ : A), x).

  Definition are_orthogonal_weq {A B : UU}
    (H : are_orthogonal A B)
    : B ≃ (A -> B)
    := make_weq _ H.

  Lemma is_const_to_eq {A B : UU}
    (f : A -> B)
    (H : ∃! b, (λ _, b) = f)
    (x y : A)
    : f x = f y.
  Proof.
    induction (iscontrpr1 H) as [b Hb].
    exact (!eqtohomot Hb x @ eqtohomot Hb y).
  Defined.

  Lemma invmap_are_orthogonal_eq {A B : UU}
    (H : are_orthogonal A B)
    (f : A -> B) (x : A)
    : invmap (are_orthogonal_weq H) f = f x.
  Proof.
    apply pathsinv0, pathsweq1; cbn.
    apply funextfun; intro y; cbn.
    apply is_const_to_eq, H.
  Qed.

  Lemma are_orthogonal_sec_from_ishinh
    (A : UU) (P : A -> UU)
    : are_orthogonal (∥ A ∥) (∏ x, P x).
  Proof.
    use isweq_iso.
    - intro g; exact (λ x, g (hinhpr x) x).
    - easy.
    - abstract (
          intros g;
          apply funextsec; intro H;
          apply funextsec; intro x;
          refine (maponpaths (λ H, g H x) _);
          apply proofirrelevance, propproperty).
  Defined.

  Lemma are_orthogonal_total2_sec_from_ishinh
    (A : UU) (P : A -> UU) (Q : (∏ x, P x) -> UU)
    (HQ : ∏ f, are_orthogonal (∥ A ∥) (Q f))
    : are_orthogonal (∥ A ∥) (∑ f, Q f).
  Proof.
    use weqhomot.
    1: intermediate_weq (∑ (f : ∥ A ∥ -> ∏ x, P x), ∏ (h : ∥ A ∥), Q (f h)).
    - use weqbandf.
      + exact (are_orthogonal_weq (are_orthogonal_sec_from_ishinh _ _)).
      + intro f; exact (are_orthogonal_weq (HQ f)).
    - apply weqtotaltoforall.
    - easy.
  Defined.

  Definition remake_are_orthogonal {A B : UU} (a : A)
    : are_orthogonal A B -> are_orthogonal A B.
  Proof.
    intro H.
    use isweq_iso.
    - intro f; exact (f a).
    - easy.
    - abstract (
          intro f;
          apply funextfun; intro b;
          apply is_const_to_eq, H).
  Defined.
End orthogonal.

(** Eliminator from [ishinh] to groupoids.

 We show that [B] is equivalent to the coherently constant functions out of [A]
 ([groupoid_squash_fun]), so long as [A] is inhabited.  The value of [B] computed
 from the coherently constant function is definitionally the one arising from the
 inhabitedness proof.
 *)
Section elim_ishinh_groupoid.
  Context {A B : UU}.
  Hypothesis isg : isofhlevel 3 B.

  Let const (f : A -> B) := ∏ (x₁ x₂ : A), f x₁ = f x₂.
  Let coh (f : A -> B) (c : const f) := ∏ (x₁ x₂ x₃ : A), c x₁ x₂ @ c x₂ x₃ = c x₁ x₃.

  Let groupoid_squash_fun := ∑ (f : A -> B) (c : const f), coh f c.

  Let squash_to_groupoid_fun : B -> groupoid_squash_fun.
  Proof.
    intro f₁.
    simple refine (_,, _,, _).
    - intros _; exact f₁.
    - easy.
    - easy.
  Defined.

  Local Definition groupoid_squash_fun_equiv
    (f g : groupoid_squash_fun) : UU
    := ∑ (α : pr1 f ~ pr1 g),
      ∏ (a₁ a₂ : A),
      pr12 f a₁ a₂ @ α a₂
      = α a₁ @ pr12 g a₁ a₂.

  Local Lemma groupoid_squash_fun_eq_weq₀
    (f g : groupoid_squash_fun)
    : f = g ≃ groupoid_squash_fun_equiv f g.
  Proof.
    induction f as [f [cf df]].
    induction g as [g [cg dg]].
    eapply weqcomp; [apply total2_paths_equiv|].
    use weqbandf; [apply invweq, weqfunextsec|].
    cbn; intro p; induction p; cbn.
    eapply weqcomp; [apply total2_paths_equiv|].
    eapply weqcomp. {
      apply weqpr1; intro p.
      refine ((_ : isaprop _) _ _).
      do 3 (apply impred; intro); use isg.
    }
    cbn.
    eapply weqcomp; [apply invweq, weqfunextsec|].
    use weqonsecfibers; intro a₁.
    eapply weqcomp; [apply invweq, weqfunextsec|].
    use weqonsecfibers; intro a₂.
    cbn.
    rewrite pathscomp0rid.
    exact (idweq _).
  Qed.

  Local Lemma squash_to_groupoid_fun_sec (a₀ : A) fcd
    : squash_to_groupoid_fun (pr1 fcd a₀) = fcd.
  Proof.
    induction fcd as [f [c d]].
    apply groupoid_squash_fun_eq_weq₀.
    use tpair.
    - exact (c a₀).
    - intros a₁ a₂; cbn.
      apply pathsinv0, d.
  Qed.

  Local Lemma isweq_squash_to_groupoid_fun (a : ∥ A ∥)
    : isweq squash_to_groupoid_fun.
  Proof.
    refine (squash_to_prop a (isapropisweq _) (λ a₀, _)); clear a.
    use isweq_iso.
    - intros [f _]; exact (f a₀). (* This ensures computability! *)
    - easy.
    - intro fcd; apply squash_to_groupoid_fun_sec.
  Defined.

  Lemma make_squash_to_groupoid_weq
    (H : are_orthogonal (∥ A ∥) (∑ (f : A -> B) (c : const f), coh f c))
    : (∥ A ∥ -> B) ≃ (∑ (f : A -> B) (c : const f), coh f c).
  Proof.
    pose (w := λ (h : ∥ A ∥), make_weq _ (isweq_squash_to_groupoid_fun h)).
    use remakeweqboth.
    - refine (weqcomp _ (invweq (are_orthogonal_weq H))).
      apply weqonsecfibers; exact w.
    - intro f.
      apply (invmap (are_orthogonal_weq H)); intro h.
      exact (squash_to_groupoid_fun (f h)).
    - intros f h; exact (invmap (w h) f).
    - easy.
    - abstract (
          intro f;
          apply funextfun; intro h;
          refine (toforallpaths (λ _, B) _ (λ _, invmap (w h) f) _ h);
          rewrite invmap_weqcomp_expand;
          apply pathsinv0, pathsweq1;
          apply funextfun; intro h';
          exact (homotweqinvweq (w h) f)).
  Defined.

  Lemma squash_to_groupoid_weq
    : (∥ A ∥ -> B) ≃ (∑ (f : A -> B) (c : const f), coh f c).
  Proof.
    apply make_squash_to_groupoid_weq.
    abstract (
        do 2 (apply are_orthogonal_total2_sec_from_ishinh; intro);
        apply are_orthogonal_sec_from_ishinh).
  Defined.

  Lemma squash_to_groupoid_weq_from_ishinh (h : ∥ A ∥)
    : (∥ A ∥ -> B) ≃ (∑ (f : A -> B) (c : const f), coh f c).
  Proof.
    apply make_squash_to_groupoid_weq.
    apply (remake_are_orthogonal h).
    abstract (
        do 2 (apply are_orthogonal_total2_sec_from_ishinh; intro);
        apply are_orthogonal_sec_from_ishinh).
  Defined.

  Definition squash_to_groupoid
    (f : A -> B) (c : const f) (d : coh f c)
    : ∥ A ∥ -> B.
  Proof.
    pose (fc := weqproperty squash_to_groupoid_weq (f,,c,,d)).
    exact (pr11 fc).
  Defined.

  Definition squash_to_groupoid_compute
    (f : A -> B) (c : const f) (d : coh f c)
    (x : A)
    : squash_to_groupoid f c d (hinhpr x) = f x.
  Proof. reflexivity. Defined.

End elim_ishinh_groupoid.

Section dep_elim_ishinh_groupoid.
  Context {A : UU} (P : ∥ A ∥ -> UU) (isg : ∏ h, isofhlevel 3 (P h)).

  Let constd (f : ∏ a, P (hinhpr a))
      := ∏ (a₁ a₂ : A), tpair P _ (f a₁) = tpair P _ (f a₂).

  Let cohd (f : ∏ a, P (hinhpr a)) (c : constd f)
      := ∏ (a₁ a₂ a₃ : A), c a₁ a₂ @ c a₂ a₃ = c a₁ a₃.

  Definition squash_to_groupoid_dep
    (f : ∏ a, P (hinhpr a))
    (c : constd f)
    (d : cohd f c)
    : ∏ a, P a.
  Proof.
    transparent assert (f : (∥ A ∥ -> total2 P)). {
      use squash_to_groupoid.
      - apply isofhleveltotal2.
        + apply isofhlevelsnprop, propproperty.
        + exact isg.
      - exact (λ a, tpair P _ (f a)).
      - exact c.
      - exact d.
    }
    intro h.
    refine (transportf P (proofirrelevance_hProp _ _ _) _).
    exact (pr2 (f h)).
  Defined.

  Definition squash_to_groupoid_dep_eq
    (f : ∏ a, P (hinhpr a))
    (c : constd f)
    (d : cohd f c)
    (x : A)
    : squash_to_groupoid_dep f c d (hinhpr x) = f x.
  Proof.
    unfold squash_to_groupoid_dep; cbn.
    refine (maponpaths (λ e, transportf P e (f x))
              (_ : _ = idpath (hinhpr x))).
    apply proofirrelevancecontr, propproperty.
  Defined.

End dep_elim_ishinh_groupoid.

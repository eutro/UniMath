(********************************************************************************

 Yoneda Lemma for Unital Magmoids

 Author: B. Szilvasy
 January 2026

 Contents:
 TODO

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.FromCategory.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Subcategories.

Local Open Scope cat.
Local Open Scope unital_magmoid.

Section notfunctor_magmoid.
  (* A not-quite-functor is a functor which does not preserve composition. *)
  Definition notfunctor (M M' : unital_premagmoid_data)
    := ∑ (F : functor_data M M'), functor_idax F.
  Definition make_notfunctor {M M' : unital_premagmoid_data}
    (F : functor_data M M') (H : functor_idax F)
    : notfunctor M M' := F,,H.
  Coercion notfunctor_to_functor_data {M M' : unital_premagmoid_data} (F : notfunctor M M')
    := pr1 F.

  Definition notfunctor_id {M M' : unital_premagmoid_data} (F : notfunctor M M')
    : ∏ (a : M), #F (identity a) = identity (F a)
    := pr2 F.

  Definition functor_to_notfunctor {M M' : unital_premagmoid_data} (F : functor M M') : notfunctor M M'.
  Proof.
    use (make_notfunctor F).
    intro a; apply functor_id.
  Defined.
  Coercion functor_to_notfunctor : functor >-> notfunctor.

  Definition notfunctor_identity (M : unital_premagmoid_data)
    : notfunctor M M := functor_identity M.

  (* Not-quite-functors do not preserve composition, so their morphisms do not either. *)
  Definition notfunctor_magmoid_ob_mor (M M' : unital_premagmoid_data) : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (notfunctor M M').
    - intros F G; exact (nat_trans_data F G).
  Defined.

  Definition notfunctor_magmoid_data (M M' : unital_premagmoid_data) : unital_premagmoid_data.
  Proof.
    use (make_precategory_data (notfunctor_magmoid_ob_mor M M')).
    - intros F a; apply identity.
    - intros F G H α β a;
        apply (α a · β a).
  Defined.

  Definition notfunctor_magmoid_is_unital (M : unital_premagmoid_data) (M' : unital_premagmoid)
    : is_unital_premagmoid (notfunctor_magmoid_data M M').
  Proof.
    split; intros F G α;
      apply funextsec; intro a.
    - apply magmoid_id_left.
    - apply magmoid_id_right.
  Defined.

  Definition notfunctor_magmoid_is_assoc (M : unital_premagmoid_data) (M' : precategory)
    : is_assoc_premagmoid (notfunctor_magmoid_data M M').
  Proof.
    split; intros F G H K α β δ;
      apply funextsec; intro a.
    - apply assoc.
    - apply assoc'.
  Defined.

  Definition notfunctor_unital_premagmoid (M : unital_premagmoid_data) (M' : unital_premagmoid)
    : unital_premagmoid
    := make_unital_premagmoid _ (notfunctor_magmoid_is_unital M M').

  Definition has_homsets_notfunctor_unital_premagmoid (M M' : unital_premagmoid_data)
    (hs : has_homsets M')
    : has_homsets (notfunctor_magmoid_data M M').
  Proof.
    intros F G.
    apply impred_isaset; intro a; apply hs.
  Qed.

  Definition notfunctor_unital_magmoid (M : unital_premagmoid_data) (M' : unital_magmoid) : unital_magmoid.
  Proof.
    use make_unital_magmoid.
    - exact (notfunctor_unital_premagmoid M M').
    - abstract (apply has_homsets_notfunctor_unital_premagmoid, unital_magmoid_has_homsets).
  Defined.

  (** Call α "locally natural" at [f : a --> b] when the naturality square communtes. *)
  Definition is_locally_natural {C D : precategory_data} {F G : functor_data C D} (α : nat_trans_data F G)
    {a b : C} (f : a --> b) : UU
    := # F f · α b = α a · #G f.

End notfunctor_magmoid.

Section yoneda.
  Context [M : unital_magmoid].

  Notation Mᵒᵖ := (opp_precat_data M).
  Notation Mₜᵒᵖ := (opp_precat_data (M ₜ)).

  (* [um_yoneda_ob a] is the postcomposition not-quite-functor [M⟦a, -⟧]. *)
  Definition um_yoneda_objects_ob (a b : M) : hSet
    := make_hSet (M⟦b, a⟧) (unital_magmoid_has_homsets M b a).

  Definition um_yoneda_objects_mor (a : M) {b b' : M} (f : b --> b')
    : um_yoneda_objects_ob a b' -> um_yoneda_objects_ob a b
    := λ g, f · g.

  Definition um_yoneda_objects (a : M) : functor_data Mᵒᵖ HSET.
  Proof.
    use make_functor_data.
    - intro b; exact (um_yoneda_objects_ob a b).
    - intros b b' f g; exact (um_yoneda_objects_mor a f g).
  Defined.

  Lemma um_yoneda_objects_id (a : M) : functor_idax (um_yoneda_objects a).
  Proof.
    intro b.
    apply funextsec; intro f.
    apply magmoid_id_left.
  Qed.

  (** Postcomposition is not functorial in general for unital magmoids *)
  Lemma um_yoneda_objects_comp (a : M) : functor_compax (um_yoneda_objects a).
  Proof.
    intros b c d f g.
    cbn in *.
    apply funextsec; intro h.
    cbn in *.
    change ((g · f) · h = g · (f · h)).
    (** Not associative in general! *)
  Abort.

  (** Postcomposition *is* functorial when restricted to thunkable maps *)
  Lemma um_yoneda_objects_comp_thunkable (a : M)
    {b c d : M} (f : c --> b) (g : d --> c) (Hg : is_thunkable g)
    : (λ x, um_yoneda_objects_mor a (f ∘ g) x) = (λ x, um_yoneda_objects_mor a g (um_yoneda_objects_mor a f x)).
  Proof.
    apply funextsec; intro h.
    apply assoc'_thunkable, Hg.
  Qed.

  Definition um_yoneda_ob (a : M) : notfunctor Mᵒᵖ HSET
    := make_notfunctor _ (um_yoneda_objects_id a).

  Definition um_yoneda_ob_thunkable (a : M) : functor Mₜᵒᵖ HSET.
  Proof.
    use make_functor.
    - refine (functor_composite_data _ (um_yoneda_objects a)).
      (* This is just [thunkable_category_to_unital_magmoid], but in the opposite categories *)
      use make_functor_data.
      + intro b; exact b.
      + cbn; intros b c f; exact f.
    - abstract (use make_is_functor;
                [ intros b; apply um_yoneda_objects_id
                | intros b c d f g;
                  cbn in f, g;
                  apply (um_yoneda_objects_comp_thunkable a f g g) ]).
  Defined.

  (** [um_yoneda_morphisms f] is the precomposition unnatural transformation [M⟦f, -⟧] *)
  Definition um_yoneda_morphisms {a a' : M} (f : a --> a')
    : nat_trans_data (um_yoneda_objects a) (um_yoneda_objects a')
    := λ b g, g · f.

  (** Precomposition is not natural in general *)
  Lemma is_nat_trans_um_yoneda_morphisms {a a' : M} (f : a --> a')
    : is_nat_trans _ _ (um_yoneda_morphisms f).
  Proof.
    intros b c g.
    apply funextsec; intro h.
    cbn in *.
    change ((g · h) · f = g · (h · f)).
    (** Not associative in general! *)
  Abort.

  (** The naturality equation at [identity a] always holds, however.
      It is useful to package up this data. *)
  Definition is_locally_yoneda_natural
    {a : M} {F : functor_data Mᵒᵖ HSET} (α : nat_trans_data (um_yoneda_objects a) F)
    {b : M} (f : b --> a) : UU
    := α b f = #F f (α a (identity a)).

  Definition is_yoneda_natural
    {a : M} {F : functor_data Mᵒᵖ HSET} (α : nat_trans_data (um_yoneda_objects a) F) : UU
    := ∏ (b : M) (f : b --> a), is_locally_yoneda_natural α f.

  Definition yoneda_nat_trans (a : M) (F : notfunctor Mᵒᵖ HSET) : UU
    := ∑ (α : nat_trans_data (um_yoneda_objects a) F), is_yoneda_natural α.
  Definition make_yoneda_nat_trans {a : M} {F : notfunctor Mᵒᵖ HSET}
    (α : nat_trans_data (um_yoneda_objects a) F)
    (H : is_yoneda_natural α) : yoneda_nat_trans a F
    := α,,H.
  Coercion yoneda_nat_trans_to_nat_trans_data {a : M} {F : notfunctor Mᵒᵖ HSET}
    (α : yoneda_nat_trans a F) : nat_trans_data (um_yoneda_objects a) F := pr1 α.
  Coercion yoneda_nat_trans_is_yoneda_natural {a : M} {F : notfunctor Mᵒᵖ HSET}
    (α : yoneda_nat_trans a F) : is_yoneda_natural α := pr2 α.

  Lemma isaprop_is_locally_yoneda_natural
    {a : M} {F : functor_data Mᵒᵖ HSET} (α : nat_trans_data (um_yoneda_objects a) F)
    {b : M} (f : b --> a)
    : isaprop (is_locally_yoneda_natural α f).
  Proof. apply setproperty. Qed.

  Lemma isaprop_is_yoneda_natural {a : M} {F : functor_data Mᵒᵖ HSET} (α : nat_trans_data (um_yoneda_objects a) F)
    : isaprop (is_yoneda_natural α).
  Proof.
    do 2 (apply impred; intro).
    apply isaprop_is_locally_yoneda_natural.
  Qed.

  Lemma is_yoneda_natural_um_yoneda_morphism  {a a' : M} (f : a --> a')
    : is_yoneda_natural (um_yoneda_morphisms f).
  Proof.
    intros b g.
    apply cancel_precomposition, pathsinv0, magmoid_id_left.
  Qed.

  (** Precomposition is natural when constrained to linear morphisms *)
  Lemma is_nat_trans_um_yoneda_morphisms_linear {a a' : M} (f : a --> a') (Hf : is_linear f)
    : is_nat_trans _ _ (um_yoneda_morphisms f).
  Proof.
    intros b c g.
    apply funextsec; intro h.
    apply assoc'_linear, Hf.
  Qed.

  (** Precomposition is also natural when the constrained to apply to thunkable morphisms. *)
  Lemma is_nat_trans_um_yoneda_morphisms_thunkable {a a' : M} (f : a --> a')
    : is_nat_trans (um_yoneda_ob_thunkable a) (um_yoneda_ob_thunkable a') (um_yoneda_morphisms f).
  Proof.
    intros b c g; cbn in g.
    apply funextsec; intro h.
    apply assoc'_thunkable, g.
  Qed.

  Definition um_yoneda_morphisms_linear {a a' : M} (f : linear_mor a a')
    : nat_trans (um_yoneda_objects a) (um_yoneda_objects a').
  Proof.
    use make_nat_trans.
    - apply (um_yoneda_morphisms f).
    - apply is_nat_trans_um_yoneda_morphisms_linear, f.
  Defined.

  Definition um_yoneda_morphisms_thunkable {a a' : M} (f : a --> a')
    : nat_trans (um_yoneda_ob_thunkable a) (um_yoneda_ob_thunkable a').
  Proof.
    use make_nat_trans.
    - apply (um_yoneda_morphisms f).
    - apply is_nat_trans_um_yoneda_morphisms_thunkable.
  Defined.

  (** [um_yoneda] is the not-quite-functor M ⟶ [Mᵒᵖ, HSET] mapping objects to their not-quite-functor *)
  Definition um_yoneda_functor_data
    : functor_data M (notfunctor_unital_magmoid Mᵒᵖ HSET).
  Proof.
    use make_functor_data.
    - intro a; exact (um_yoneda_ob a).
    - intros a b f;
        exact (um_yoneda_morphisms f).
  Defined.

  Lemma um_yoneda_functor_id
    : functor_idax um_yoneda_functor_data.
  Proof.
    intro a.
    do 2 (apply funextsec; intro).
    apply magmoid_id_right.
  Qed.

  (** [um_yoneda] is not functorial in general *)
  Lemma um_yoneda_functor_comp : functor_compax um_yoneda_functor_data.
  Proof.
    intros a b c f g.
    apply funextsec; intro d.
    apply funextsec; intro h.
    cbn in *.
    change (h · (f · g) = (h · f) · g).
    (** Not associative in general! *)
  Abort.

  (** [um_yoneda] is functorial when restricted to linear maps *)
  Lemma um_yoneda_functor_comp_linear
    {a b c : M} (f : a --> b) (g : b --> c) (Hg : is_linear g)
    : #um_yoneda_functor_data (f · g) = #um_yoneda_functor_data f · #um_yoneda_functor_data g.
  Proof.
    do 2 (apply funextsec; intro).
    apply assoc_linear, Hg.
  Qed.

  (** [um_yoneda] is the mapping of a unital magmoid into its category of (almost) presheaves *)
  Definition um_yoneda
    : notfunctor M (notfunctor_unital_magmoid Mᵒᵖ HSET)
    := make_notfunctor _ um_yoneda_functor_id.

  (** [um_yoneda] restricted to linear maps: a functor *)
  Lemma um_yoneda_linear : functor (M ₗ) (notfunctor_unital_magmoid Mᵒᵖ HSET).
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro a; exact (um_yoneda_ob a).
      + intros a b f; exact (um_yoneda_morphisms_linear f).
    - abstract (use make_is_functor;
                [ intro a; apply um_yoneda_functor_id
                | intros a b c f g; cbn in g;
                  apply um_yoneda_functor_comp_linear, g ]).
  Defined.

  (** [um_yoneda] restricted to thunkable maps in the second argument: the codomain is functors *)
  Lemma um_yoneda_thunkable : notfunctor M [Mₜᵒᵖ, HSET].
  Proof.
    use make_notfunctor.
    - use make_functor_data.
      + intro a; exact (um_yoneda_ob_thunkable a).
      + intros a b f; exact (um_yoneda_morphisms_thunkable f).
    - intro a.
      apply subtypePath'; [|apply isaprop_is_nat_trans, homset_property].
      apply um_yoneda_functor_id.
  Defined.

  (* [um_yoneda] restricted to linear maps and thunkable maps in the second argument: functorial
     at both points *)
  Lemma um_yoneda_linear_and_thunkable : functor (M ₗ) [Mₜᵒᵖ, HSET].
  Proof.
    use make_functor.
    - exact (functor_composite_data (linear_category_to_unital_magmoid M) um_yoneda_thunkable).
    - abstract (use make_is_functor;
                [ intro a; apply (notfunctor_id um_yoneda_thunkable)
                | intros a b c f g; cbn in g;
                  apply subtypePath'; [|apply isaprop_is_nat_trans, homset_property];
                  apply um_yoneda_functor_comp_linear, g ]).
  Defined.

  (** The first yoneda map [[Mᵒᵖ, HSET]⟦um_yoneda a, F⟧ -> F a] *)
  Definition um_yoneda_map_1 {a : M} {F : functor_data Mᵒᵖ HSET}
    : nat_trans_data (um_yoneda_objects a) F -> (F a : hSet).
  Proof. intro α; exact (α a (identity a)). Defined.

  (** The second yoneda map [F a -> [Mᵒᵖ, HSET]⟦um_yoneda a, F⟧] *)
  Definition um_yoneda_map_2 {a : M} {F : functor_data Mᵒᵖ HSET}
    : (F a : hSet) -> nat_trans_data (um_yoneda_objects a) F.
  Proof.
    intros x b f.
    exact (#F f x).
  Defined.

  (** Though not natural in general, the second Yoneda map is natural when F is a functor
      (in particular, [um_yoneda_ob] when restricted to thunkable maps) *)

  (** [um_yoneda_map_2] is always yoneda natural *)
  Definition is_yoneda_natural_um_yoneda_map_2 {a : M} {F : functor_data Mᵒᵖ HSET}
    (HF : functor_idax F) (x : (F a : hSet)) : is_yoneda_natural (um_yoneda_map_2 (F:=F) x).
  Proof.
    intros b f.
    unfold is_locally_yoneda_natural, um_yoneda_map_2.
    apply maponpaths, pathsinv0, (eqtohomot (HF a)).
  Qed.

  (** [um_yoneda_map_2] is fully natural whenever F is functorial *)
  Definition is_nat_trans_um_yoneda_map_2 {a : M} {F : functor_data Mᵒᵖ HSET}
    (HF : functor_compax F) (x : (F a : hSet)) : is_nat_trans _ _ (um_yoneda_map_2 (F:=F) x).
  Proof.
    intros b c f.
    apply funextsec; intro g.
    cbn in *.
    change (# F (f · g) x = # F f (# F g x)).
    exact (eqtohomot (HF _ _ _ g f) x).
  Qed.

  Definition um_yoneda_map_2_functorial {a : M} {F : functor_data Mᵒᵖ HSET}
    (HF : functor_compax F) (x : (F a : hSet))
    : um_yoneda_objects a ⟹ F
    := make_nat_trans _ _ _ (is_nat_trans_um_yoneda_map_2 HF x).

  (** [um_yoneda_map_1] inverts [um_yoneda_map_2] if F preserves identities *)
  Lemma um_yoneda_map_2_1 {a : M} {F : functor_data Mᵒᵖ HSET}
    (HF : functor_idax F) (x : (F a : hSet)) :
    um_yoneda_map_1 (um_yoneda_map_2 x) = x.
  Proof.
    unfold um_yoneda_map_1, um_yoneda_map_2; cbn in *.
    exact (eqtohomot (HF a) x).
  Qed.

  (** [um_yoneda_map_2] inverts [um_yoneda_map_1] wherever α [is_locally_yoneda_natural]
      at [f]. *)
  Lemma um_yoneda_map_1_2_locally_yoneda_natural {a : M} {F : functor_data Mᵒᵖ HSET}
    (α : nat_trans_data (um_yoneda_objects a) F)
    (b : M) (f : b --> a) (Hα : is_locally_yoneda_natural α f) :
    um_yoneda_map_2 (um_yoneda_map_1 α) b f = α b f.
  Proof.
    unfold um_yoneda_map_1, um_yoneda_map_2; cbn in *.
    apply pathsinv0, Hα.
  Qed.

  (** In particular, this works if α is [locally_natural], or indeed natural everywhere. *)
  Lemma um_yoneda_map_1_2_locally_natural {a : M} {F : functor_data Mᵒᵖ HSET}
    (α : nat_trans_data (um_yoneda_objects a) F)
    (b : M) (f : b --> a) (Hα : is_locally_natural α f) :
    um_yoneda_map_2 (um_yoneda_map_1 α) b f = α b f.
  Proof.
    apply um_yoneda_map_1_2_locally_yoneda_natural.
    etrans.
    - apply maponpaths, pathsinv0, magmoid_id_right.
    - apply (eqtohomot Hα).
  Qed.

  Lemma um_yoneda_map_1_2_yoneda_natural {a : M} {F : functor_data Mᵒᵖ HSET}
    (α : nat_trans_data (um_yoneda_objects a) F)
    (Hα : is_yoneda_natural α) :
    um_yoneda_map_2 (um_yoneda_map_1 α) = α.
  Proof.
    do 2 (apply funextsec; intro).
    apply um_yoneda_map_1_2_locally_yoneda_natural, Hα.
  Qed.

  Lemma um_yoneda_map_1_2_natural {a : M} {F : functor_data Mᵒᵖ HSET}
    (α : nat_trans_data (um_yoneda_objects a) F)
    (Hα : is_nat_trans (um_yoneda_objects a) F α) :
    um_yoneda_map_2 (um_yoneda_map_1 α) = α.
  Proof.
    do 2 (apply funextsec; intro).
    apply um_yoneda_map_1_2_locally_natural.
    apply Hα.
  Qed.

  (** [yoneda_map_2] is a weak equivalence [F a ≃ (um_yoneda a ⟹ F)] when F is a [functor] *)
  Lemma isweq_um_yoneda_map_2_functorial {a : M} {F : functor Mᵒᵖ HSET}
    : isweq (λ (x : (F a : hSet)), um_yoneda_map_2_functorial (pr22 F) x).
  Proof.
    use isweq_iso.
    - intro α; exact (um_yoneda_map_1 α).
    - abstract (intro x; cbn; apply (eqtohomot (functor_id F a))).
    - abstract (intro α;
                apply subtypePath'; [|apply isaprop_is_nat_trans, homset_property];
                apply um_yoneda_map_1_2_natural, α).
  Defined.

  (** In fact, [yoneda_map_2] is a weak equivalence [F a ≃ (yoneda_nat_trans (um_yoneda a) F)]
      for all [notfunctor]s *)
  Lemma isweq_um_yoneda_map_2_yoneda_natural {a : M} {F : notfunctor Mᵒᵖ HSET}
    : isweq (λ (x : (F a : hSet)),
          make_yoneda_nat_trans
            (um_yoneda_map_2 x)
            (is_yoneda_natural_um_yoneda_map_2 (notfunctor_id F) x)).
  Proof.
    use isweq_iso.
    - intro α; exact (um_yoneda_map_1 α).
    - abstract (intro x; cbn; apply (eqtohomot (notfunctor_id F a))).
    - abstract (intro α;
                apply subtypePath'; [|apply isaprop_is_yoneda_natural];
                apply um_yoneda_map_1_2_yoneda_natural, α).
  Defined.

  (** [yoneda_map_1] is surjective for F a [notfunctor] *)
  Lemma issurjective_um_yoneda_map_1 {a : M} {F : notfunctor Mᵒᵖ HSET}
    : issurjective (λ (α : nat_trans_data (um_yoneda_objects a) F), um_yoneda_map_1 α).
  Proof.
    intro α.
    apply hinhpr; exists (um_yoneda_map_2 α).
    abstract (apply um_yoneda_map_2_1, F).
  Defined.

  (** Likewise, [yoneda_map_2] is injective for F a [notfunctor] *)
  Lemma isincl_um_yoneda_map_2 {a : M} {F : notfunctor Mᵒᵖ HSET}
    : isincl (λ (x : (F a : hSet)), um_yoneda_map_2 x).
  Proof.
    apply isinclbetweensets.
    - apply setproperty.
    - apply impred_isaset; intro; apply homset_property.
    - intros x x' H.
      apply (maponpaths um_yoneda_map_1) in H.
      refine (!_ @ H @ _); apply (um_yoneda_map_2_1 (notfunctor_id F)).
  Qed.

  (** [um_yoneda] is [faithful] in general *)
  Lemma faithful_um_yoneda (a b : M)
    : isincl (λ (f : a --> b), #um_yoneda f).
  Proof.
    apply isinclbetweensets.
    1, 2: apply unital_magmoid_has_homsets.
    intros f g H.
    apply (maponpaths um_yoneda_map_1) in H.
    change (identity a · f = identity a · g) in H.
    refine (!_ @ H @ _); apply magmoid_id_left.
  Qed.

  (** [um_yoneda] is [full] in the subcategory with yoneda-natural morphisms *)
  Lemma full_um_yoneda (a b : M)
    : issurjective (λ (f : a --> b),
          make_yoneda_nat_trans
            (#um_yoneda f)
            (is_yoneda_natural_um_yoneda_morphism f)).
  Proof.
    intro α.
    apply hinhpr.
    induction α as [α Hα].
    exists (um_yoneda_map_1 α).
    apply subtypePath'; [|apply isaprop_is_yoneda_natural].
    apply funextsec; intro c.
    apply funextsec; intro f.
    apply pathsinv0, Hα.
  Qed.

  (** [um_yoneda] preserves isomorphisms *)
  Definition um_yoneda_on_lt_iso {a b : M} (f : lt_iso a b)
    : is_z_isomorphism (#um_yoneda f).
  Proof.
    use make_is_z_isomorphism.
    - apply (#um_yoneda (lt_iso_inv f)).
    - abstract (split; do 2 (apply funextsec; intro);
                [ apply lt_iso_right
                | apply lt_iso_inverse_right ]).
  Defined.

End yoneda.

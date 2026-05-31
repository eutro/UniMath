(********************************************************************************

 Yoneda Lemma for Unital Magmoids

 Author: B. Szilvasy
 January 2026

 Yoneda's lemma fails at almost every step for unital magmoids.  We find one
 weakening useful: the Yoneda functor (suitably weakened) is functorial when
 restricted to linear morphisms and fully-faithful when also co-restricted to
 natural transformations.

 Contents:
 1. Unital magmoid of [rxfunctor]s and unnatural transformations
 2. Category of (category-valued) [rxfunctor]s and natural transformations
 3. Weakened Yoneda's lemma
 3.1. Object part
 3.2. Morphism part
 3.3. Full [rxfunctor]
 3.4. The not-quite isomorphism [[Mᵒᵖ, HSET]⟦um_yoneda a, F⟧ ≃ F a]
 3.5. Fully-faithful Yoneda functor on linear morphisms

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
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Functors.

Local Open Scope cat.
Local Open Scope unital_magmoid.

(** ** 1. Unital magmoid of [rxfunctor]s and unnatural transformations *)
Section rxfunctor_magmoid.

  Definition rxfunctor_magmoid_ob_mor (M M' : unital_premagmoid_data) : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (rxfunctor M M').
    - intros F G; exact (nat_trans_data F G).
  Defined.

  Definition rxfunctor_magmoid_data (M M' : unital_premagmoid_data) : unital_premagmoid_data.
  Proof.
    use (make_precategory_data (rxfunctor_magmoid_ob_mor M M')).
    - intros F a; apply identity.
    - intros F G H α β a;
        apply (α a · β a).
  Defined.

  Definition rxfunctor_magmoid_is_unital (M : unital_premagmoid_data) (M' : unital_premagmoid)
    : is_unital_premagmoid (rxfunctor_magmoid_data M M').
  Proof.
    split; intros F G α;
      apply funextsec; intro a.
    - apply magmoid_id_left.
    - apply magmoid_id_right.
  Defined.

  Definition rxfunctor_magmoid_is_assoc (M : unital_premagmoid_data) (M' : precategory)
    : is_assoc_premagmoid (rxfunctor_magmoid_data M M').
  Proof.
    split; intros F G H K α β δ;
      apply funextsec; intro a.
    - apply assoc.
    - apply assoc'.
  Defined.

  Definition rxfunctor_unital_premagmoid (M : unital_premagmoid_data) (M' : unital_premagmoid)
    : unital_premagmoid
    := make_unital_premagmoid _ (rxfunctor_magmoid_is_unital M M').

  Definition has_homsets_rxfunctor_unital_premagmoid (M M' : unital_premagmoid_data)
    (hs : has_homsets M')
    : has_homsets (rxfunctor_magmoid_data M M').
  Proof.
    intros F G.
    apply impred_isaset; intro a; apply hs.
  Qed.

  Definition rxfunctor_unital_magmoid (M : unital_premagmoid_data) (M' : unital_magmoid) : unital_magmoid.
  Proof.
    use make_unital_magmoid.
    - exact (rxfunctor_unital_premagmoid M M').
    - abstract (apply has_homsets_rxfunctor_unital_premagmoid, unital_magmoid_has_homsets).
  Defined.

  (** Call α "locally natural" at [f : a --> b] when the naturality square communtes. *)
  Definition is_locally_natural {C D : precategory_data} {F G : functor_data C D} (α : nat_trans_data F G)
    {a b : C} (f : a --> b) : UU
    := # F f · α b = α a · #G f.

End rxfunctor_magmoid.

(** ** 2. Category of (category-valued) [rxfunctor]s and natural transformations

This is the subcategory of [rxfunctor_magmoid] with morphisms natural. *)
Section rxfunctor_magmoid.

  Definition natrxfunctor_magmoid_ob_mor (M M' : unital_premagmoid_data) : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (rxfunctor M M').
    - intros F G; exact (nat_trans F G).
  Defined.

  Definition natrxfunctor_magmoid_data (M : unital_premagmoid_data) (M' : precategory) : unital_premagmoid_data.
  Proof.
    use (make_precategory_data (natrxfunctor_magmoid_ob_mor M M')).
    - intros F.
      cbn in F |- *; red.
      exists (λ a : M, identity (F a)).
      abstract (intros a b f; now rewrite id_right, id_left).
    - intros F G H α β.
      cbn in F, G, H, α, β |- *; red.
      exists (λ a : M, α a · β a).
      abstract (
          intros a b f;
          rewrite assoc, (nat_trans_ax α);
          rewrite assoc', (nat_trans_ax β);
          apply assoc).
  Defined.

  Definition natrxfunctor_magmoid_is_unital (M : unital_premagmoid_data) (M' : category)
    : is_unital_premagmoid (natrxfunctor_magmoid_data M M').
  Proof.
    split; intros F G α; apply (nat_trans_eq M'); intro a.
    - apply id_left.
    - apply id_right.
  Defined.

  Definition natrxfunctor_magmoid_is_assoc (M : unital_premagmoid_data) (M' : category)
    : is_assoc_premagmoid (natrxfunctor_magmoid_data M M').
  Proof.
    split; intros F G H K α β δ; apply (nat_trans_eq M'); intro a.
    - apply assoc.
    - apply assoc'.
  Defined.

  Definition natrxfunctor_precategory (M : unital_premagmoid_data) (M' : category)
    : precategory
    := make_precategory (natrxfunctor_magmoid_data M M')
         (make_dirprod
            (natrxfunctor_magmoid_is_unital M M')
            (natrxfunctor_magmoid_is_assoc M M')).

  Definition has_homsets_natrxfunctor_precategory (M : unital_premagmoid_data) (M' : category)
    : has_homsets (natrxfunctor_magmoid_data M M').
  Proof.
    intros F G.
    apply isaset_nat_trans, M'.
  Qed.

  Definition natrxfunctor_category (M : unital_premagmoid_data) (M' : category) : category
    := make_category (natrxfunctor_precategory M M') (has_homsets_natrxfunctor_precategory M M').

  Lemma natrxfunctor_is_nat_iso_iff_is_z_isomorphism (M : unital_premagmoid_data) (M' : category)
    (F G : natrxfunctor_category M M') (α : F --> G)
    : is_z_isomorphism α <-> is_nat_z_iso (α : nat_trans _ _).
  Proof.
    split.
    - intros αinv a.
      exists ((is_z_isomorphism_mor αinv : nat_trans _ _) a).
      abstract (
          split;
          [ exact (eqtohomot (base_paths _ _ (is_inverse_in_precat1 αinv)) a)
          | exact (eqtohomot (base_paths _ _ (is_inverse_in_precat2 αinv)) a) ]).
    - intros αinv.
      use tpair. {
        exists (λ a, is_z_isomorphism_mor (αinv a)).
        abstract (
            intros a b f;
            apply pathsinv0, (z_iso_inv_on_right (C:=M') _ _ _ (_,,αinv a));
            rewrite assoc;
            apply (z_iso_inv_on_left (C:=M') _ _ _ _ (_,,αinv b)), pathsinv0;
            apply (nat_trans_ax α)).
      }
      abstract (
          split; apply (nat_trans_eq M'); intro a;
          [ exact (is_inverse_in_precat1 (αinv a))
          | exact (is_inverse_in_precat2 (αinv a)) ]).
  Defined.

  Lemma natrxfunctor_category_z_iso_weq_nat_z_iso (M : unital_premagmoid_data) (M' : category)
  (F G : natrxfunctor_category M M')
    : z_iso F G ≃ (∑ α : F --> G, is_nat_z_iso (α : nat_trans _ _)).
  Proof.
    use weqbandf; [apply idweq|].
    intro α; apply weqiff.
    - apply natrxfunctor_is_nat_iso_iff_is_z_isomorphism.
    - abstract (apply isaprop_is_z_isomorphism).
    - abstract (apply impred; intro; apply isaprop_is_z_isomorphism).
  Defined.

End rxfunctor_magmoid.

(** ** 3. Weakened Yoneda's lemma *)
Section yoneda.
  Context [M : unital_magmoid].

  Notation Mᵒᵖ := (opp_precat_data M).
  Notation Mₜᵒᵖ := (opp_precat_data (M ₜ)).

  (** *** 3.1. Object part *)

  (* [um_yoneda_ob a] is the postcomposition [rxfunctor]: [M⟦a, -⟧]. *)
  Definition um_yoneda_objects_ob (a b : M) : hSet
    := make_hSet (M⟦b, a⟧) (unital_magmoid_has_homsets M b a).

  Definition um_yoneda_objects_mor (a : M) {b b' : M} (f : b --> b')
    : um_yoneda_objects_ob a b' -> um_yoneda_objects_ob a b
    := λ g, f · g.
  Arguments um_yoneda_objects_mor _ {_ _} _ / _.

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

  Definition um_yoneda_ob (a : M) : rxfunctor Mᵒᵖ HSET
    := make_rxfunctor _ (um_yoneda_objects_id a).

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

  (** *** 3.2. Morphism part *)

  (** [um_yoneda_morphisms f] is the precomposition unnatural transformation [M⟦f, -⟧] *)
  Definition um_yoneda_morphisms {a a' : M} (f : a --> a')
    : nat_trans_data (um_yoneda_objects a) (um_yoneda_objects a')
    := λ b g, g · f.
  Arguments um_yoneda_morphisms {_ _} _ _ / _.

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

  Definition yoneda_nat_trans (a : M) (F : rxfunctor Mᵒᵖ HSET) : UU
    := ∑ (α : nat_trans_data (um_yoneda_objects a) F), is_yoneda_natural α.
  Definition make_yoneda_nat_trans {a : M} {F : rxfunctor Mᵒᵖ HSET}
    (α : nat_trans_data (um_yoneda_objects a) F)
    (H : is_yoneda_natural α) : yoneda_nat_trans a F
    := α,,H.
  Coercion yoneda_nat_trans_to_nat_trans_data {a : M} {F : rxfunctor Mᵒᵖ HSET}
    (α : yoneda_nat_trans a F) : nat_trans_data (um_yoneda_objects a) F := pr1 α.
  Coercion yoneda_nat_trans_is_yoneda_natural {a : M} {F : rxfunctor Mᵒᵖ HSET}
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

  (** *** Full [rxfunctor] *)

  (** [um_yoneda] is the [rxfunctor] M ⟶ [Mᵒᵖ, HSET] mapping objects to their not-quite-functor *)
  Definition um_yoneda_functor_data
    : functor_data M (rxfunctor_unital_magmoid Mᵒᵖ HSET).
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
    : rxfunctor M (rxfunctor_unital_magmoid Mᵒᵖ HSET)
    := make_rxfunctor _ um_yoneda_functor_id.

  (** [um_yoneda] restricted to linear maps: a functor *)
  Lemma um_yoneda_linear : functor (M ₗ) (natrxfunctor_category Mᵒᵖ HSET).
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro a; exact (um_yoneda_ob a).
      + intros a b f; exact (um_yoneda_morphisms_linear f).
    - abstract (use make_is_functor;
                [ intro a; apply (nat_trans_eq HSET), eqtohomot, um_yoneda_functor_id
                | intros a b c f g; cbn in g;
                  apply (nat_trans_eq HSET), eqtohomot,
                    um_yoneda_functor_comp_linear, g ]).
  Defined.

  (** [um_yoneda] restricted to thunkable maps in the second argument: the codomain is functors *)
  Lemma um_yoneda_thunkable : rxfunctor M [Mₜᵒᵖ, HSET].
  Proof.
    use make_rxfunctor.
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
                [ intro a; apply (rxfunctor_id um_yoneda_thunkable)
                | intros a b c f g; cbn in g;
                  apply subtypePath'; [|apply isaprop_is_nat_trans, homset_property];
                  apply um_yoneda_functor_comp_linear, g ]).
  Defined.

  (** *** 3.4. The not-quite isomorphism [[Mᵒᵖ, HSET]⟦um_yoneda a, F⟧ ≃ F a] *)

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
      for all [rxfunctor]s *)
  Lemma isweq_um_yoneda_map_2_yoneda_natural {a : M} {F : rxfunctor Mᵒᵖ HSET}
    : isweq (λ (x : (F a : hSet)),
          make_yoneda_nat_trans
            (um_yoneda_map_2 x)
            (is_yoneda_natural_um_yoneda_map_2 (rxfunctor_id F) x)).
  Proof.
    use isweq_iso.
    - intro α; exact (um_yoneda_map_1 α).
    - abstract (intro x; cbn; apply (eqtohomot (rxfunctor_id F a))).
    - abstract (intro α;
                apply subtypePath'; [|apply isaprop_is_yoneda_natural];
                apply um_yoneda_map_1_2_yoneda_natural, α).
  Defined.

  (** [yoneda_map_1] is surjective for F a [rxfunctor] *)
  Lemma issurjective_um_yoneda_map_1 {a : M} {F : rxfunctor Mᵒᵖ HSET}
    : issurjective (λ (α : nat_trans_data (um_yoneda_objects a) F), um_yoneda_map_1 α).
  Proof.
    intro α.
    apply hinhpr; exists (um_yoneda_map_2 α).
    abstract (apply um_yoneda_map_2_1, F).
  Defined.

  (** Likewise, [yoneda_map_2] is injective for F a [rxfunctor] *)
  Lemma isincl_um_yoneda_map_2 {a : M} {F : rxfunctor Mᵒᵖ HSET}
    : isincl (λ (x : (F a : hSet)), um_yoneda_map_2 x).
  Proof.
    apply isinclbetweensets.
    - apply setproperty.
    - apply impred_isaset; intro; apply homset_property.
    - intros x x' H.
      apply (maponpaths um_yoneda_map_1) in H.
      refine (!_ @ H @ _); apply (um_yoneda_map_2_1 (rxfunctor_id F)).
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
  Defined.

  Corollary isweq_um_yoneda_to_yoneda_natural (a b : M)
    : isweq (λ (f : a --> b),
        make_yoneda_nat_trans
            (#um_yoneda f)
            (is_yoneda_natural_um_yoneda_morphism f)).
  Proof.
    use isweqinclandsurj.
    - use (isincltwooutof3a _ pr1).
      + use isinclpr1.
        intro; use isaprop_is_yoneda_natural.
      + use faithful_um_yoneda.
    - use full_um_yoneda.
  Defined.

  (** *** 3.5. Fully-faithful Yoneda functor on linear morphisms *)

  (** [um_yoneda] preserves linear-and-thunkable isomorphisms *)
  Theorem um_yoneda_on_lt_iso {a b : M} (f : lt_iso a b)
    : is_z_isomorphism (#um_yoneda f).
  Proof.
    use make_is_z_isomorphism.
    - apply (#um_yoneda (lt_iso_inv f)).
    - abstract (split; do 2 (apply funextsec; intro);
                [ apply lt_iso_right
                | apply lt_iso_inverse_right ]).
  Defined.

  (** [um_yoneda_map_1] is linear if the transformation is natural *)
  Theorem is_linear_um_yoneda_map_1_from_is_nat_trans {a b : M}
    (α : um_yoneda a --> um_yoneda b)
    (Hα : is_nat_trans _ _ α)
    : is_linear (um_yoneda_map_1 α).
  Proof.
    intros c d g h.
    unfold um_yoneda_map_1.
    etrans; [apply pathsinv0, (eqtohomot (Hα _ _ _) _)|]; cbn.
    etrans; [|apply cancel_precomposition, (eqtohomot (Hα _ _ _) _)]; cbn.
    etrans; [|apply (eqtohomot (Hα _ _ _) _)]; cbn.
    apply maponpaths.
    now rewrite !magmoid_id_right.
  Qed.

  Theorem um_yoneda_linear_fully_faithful : fully_faithful um_yoneda_linear.
  Proof.
    intros a b.
    use isweq_iso.
    - intro α; cbn in α.
      exact (make_linear_mor _ (is_linear_um_yoneda_map_1_from_is_nat_trans α (nat_trans_ax α))).
    - abstract (
          intro f; apply carrier_eq; cbn;
          apply magmoid_id_left).
    - abstract (
          cbn; intro α;
          apply (nat_trans_eq HSET), eqtohomot,
            (um_yoneda_map_1_2_natural α (nat_trans_ax α))).
  Defined.

  Definition weq_um_yoneda_linear (a b : M)
    : linear_mor a b ≃ nat_trans (um_yoneda a : _ ⟶¹ _) (um_yoneda b : _ ⟶¹ _)
    := weq_from_fully_faithful um_yoneda_linear_fully_faithful a b.

  (** [um_yoneda] reflects natural isomorphisms into linear isomorphisms *)
  Definition um_yoneda_on_linear_iso {a b : M}
    (f : z_iso (C:=linear_category M) a b)
    : is_z_isomorphism (#um_yoneda_linear (z_iso_mor f))
    := functor_on_is_z_isomorphism _ (z_iso_is_z_isomorphism f).

  Definition um_yoneda_reflects_iso {a b : M}
    (α : z_iso (um_yoneda_linear a) (um_yoneda_linear b))
    : z_iso (C:=linear_category M) a b
    := make_z_iso' _ (fully_faithful_reflects_iso_proof _ _ _
         um_yoneda_linear_fully_faithful _ _ α).

  (** A linear isomorphism [a ≅ₗ b] is equivalently a natural isomorphism [M⟦-, a⟧ ≅ M⟦-, b⟧]. *)
  Definition weq_um_yoneda_linear_isos {a b : M}
    : z_iso (C:=linear_category M) a b
        ≃ z_iso (um_yoneda_linear a) (um_yoneda_linear b).
  Proof.
    use weq_iso.
    - intro f; exact (make_z_iso' _ (um_yoneda_on_linear_iso f)).
    - intros α; exact (um_yoneda_reflects_iso α).
    - abstract (intro f; apply z_iso_eq, carrier_eq, magmoid_id_left).
    - abstract (intro α; apply z_iso_eq, (nat_trans_eq HSET), eqtohomot,
                  (um_yoneda_map_1_2_natural _ (nat_trans_ax (z_iso_mor α)))).
  Defined.

End yoneda.

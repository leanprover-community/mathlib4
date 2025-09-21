/-
Copyright (c) 2024 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Covers of schemes

This file provides the basic API for covers of schemes. A cover of a scheme `X` with respect to
a morphism property `P` is a jointly surjective indexed family of scheme morphisms with
target `X` all satisfying `P`.

## Implementation details

The definition on the pullback of a cover along a morphism depends on results that
are developed later in the import tree. Hence in this file, they have additional assumptions
that will be automatically satisfied in later files. The motivation here is that we already
know that these assumptions are satisfied for open immersions and hence the cover API for open
immersions can be used to deduce these assumptions in the general case.

-/


noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

universe v v₁ v₂ u

namespace AlgebraicGeometry

namespace Scheme

-- TODO: provide API to and from a presieve.
/-- A cover of `X` consists of jointly surjective indexed family of scheme morphisms
with target `X` all satisfying `P`.

This is merely a coverage in the pretopology defined by `P`, and it would be optimal
if we could reuse the existing API about pretopologies, However, the definitions of sieves and
Grothendieck topologies uses `Prop`s, so that the actual open sets and immersions are hard to
obtain. Also, since such a coverage in the pretopology usually contains a proper class of
immersions, it is quite hard to glue them, reason about finite covers, etc.

Note: The `map_prop` field is equipped with a default argument `by infer_instance`. In general
this causes worse error messages, but in practice `P` is mostly defined via `class`.
-/
structure Cover (P : MorphismProperty Scheme.{u}) (S : Scheme.{u}) where
  /-- index set of a cover of a scheme `X` -/
  I₀ : Type v
  /-- the components of a cover -/
  X (j : I₀) : Scheme
  /-- the components map to `X` -/
  f (j : I₀) : X j ⟶ S
  /-- given a point of `x : X`, `idx x` is the index of the component which contains `x` -/
  idx (x : S) : I₀
  /-- the components cover `X` -/
  covers (x : S) : x ∈ Set.range (f (idx x)).base
  /-- the component maps satisfy `P` -/
  map_prop (j : I₀) : P (f j) := by infer_instance

@[deprecated (since := "2025-09-19")]
alias Cover.J := Cover.I₀

@[deprecated (since := "2025-09-19")]
alias Cover.obj := Cover.X

@[deprecated (since := "2025-09-19")]
alias Cover.map := Cover.f

variable {P : MorphismProperty Scheme.{u}}

variable {X Y Z : Scheme.{u}} (𝒰 : X.Cover P) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ x, HasPullback (𝒰.f x ≫ f) g]

theorem Cover.iUnion_range {X : Scheme.{u}} (𝒰 : X.Cover P) :
    ⋃ i, Set.range (𝒰.f i).base = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  exact ⟨𝒰.idx x, 𝒰.covers x⟩

lemma Cover.exists_eq (𝒰 : X.Cover P) (x : X) : ∃ i y, (𝒰.f i).base y = x :=
  ⟨_, 𝒰.covers x⟩

instance Cover.nonempty_of_nonempty [Nonempty X] (𝒰 : X.Cover P) : Nonempty 𝒰.I₀ :=
  Nonempty.map 𝒰.idx ‹_›

/-- Given a family of schemes with morphisms to `X` satisfying `P` that jointly
cover `X`, `Cover.mkOfCovers` is an associated `P`-cover of `X`. -/
@[simps]
def Cover.mkOfCovers (J : Type*) (obj : J → Scheme.{u}) (map : (j : J) → obj j ⟶ X)
    (covers : ∀ x, ∃ j y, (map j).base y = x)
    (map_prop : ∀ j, P (map j) := by infer_instance) : X.Cover P where
  I₀ := J
  X := obj
  f := map
  idx x := (covers x).choose
  covers x := (covers x).choose_spec
  map_prop := map_prop

/-- Turn a `P`-cover into a `Q`-cover by showing that the components satisfy `Q`. -/
def Cover.changeProp (Q : MorphismProperty Scheme.{u}) (𝒰 : X.Cover P) (h : ∀ j, Q (𝒰.f j)) :
    X.Cover Q where
  I₀ := 𝒰.I₀
  X := 𝒰.X
  f := 𝒰.f
  idx := 𝒰.idx
  covers := 𝒰.covers
  map_prop := h

/-- Given a `P`-cover `{ Uᵢ }` of `X`, and for each `Uᵢ` a `P`-cover, we may combine these
covers to form a `P`-cover of `X`. -/
@[simps! I₀ X f]
def Cover.bind [P.IsStableUnderComposition] (g : ∀ x : 𝒰.I₀, (𝒰.X x).Cover P) : X.Cover P where
  I₀ := Σ i : 𝒰.I₀, (g i).I₀
  X x := (g x.1).X x.2
  f x := (g x.1).f x.2 ≫ 𝒰.f x.1
  idx x := ⟨_, (g _).idx (𝒰.covers x).choose⟩
  covers x := by
    let y := (𝒰.covers x).choose
    have hy : (𝒰.f (𝒰.idx x)).base y = x := (𝒰.covers x).choose_spec
    rcases (g (𝒰.idx x)).covers y with ⟨z, hz⟩
    change x ∈ Set.range ((g (𝒰.idx x)).f ((g (𝒰.idx x)).idx y) ≫ 𝒰.f (𝒰.idx x)).base
    use z
    simp only [comp_coeBase, TopCat.hom_comp, ContinuousMap.comp_apply]
    rw [hz, hy]
  map_prop _ := P.comp_mem _ _ ((g _).map_prop _) (𝒰.map_prop _)

/-- An isomorphism `X ⟶ Y` is a `P`-cover of `Y`. -/
@[simps I₀ X f]
def coverOfIsIso [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] : Cover.{v} P Y where
  I₀ := PUnit.{v + 1}
  X _ := X
  f _ := f
  idx _ := PUnit.unit
  covers x := by
    rw [Set.range_eq_univ.mpr]
    all_goals try trivial
    rw [← TopCat.epi_iff_surjective]
    infer_instance
  map_prop _ := P.of_isIso _

/-- We construct a cover from another, by providing the needed fields and showing that the
provided fields are isomorphic with the original cover. -/
@[simps I₀ X f]
def Cover.copy [P.RespectsIso] {X : Scheme.{u}} (𝒰 : X.Cover P)
    (J : Type*) (obj : J → Scheme)
    (map : ∀ i, obj i ⟶ X) (e₁ : J ≃ 𝒰.I₀) (e₂ : ∀ i, obj i ≅ 𝒰.X (e₁ i))
    (h : ∀ i, map i = (e₂ i).hom ≫ 𝒰.f (e₁ i)) : X.Cover P :=
  { I₀ := J, X := obj, f := map
    idx := fun x ↦ e₁.symm (𝒰.idx x)
    covers := fun x ↦ by
      rw [h, Scheme.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr,
        Set.image_univ, e₁.rightInverse_symm]
      · exact 𝒰.covers x
      · rw [← TopCat.epi_iff_surjective]; infer_instance
    map_prop := fun j ↦ by
      rw [h, P.cancel_left_of_respectsIso]
      exact 𝒰.map_prop (e₁ j) }

/-- The pushforward of a cover along an isomorphism. -/
@[simps! I₀ X f]
def Cover.pushforwardIso [P.RespectsIso] [P.ContainsIdentities] [P.IsStableUnderComposition]
    {X Y : Scheme.{u}} (𝒰 : Cover.{v} P X) (f : X ⟶ Y) [IsIso f] :
    Cover.{v} P Y :=
  ((coverOfIsIso.{v, u} f).bind fun _ => 𝒰).copy 𝒰.I₀ _ _
    ((Equiv.punitProd _).symm.trans (Equiv.sigmaEquivProd PUnit 𝒰.I₀).symm) (fun _ => Iso.refl _)
    fun _ => (Category.id_comp _).symm

/-- Adding map satisfying `P` into a cover gives another cover. -/
@[simps]
def Cover.add {X Y : Scheme.{u}} (𝒰 : X.Cover P) (f : Y ⟶ X) (hf : P f := by infer_instance) :
    X.Cover P where
  I₀ := Option 𝒰.I₀
  X i := Option.rec Y 𝒰.X i
  f i := Option.rec f 𝒰.f i
  idx x := some (𝒰.idx x)
  covers := 𝒰.covers
  map_prop j := by
    obtain ⟨_ | _⟩ := j
    · exact hf
    · exact 𝒰.map_prop _

/-- A morphism property of schemes is said to preserve joint surjectivity, if
for any pair of morphisms `f : X ⟶ S` and `g : Y ⟶ S` where `g` satisfies `P`,
any pair of points `x : X` and `y : Y` with `f x = g y` can be lifted to a point
of `X ×[S] Y`.

In later files, this will be automatic, since this holds for any morphism `g`
(see `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`). But at
this early stage in the import tree, we only know it for open immersions. -/
class IsJointlySurjectivePreserving (P : MorphismProperty Scheme.{u}) where
  exists_preimage_fst_triplet_of_prop {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hg : P g) (x : X) (y : Y) (h : f.base x = g.base y) :
    ∃ a : ↑(pullback f g), (pullback.fst f g).base a = x

lemma IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
    [IsJointlySurjectivePreserving P] {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : P f) (x : X) (y : Y) (h : f.base x = g.base y) :
    ∃ a : ↑(pullback f g), (pullback.snd f g).base a = y := by
  let iso := pullbackSymmetry f g
  haveI : HasPullback g f := hasPullback_symmetry f g
  obtain ⟨a, ha⟩ := exists_preimage_fst_triplet_of_prop hf y x h.symm
  use (pullbackSymmetry f g).inv.base a
  rwa [← Scheme.comp_base_apply, pullbackSymmetry_inv_comp_snd]

instance : IsJointlySurjectivePreserving @IsOpenImmersion where
  exists_preimage_fst_triplet_of_prop {X Y S f g} _ hg x y h := by
    rw [← show _ = (pullback.fst _ _ : pullback f g ⟶ _).base from
        PreservesPullback.iso_hom_fst Scheme.forgetToTop f g]
    have : x ∈ Set.range (pullback.fst f.base g.base) := by
      rw [TopCat.pullback_fst_range f.base g.base]
      use y
    obtain ⟨a, ha⟩ := this
    use (PreservesPullback.iso forgetToTop f g).inv a
    rwa [← TopCat.comp_app, Iso.inv_hom_id_assoc]

/-- Given a cover on `X`, we may pull them back along a morphism `W ⟶ X` to obtain
a cover of `W`.

Note that this requires the (unnecessary) assumptions that the pullback exists and that `P`
preserves joint surjectivity. This is needed, because we don't know these in general at this
stage of the import tree, but this API is used in the case of `P = IsOpenImmersion` to
obtain these results in the general case. -/
@[simps]
def Cover.pullbackCover [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
    {X W : Scheme.{u}} (𝒰 : X.Cover P) (f : W ⟶ X) [∀ x, HasPullback f (𝒰.f x)] : W.Cover P where
  I₀ := 𝒰.I₀
  X x := pullback f (𝒰.f x)
  f _ := pullback.fst _ _
  idx x := 𝒰.idx (f.base x)
  covers x := by
    obtain ⟨y, hy⟩ := 𝒰.covers (f.base x)
    exact IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
      (𝒰.map_prop _) x y hy.symm
  map_prop j := P.pullback_fst _ _ (𝒰.map_prop j)

/-- The family of morphisms from the pullback cover to the original cover. -/
def Cover.pullbackHom [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
    {X W : Scheme.{u}} (𝒰 : X.Cover P)
    (f : W ⟶ X) (i) [∀ x, HasPullback f (𝒰.f x)] :
    (𝒰.pullbackCover f).X i ⟶ 𝒰.X i :=
  pullback.snd f (𝒰.f i)

@[reassoc (attr := simp)]
lemma Cover.pullbackHom_map [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
    {X W : Scheme.{u}} (𝒰 : X.Cover P) (f : W ⟶ X) [∀ (x : 𝒰.I₀), HasPullback f (𝒰.f x)] (i) :
    𝒰.pullbackHom f i ≫ 𝒰.f i = (𝒰.pullbackCover f).f i ≫ f := pullback.condition.symm

/-- Given a cover on `X`, we may pull them back along a morphism `f : W ⟶ X` to obtain
a cover of `W`. This is similar to `Scheme.Cover.pullbackCover`, but here we
take `pullback (𝒰.f x) f` instead of `pullback f (𝒰.f x)`. -/
@[simps]
def Cover.pullbackCover' [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
    {X W : Scheme.{u}} (𝒰 : X.Cover P) (f : W ⟶ X)
    [∀ x, HasPullback (𝒰.f x) f] :
    W.Cover P where
  I₀ := 𝒰.I₀
  X x := pullback (𝒰.f x) f
  f _ := pullback.snd _ _
  idx x := 𝒰.idx (f.base x)
  covers x := by
    obtain ⟨y, hy⟩ := 𝒰.covers (f.base x)
    exact IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
      (𝒰.map_prop _) y x hy
  map_prop j := P.pullback_snd _ _ (𝒰.map_prop j)

/-- Given covers `{ Uᵢ }` and `{ Uⱼ }`, we may form the cover `{ Uᵢ ×[X] Uⱼ }`. -/
def Cover.inter [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    [IsJointlySurjectivePreserving P]
    {X : Scheme.{u}} (𝒰₁ : Scheme.Cover.{v₁} P X)
    (𝒰₂ : Scheme.Cover.{v₂} P X)
    [∀ (i : 𝒰₁.I₀) (j : 𝒰₂.I₀), HasPullback (𝒰₁.f i) (𝒰₂.f j)] : X.Cover P where
  I₀ := 𝒰₁.I₀ × 𝒰₂.I₀
  X ij := pullback (𝒰₁.f ij.1) (𝒰₂.f ij.2)
  f ij := pullback.fst _ _ ≫ 𝒰₁.f ij.1
  idx x := ⟨𝒰₁.idx x, 𝒰₂.idx x⟩
  covers x := by
    simp only [comp_coeBase, TopCat.coe_comp, Set.mem_range, Function.comp_apply]
    obtain ⟨y₁, hy₁⟩ := 𝒰₁.covers x
    obtain ⟨y₂, hy₂⟩ := 𝒰₂.covers x
    obtain ⟨z, hz⟩ := IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
      (𝒰₂.map_prop _) y₁ y₂ (by rw [hy₁, hy₂])
    use z
    rw [hz, hy₁]
  map_prop ij := P.comp_mem _ _ (P.pullback_fst _ _ (𝒰₂.map_prop ij.2)) (𝒰₁.map_prop ij.1)

/--
An affine cover of `X` consists of a jointly surjective family of maps into `X` from
spectra of rings.

Note: The `map_prop` field is equipped with a default argument `by infer_instance`. In general
this causes worse error messages, but in practice `P` is mostly defined via `class`.
-/
structure AffineCover (P : MorphismProperty Scheme.{u}) (S : Scheme.{u}) where
  /-- index set of an affine cover of a scheme `S` -/
  I₀ : Type v
  /-- the ring associated to a component of an affine cover -/
  X (j : I₀) : CommRingCat.{u}
  /-- the components map to `S` -/
  f (j : I₀) : Spec (X j) ⟶ S
  /-- given a point of `x : S`, `idx x` is the index of the component which contains `x` -/
  idx (x : S) : I₀
  /-- the components cover `S` -/
  covers (x : S) : x ∈ Set.range (f (idx x)).base
  /-- the component maps satisfy `P` -/
  map_prop (j : I₀) : P (f j) := by infer_instance

@[deprecated (since := "2025-09-19")]
alias AffineCover.J := AffineCover.I₀

@[deprecated (since := "2025-09-19")]
alias AffineCover.obj := AffineCover.X

@[deprecated (since := "2025-09-19")]
alias AffineCover.map := AffineCover.f

/-- The cover associated to an affine cover. -/
@[simps]
def AffineCover.cover {S : Scheme.{u}} (𝒰 : S.AffineCover P) : S.Cover P where
  I₀ := 𝒰.I₀
  X j := Spec (𝒰.X j)
  f := 𝒰.f
  idx := 𝒰.idx
  covers := 𝒰.covers
  map_prop := 𝒰.map_prop

/-- Replace the index type of a cover by an equivalent one. -/
@[simps]
def Cover.reindex (𝒰 : Cover.{v} P X) {ι : Type*} (e : ι ≃ 𝒰.I₀) : Cover P X where
  I₀ := ι
  X := 𝒰.X ∘ e
  f i := 𝒰.f (e i)
  idx := e.symm ∘ 𝒰.idx
  covers x := by
    convert 𝒰.covers _
    dsimp only [Function.comp_apply]
    rw [Equiv.apply_symm_apply]
  map_prop i := 𝒰.map_prop _

/-- Any `v`-cover `𝒰` induces a `u`-cover indexed by the points of `X`. -/
@[simps!]
def Cover.ulift (𝒰 : Cover.{v} P X) : Cover.{u} P X where
  I₀ := X
  X x := 𝒰.X (𝒰.idx x)
  f x := 𝒰.f (𝒰.idx x)
  idx := id
  covers := 𝒰.covers
  map_prop _ := 𝒰.map_prop _

section category

/--
A morphism between covers `𝒰 ⟶ 𝒱` indicates that `𝒰` is a refinement of `𝒱`.
Since covers of schemes are indexed, the definition also involves a map on the
indexing types.
-/
@[ext]
structure Cover.Hom {X : Scheme.{u}} (𝒰 𝒱 : Cover.{v} P X) where
  /-- The map on indexing types associated to a morphism of covers. -/
  idx : 𝒰.I₀ → 𝒱.I₀
  /-- The morphism between open subsets associated to a morphism of covers. -/
  app (j : 𝒰.I₀) : 𝒰.X j ⟶ 𝒱.X (idx j)
  app_prop (j : 𝒰.I₀) : P (app j) := by infer_instance
  w (j : 𝒰.I₀) : app j ≫ 𝒱.f _ = 𝒰.f _ := by cat_disch

attribute [reassoc (attr := simp)] Cover.Hom.w

/-- The identity morphism in the category of covers of a scheme. -/
def Cover.Hom.id [P.ContainsIdentities] {X : Scheme.{u}} (𝒰 : Cover.{v} P X) : 𝒰.Hom 𝒰 where
  idx j := j
  app _ := 𝟙 _
  app_prop _ := P.id_mem _

/-- The composition of two morphisms in the category of covers of a scheme. -/
def Cover.Hom.comp [P.IsStableUnderComposition] {X : Scheme.{u}} {𝒰 𝒱 𝒲 : Cover.{v} P X}
    (f : 𝒰.Hom 𝒱) (g : 𝒱.Hom 𝒲) : 𝒰.Hom 𝒲 where
  idx j := g.idx <| f.idx j
  app _ := f.app _ ≫ g.app _
  app_prop _ := P.comp_mem _ _ (f.app_prop _) (g.app_prop _)

instance Cover.category [P.IsMultiplicative] {X : Scheme.{u}} : Category (Cover.{v} P X) where
  Hom 𝒰 𝒱 := 𝒰.Hom 𝒱
  id := Cover.Hom.id
  comp f g := f.comp g

variable [P.IsMultiplicative]

@[simp]
lemma Cover.id_idx_apply {X : Scheme.{u}} (𝒰 : X.Cover P) (j : 𝒰.I₀) :
    (𝟙 𝒰 : 𝒰 ⟶ 𝒰).idx j = j := rfl

@[simp]
lemma Cover.id_app {X : Scheme.{u}} (𝒰 : X.Cover P) (j : 𝒰.I₀) :
    (𝟙 𝒰 : 𝒰 ⟶ 𝒰).app j = 𝟙 _ := rfl

@[simp]
lemma Cover.comp_idx_apply {X : Scheme.{u}} {𝒰 𝒱 𝒲 : X.Cover P}
    (f : 𝒰 ⟶ 𝒱) (g : 𝒱 ⟶ 𝒲) (j : 𝒰.I₀) :
    (f ≫ g).idx j = g.idx (f.idx j) := rfl

@[simp]
lemma Cover.comp_app {X : Scheme.{u}} {𝒰 𝒱 𝒲 : X.Cover P}
    (f : 𝒰 ⟶ 𝒱) (g : 𝒱 ⟶ 𝒲) (j : 𝒰.I₀) :
    (f ≫ g).app j = f.app j ≫ g.app _ := rfl

end category

end Scheme

end AlgebraicGeometry

/-
Copyright (c) 2024 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits

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
set_option backward.defeqAttrib.useBackward true

@[expose] public section


noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

universe v v₁ v₂ u

namespace AlgebraicGeometry

namespace Scheme

variable (K : Precoverage Scheme.{u})

/-- A coverage `K` on `Scheme` is called jointly surjective if every covering family in `K`
is jointly surjective. -/
class JointlySurjective (K : Precoverage Scheme.{u}) : Prop where
  exists_eq {X : Scheme.{u}} (S : Presieve X) (hS : S ∈ K X) (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ x ∈ Set.range g

/-- A cover of `X` in the coverage `K` is a `0`-hypercover for `K`. -/
abbrev Cover (K : Precoverage Scheme.{u}) := Precoverage.ZeroHypercover.{v} K

variable {K}

variable {X Y Z : Scheme.{u}} (𝒰 : X.Cover K) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ x, HasPullback (𝒰.f x ≫ f) g]

lemma Cover.exists_eq [JointlySurjective K] (𝒰 : X.Cover K) (x : X) :
    ∃ i y, 𝒰.f i y = x := by
  obtain ⟨Y, g, ⟨i⟩, y, hy⟩ := JointlySurjective.exists_eq 𝒰.presieve₀ 𝒰.mem₀ x
  use i, y

/-- A choice of an index `i` such that `x` is in the range of `𝒰.f i`. -/
def Cover.idx [JointlySurjective K] (𝒰 : X.Cover K) (x : X) : 𝒰.I₀ :=
  (𝒰.exists_eq x).choose

lemma Cover.covers [JointlySurjective K] (𝒰 : X.Cover K) (x : X) :
    x ∈ Set.range (𝒰.f (𝒰.idx x)) :=
  (𝒰.exists_eq x).choose_spec

theorem Cover.iUnion_range [JointlySurjective K] {X : Scheme.{u}} (𝒰 : X.Cover K) :
    ⋃ i, Set.range (𝒰.f i) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  exact 𝒰.exists_eq x

instance Cover.nonempty_of_nonempty [JointlySurjective K] [Nonempty X] (𝒰 : X.Cover K) :
    Nonempty 𝒰.I₀ := by
  obtain ⟨i, _⟩ := 𝒰.exists_eq ‹Nonempty X›.some
  use i

section MorphismProperty

variable {P Q : MorphismProperty Scheme.{u}}

lemma presieve₀_mem_precoverage_iff (E : PreZeroHypercover X) :
    E.presieve₀ ∈ precoverage P X ↔ (∀ x, ∃ i, x ∈ Set.range (E.f i)) ∧ ∀ i, P (E.f i) := by
  simp

@[grind ←]
lemma Cover.map_prop (𝒰 : X.Cover (precoverage P)) (i : 𝒰.I₀) : P (𝒰.f i) :=
  𝒰.mem₀.2 ⟨i⟩

/-- Given a family of schemes with morphisms to `X` satisfying `P` that jointly
cover `X`, `Cover.mkOfCovers` is an associated `P`-cover of `X`. -/
@[simps!]
def Cover.mkOfCovers (J : Type*) (obj : J → Scheme.{u}) (map : (j : J) → obj j ⟶ X)
    (covers : ∀ x, ∃ j y, map j y = x)
    (map_prop : ∀ j, P (map j) := by infer_instance) : X.Cover (precoverage P) where
  I₀ := J
  X := obj
  f := map
  mem₀ := by
    simp_rw [presieve₀_mem_precoverage_iff, Set.mem_range]
    #adaptation_note /-- This was `grind` before nightly-2026-02-05. -/
    exact ⟨covers, map_prop⟩

/-- An isomorphism `X ⟶ Y` is a `P`-cover of `Y`. -/
@[simps! I₀ X f]
def coverOfIsIso [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] : Cover.{v} (precoverage P) Y :=
  .mkOfCovers PUnit (fun _ ↦ X)
    (fun _ ↦ f)
    (fun x ↦ ⟨⟨⟩, inv f x, by simp [← Hom.comp_apply]⟩)
    (fun _ ↦ P.of_isIso f)

instance : JointlySurjective (precoverage P) where
  exists_eq {X} R := fun ⟨hR, _⟩ x ↦ by
    rw [jointlySurjectivePrecoverage, Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    obtain ⟨Y, g, hg, heq⟩ := hR x
    use Y, g, hg
    exact heq

/-- Turn a `K`-cover into a `Q`-cover by showing that the components satisfy `Q`. -/
def Cover.changeProp [JointlySurjective K] (𝒰 : X.Cover K) (h : ∀ j, Q (𝒰.f j)) :
    X.Cover (precoverage Q) where
  I₀ := 𝒰.I₀
  X := 𝒰.X
  f := 𝒰.f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨𝒰.exists_eq, h⟩

/-- We construct a cover from another, by providing the needed fields and showing that the
provided fields are isomorphic with the original cover. -/
@[simps I₀ X f]
def Cover.copy [P.RespectsIso] {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P))
    (J : Type*) (obj : J → Scheme)
    (map : ∀ i, obj i ⟶ X) (e₁ : J ≃ 𝒰.I₀) (e₂ : ∀ i, obj i ≅ 𝒰.X (e₁ i))
    (h : ∀ i, map i = (e₂ i).hom ≫ 𝒰.f (e₁ i)) : X.Cover (precoverage P) where
  I₀ := J
  X := obj
  f := map
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, ?_⟩
    · obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
      obtain ⟨i, rfl⟩ := e₁.surjective i
      use i, (e₂ i).inv y
      simp [h]
    · simp_rw [h, MorphismProperty.cancel_left_of_respectsIso]
      intro i
      exact 𝒰.map_prop _

/-- The pushforward of a cover along an isomorphism. -/
@[simps! I₀ X f]
def Cover.pushforwardIso [P.RespectsIso] [P.ContainsIdentities] [P.IsStableUnderComposition]
    {X Y : Scheme.{u}} (𝒰 : Cover.{v} (precoverage P) X) (f : X ⟶ Y) [IsIso f] :
    Cover.{v} (precoverage P) Y :=
  Cover.copy ((coverOfIsIso.{v, u} f).bind fun _ => 𝒰) 𝒰.I₀ _ _
    ((Equiv.punitProd _).symm.trans (Equiv.sigmaEquivProd PUnit 𝒰.I₀).symm) (fun _ => Iso.refl _)
    fun _ => (Category.id_comp _).symm

/-- Adding map satisfying `P` into a cover gives another cover. -/
@[simps toPreZeroHypercover]
nonrec def Cover.add {X Y : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : Y ⟶ X)
    (hf : P f := by infer_instance) : X.Cover (precoverage P) where
  __ := 𝒰.toPreZeroHypercover.add f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨some <| 𝒰.idx x, 𝒰.covers x⟩, ?_⟩
    rintro (i | i) <;> simp [hf, 𝒰.map_prop]

/-- The family of morphisms from the pullback cover to the original cover. -/
def Cover.pullbackHom [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
    {X W : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : W ⟶ X) (i) [∀ x, HasPullback f (𝒰.f x)] :
    (𝒰.pullback₁ f).X i ⟶ 𝒰.X i :=
  pullback.snd f (𝒰.f i)

@[reassoc (attr := simp)]
lemma Cover.pullbackHom_map [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
    {X W : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : W ⟶ X)
    [∀ (x : 𝒰.I₀), HasPullback f (𝒰.f x)] (i) :
    𝒰.pullbackHom f i ≫ 𝒰.f i = (𝒰.pullback₁ f).f i ≫ f := pullback.condition.symm

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
  covers (x : S) : x ∈ Set.range (f (idx x))
  /-- the component maps satisfy `P` -/
  map_prop (j : I₀) : P (f j) := by infer_instance

/-- The cover associated to an affine cover. -/
@[simps]
def AffineCover.cover {X : Scheme.{u}} (𝒰 : X.AffineCover P) :
    X.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X j := Spec (𝒰.X j)
  f := 𝒰.f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, 𝒰.map_prop⟩
    obtain ⟨y, hy⟩ := 𝒰.covers x
    use 𝒰.idx x, y

/-- Any `v`-cover `𝒰` induces a `u`-cover indexed by the points of `X`. -/
@[simps!]
def Cover.ulift (𝒰 : Cover.{v} (precoverage P) X) : Cover.{u} (precoverage P) X where
  I₀ := X
  X x := 𝒰.X (𝒰.idx x)
  f x := 𝒰.f _
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ 𝒰.map_prop _⟩
    use x, (𝒰.exists_eq x).choose_spec.choose, (𝒰.exists_eq x).choose_spec.choose_spec

instance : Precoverage.Small.{u} (precoverage P) where
  zeroHypercoverSmall {S} 𝒰 := ⟨S, Cover.idx 𝒰, (Cover.ulift 𝒰).mem₀⟩

section category

/--
A morphism between covers `𝒰 ⟶ 𝒱` indicates that `𝒰` is a refinement of `𝒱`.
Since covers of schemes are indexed, the definition also involves a map on the
indexing types.
This is implemented as an `abbrev` for `CategoryTheory.Precoverage.ZeroHypercover.Hom`.
-/
abbrev Cover.Hom {X : Scheme.{u}} (𝒰 𝒱 : Cover.{v} K X) :=
  Precoverage.ZeroHypercover.Hom K 𝒰 𝒱

@[deprecated (since := "2026-01-13")] alias Cover.Hom.idx := PreZeroHypercover.Hom.s₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.app := PreZeroHypercover.Hom.h₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.w := PreZeroHypercover.Hom.w₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.id := PreZeroHypercover.Hom.id

@[deprecated (since := "2026-01-13")] alias Cover.Hom.comp := PreZeroHypercover.Hom.comp

@[deprecated (since := "2026-01-13")] alias Cover.id_idx_apply := PreZeroHypercover.id_s₀

@[deprecated (since := "2026-01-13")] alias Cover.id_app := PreZeroHypercover.id_h₀

@[deprecated (since := "2026-01-13")] alias Cover.comp_idx_apply := PreZeroHypercover.comp_s₀

@[deprecated (since := "2026-01-13")] alias Cover.comp_app := PreZeroHypercover.comp_h₀

end category

end MorphismProperty

end Scheme

end AlgebraicGeometry

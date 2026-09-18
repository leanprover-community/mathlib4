/-
Copyright (c) 2023 Anne Baanen, Sam van Gool, Leo Mayer, Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Sam van Gool, Leo Mayer, Brendan Murphy
-/
module

public import Mathlib.Topology.Category.Locale
public import Mathlib.Topology.Sober

/-!
# Adjunction between Locales and Topological Spaces

This file defines the point functor from the category of locales to topological spaces
and proves that it is right adjoint to the forgetful functor from topological spaces to locales.

## Main declarations

* `Locale.pt`: the *points* functor from the category of locales to the category of topological
  spaces.

* `Locale.adjunctionTopToLocalePT`: the adjunction between the functors `topToLocale` and `pt`.

## Motivation

This adjunction provides a framework in which several Stone-type dualities fit.

## Implementation notes

* In naming the various functions below, we follow common terminology and reserve the word *point*
  for an inhabitant of a type `X` which is a topological space, while we use the word *element* for
  an inhabitant of a type `L` which is a locale.

## References

* [J. Picado and A. Pultr, Frames and Locales: topology without points][picado2011frames]

## Tags

topological space, frame, locale, Stone duality, adjunction, points
-/

@[expose] public section

open CategoryTheory Order Set TopologicalSpace Topology

universe u

namespace Locale

/-! ### Definition of the points functor `pt` -/
section pt_definition

variable (L : Type*) [CompleteLattice L]

/-- The type of points of a complete lattice `L`, where a *point* of a complete lattice is,
by definition, a frame homomorphism from `L` to `Prop`. -/
abbrev PT := FrameHom L Prop

/-- The frame homomorphism from a complete lattice `L` to the complete lattice of sets of
points of `L`. -/
@[simps]
def openOfElementHom : FrameHom L (Set (PT L)) where
  toFun u := {x | x u}
  map_inf' a b := by simp [Set.ofPred_and]
  map_top' := by simp
  map_sSup' S := by ext; simp [Prop.exists]

namespace PT

/-- The topology on the set of points of the complete lattice `L`. -/
instance instTopologicalSpace : TopologicalSpace (PT L) where
  IsOpen s := ∃ u, {x | x u} = s
  isOpen_univ := ⟨⊤, by simp⟩
  isOpen_inter := by rintro s t ⟨u, rfl⟩ ⟨v, rfl⟩; use u ⊓ v; simp_rw [map_inf]; rfl
  isOpen_sUnion S hS := by
    choose f hf using hS
    use ⨆ t, ⨆ ht, f t ht
    simp_rw [map_iSup, iSup_Prop_eq, ofPred_exists, hf, sUnion_eq_biUnion]

/-- Characterization of when a subset of the space of points is open. -/
lemma isOpen_iff (U : Set (PT L)) : IsOpen U ↔ ∃ u : L, {x | x u} = U := Iff.rfl

lemma isClosed_iff (S : Set (PT L)) : IsClosed S ↔ ∃ u, {x | ¬ x u} = S := by
  simp only [← isOpen_compl_iff, isOpen_iff, Set.ext_iff]
  congr! 3
  grind

lemma specializes_iff (x y : PT L) : x ⤳ y ↔ y ≤ x := by
  simp [specializes_iff_forall_open, isOpen_iff, LE.le]

instance : T0Space (PT L) where
  t0 := by simp +contextual [inseparable_iff_specializes_and, specializes_iff, le_antisymm_iff]

instance : QuasiSober (PT L) where
  sober := by
    intro S ⟨h_ne, h_irred⟩ h_closed
    let x : L → Prop := fun u ↦ ∃ y ∈ S, y u
    have hinf (u v : L) : x (u ⊓ v) = x u ⊓ x v := by
      simp_rw [x, map_inf, inf_Prop_eq, eq_iff_iff]
      refine ⟨fun h ↦ ⟨h.imp ?_, h.imp ?_⟩, fun ⟨⟨y, hy, hyu⟩, z, hz, hzv⟩ ↦ ?irred⟩
      case irred => exact h_irred {x | x u} {x | x v} ⟨u, rfl⟩ ⟨v, rfl⟩ ⟨y, hy, hyu⟩ ⟨z, hz, hzv⟩
      all_goals simp +contextual
    have htop : x ⊤ = ⊤ := by simpa [x]
    have hsup (s : Set L) : x (sSup s) = sSup (x '' s) := by
      simp_rw [x, map_sSup, sSup_image, iSup_Prop_eq, eq_iff_iff, ← exists_prop]
      exact exists₂_comm
    use {toFun := x, map_inf' := hinf, map_top' := htop, map_sSup' := hsup}
    obtain ⟨u, rfl⟩ := isClosed_iff L S |>.mp h_closed
    simp [isGenericPoint_def, Set.ext_iff, ← specializes_iff_mem_closure, specializes_iff, x,
      LE.le]
    grind

end PT

/-- The covariant functor `pt` from the category of locales to the category of
topological spaces, which sends a locale `L` to the topological space `PT L` of homomorphisms
from `L` to `Prop` and a locale homomorphism `f` to a continuous function between the spaces
of points. -/
def pt : Locale ⥤ TopCat where
  obj L := ↧(PT L.unop)
  map f := TopCat.ofHom ⟨fun p ↦ p.comp f.unop.hom,
    continuous_def.2 <| by rintro s ⟨u, rfl⟩; use f.unop u; rfl⟩

end pt_definition

section locale_top_adjunction

open PT

/-- The unit of the adjunction between locales and topological spaces, which associates with
a point `x` of the space `X` a point of the locale of opens of `X`. -/
@[simps]
def localePointOfSpacePoint (X : Type*) [TopologicalSpace X] (x : X) : PT (Opens X) where
  toFun := (x ∈ ·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' S := by simp [Prop.exists]

lemma isInducing_localePointOfSpacePoint (X : Type*) [TopologicalSpace X] :
    IsInducing (localePointOfSpacePoint X) where
  eq_induced := by
    ext u
    simp_rw [isOpen_induced_iff, isOpen_iff, exists_exists_eq_and, preimage_ofPred_eq,
      localePointOfSpacePoint_toFun, SetLike.setOfPred_mem_eq]
    exact ⟨fun hu ↦ ⟨⟨u, hu⟩, rfl⟩, fun ⟨⟨u', hu'⟩, heq⟩ ↦ heq ▸ hu'⟩

/-- The counit is a frame homomorphism. -/
def counitAppCont (L : Type*) [CompleteLattice L] : FrameHom L (Opens <| PT L) where
  toFun u := ⟨openOfElementHom L u, u, rfl⟩
  map_inf' a b := by simp
  map_top' := by simp
  map_sSup' S := by ext; simp

/-- On an object in the image of `Opens`, `counitAppCont` is an order isomorphism. Abstractly, this
shows that the adjunction to follow is idempotent. -/
def orderIsoOpensPtOpens (X : Type*) [TopologicalSpace X] : Opens X ≃o Opens (PT (Opens X)) :=
  OrderIso.ofHomInv
    (counitAppCont (Opens X))
    (Opens.comap ⟨localePointOfSpacePoint X, (isInducing_localePointOfSpacePoint X).continuous⟩)
    (by ext ⟨u, v, hv⟩ x; simp [counitAppCont, Opens.comap, ← hv]) rfl

/-- The forgetful functor `topToLocale` is left adjoint to the functor `pt`. -/
def adjunctionTopToLocalePT : topToLocale ⊣ pt where
  unit := { app := fun X ↦ TopCat.ofHom ⟨localePointOfSpacePoint X,
    (isInducing_localePointOfSpacePoint X).continuous⟩ }
  counit := { app := fun L ↦ ⟨Frm.ofHom (counitAppCont L)⟩ }

end locale_top_adjunction

end Locale

open Locale in
/-- A down-to-earth version of `Locale.adjunctionTopToLocalePT`, expressed as an equivalence
between continuous maps `X → PT L` and frame homomorphisms `L → Opens X`. -/
def continuousMapPTEquivFrameHomOpens (X : Type u) [TopologicalSpace X] (L : Type u)
    [Order.Frame L] : C(X, PT L) ≃ FrameHom L (Opens X) :=
  (TopCat.Hom.equivContinuousMap ↧X ↧(PT L)).symm.trans <|
    (adjunctionTopToLocalePT.homEquiv ↧X _).symm.trans <| homEquivFrameHom _ _

/-
Copyright (c) 2023 Anne Baanen, Sam van Gool, Leo Mayer, Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Sam van Gool, Leo Mayer, Brendan Murphy
-/
import Mathlib.Topology.Category.Locale

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

open CategoryTheory Order Set Topology TopologicalSpace

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
  map_inf' a b := by simp [Set.setOf_and]
  map_top' := by simp
  map_sSup' S := by ext; simp [Prop.exists_iff]

namespace PT

/-- The topology on the set of points of the complete lattice `L`. -/
instance instTopologicalSpace : TopologicalSpace (PT L) where
  IsOpen s := ∃ u, {x | x u} = s
  isOpen_univ := ⟨⊤, by simp⟩
  isOpen_inter := by rintro s t ⟨u, rfl⟩ ⟨v, rfl⟩; use u ⊓ v; simp_rw [map_inf]; rfl
  isOpen_sUnion S hS := by
    choose f hf using hS
    use ⨆ t, ⨆ ht, f t ht
    simp_rw [map_iSup, iSup_Prop_eq, setOf_exists, hf, sUnion_eq_biUnion]

/-- Characterization of when a subset of the space of points is open. -/
lemma isOpen_iff (U : Set (PT L)) : IsOpen U ↔ ∃ u : L, {x | x u} = U := Iff.rfl

end PT

/-- The covariant functor `pt` from the category of locales to the category of
topological spaces, which sends a locale `L` to the topological space `PT L` of homomorphisms
from `L` to `Prop` and a locale homomorphism `f` to a continuous function between the spaces
of points. -/
def pt : Locale ⥤ TopCat where
  obj L := .of (PT L.unop)
  map f := TopCat.ofHom ⟨fun p ↦ p.comp f.unop.hom,
    continuous_def.2 <| by rintro s ⟨u, rfl⟩; use f.unop u; rfl⟩

end pt_definition

section locale_top_adjunction

variable (X : Type*) [TopologicalSpace X] (L : Locale)

/-- The unit of the adjunction between locales and topological spaces, which associates with
a point `x` of the space `X` a point of the locale of opens of `X`. -/
@[simps]
def localePointOfSpacePoint (x : X) : PT (Opens X) where
  toFun := (x ∈ ·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' S := by simp [Prop.exists_iff]

/-- The counit is a frame homomorphism. -/
def counitAppCont : FrameHom L (Opens <| PT L) where
  toFun u := ⟨openOfElementHom L u, u, rfl⟩
  map_inf' a b := by simp
  map_top' := by simp
  map_sSup' S := by ext; simp

/-- The forgetful functor `topToLocale` is left adjoint to the functor `pt`. -/
def adjunctionTopToLocalePT : topToLocale ⊣ pt where
  unit := { app := fun X ↦ TopCat.ofHom ⟨localePointOfSpacePoint X, continuous_def.2 <|
        by rintro _ ⟨u, rfl⟩; simpa using u.2⟩ }
  counit := { app := fun L ↦ ⟨Frm.ofHom (counitAppCont L)⟩ }

end locale_top_adjunction

end Locale

/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
/-!

# Dominant rational maps

This file defines `RationalMap.IsDominant` and establishes its connection to
`IsDominant` on the underlying partial maps.

## Main definitions

- `Scheme.RationalMap.IsDominant`: a rational map is dominant if some (equivalently, any)
  representative partial map has dominant underlying morphism.
- `Scheme.RationalMap.dominantRep`: a chosen dominant partial map representative.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

namespace Scheme

namespace PartialMap

/-- Restricting a dominant partial map yields a dominant partial map. -/
instance isDominant_restrict_hom (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) : IsDominant (f.restrict U hU hU').hom := by
  dsimp only [restrict_domain, restrict_hom]
  have : IsDominant (X.homOfLE hU') := Opens.isDominant_homOfLE hU hU'
  rwa [IsDominant.comp_iff]

/-- If a restriction of `f` is dominant, then `f` is dominant. -/
lemma isDominant_hom_of_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) [H : IsDominant (f.restrict U hU hU').hom] :
    IsDominant f.hom :=
  IsDominant.of_comp (X.homOfLE hU') f.hom (H := H)

/-- `f.hom` is dominant iff any restriction of `f` is. -/
lemma isDominant_hom_iff_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    IsDominant f.hom ↔ IsDominant (f.restrict U hU hU').hom :=
  ⟨fun _ ↦ f.isDominant_restrict_hom U hU hU',
    fun _ ↦ f.isDominant_hom_of_isDominant_restrict_hom U hU hU'⟩

/-- Dominance of the underlying morphism is invariant under equivalence of partial maps. -/
lemma isDominant_hom_iff_of_equiv (f g : X.PartialMap Y) (h : f.equiv g) :
    IsDominant f.hom ↔ IsDominant g.hom := by
  obtain ⟨W, hW, hWl, hWr, h⟩ := h
  have e₁ := isDominant_hom_iff_isDominant_restrict_hom f W hW hWl
  have e₂ := isDominant_hom_iff_isDominant_restrict_hom g W hW hWr
  dsimp only [restrict_domain, restrict_hom] at ⊢ e₁ e₂ h
  rw [e₁, h, ← e₂]

end PartialMap

namespace RationalMap

/-- A rational map is dominant if it has a representative partial map with dominant morphism. -/
@[mk_iff, stacks 0A1Z]
protected class IsDominant (f : X ⤏ Y) : Prop where
  exists_dominant_rep' : ∃ g : X.PartialMap Y, IsDominant g.hom ∧ g.toRationalMap = f

lemma exists_dominant_rep (f : X ⤏ Y) [f.IsDominant] :
    ∃ g : X.PartialMap Y, IsDominant g.hom ∧ g.toRationalMap = f :=
  IsDominant.exists_dominant_rep'

/-- A chosen dominant partial map representing of `f`. -/
noncomputable def dominantRep (f : X ⤏ Y) [f.IsDominant] : X.PartialMap Y :=
  f.exists_dominant_rep.choose

instance (f : X ⤏ Y) [f.IsDominant] : IsDominant f.dominantRep.hom :=
  f.exists_dominant_rep.choose_spec.1

@[simp]
lemma toRationalMap_dominantRep (f : X ⤏ Y) [f.IsDominant] : f.dominantRep.toRationalMap = f :=
  f.exists_dominant_rep.choose_spec.2

end RationalMap

instance PartialMap.isDominant_toRationalMap (f : X.PartialMap Y) [IsDominant f.hom] :
    f.toRationalMap.IsDominant :=
  ⟨f, ‹_›, rfl⟩

lemma PartialMap.toRationalMap_dominantRep_equiv (f : X.PartialMap Y) [IsDominant f.hom] :
    f.toRationalMap.dominantRep.equiv f := by
  rw [← PartialMap.toRationalMap_eq_iff, f.toRationalMap.toRationalMap_dominantRep]

lemma PartialMap.isDominant_hom_of_toRationalMap_eq (f : X.PartialMap Y) (g : X ⤏ Y)
    [H : g.IsDominant] (h : f.toRationalMap = g) : IsDominant f.hom := by
  obtain ⟨_, _, rfl⟩ := H
  rwa [isDominant_hom_iff_of_equiv _ _ (toRationalMap_eq_iff.mp h)]

lemma PartialMap.isDominant_hom_of_isDominant_toRationalMap (f : X.PartialMap Y)
    [H : f.toRationalMap.IsDominant] : IsDominant f.hom :=
  isDominant_hom_of_toRationalMap_eq f f.toRationalMap rfl

lemma PartialMap.isDominant_hom_iff_isDominant_toRationalMap (f : X.PartialMap Y) :
    IsDominant f.hom ↔ f.toRationalMap.IsDominant :=
  ⟨fun _ ↦ f.isDominant_toRationalMap, fun _ ↦ f.isDominant_hom_of_isDominant_toRationalMap⟩

end Scheme

end AlgebraicGeometry

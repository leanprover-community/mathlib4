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

## Main definition

- `Scheme.RationalMap.IsDominant`: a rational map is dominant if some (equivalently, any)
  representative partial map has dominant underlying morphism.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

namespace Scheme

namespace PartialMap

set_option backward.defeqAttrib.useBackward true in
/-- Restricting a dominant partial map to a dense open yields a dominant partial map. -/
lemma isDominant_restrict_hom (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
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

set_option backward.defeqAttrib.useBackward true in
/-- Dominance of the underlying morphism is invariant under equivalence of partial maps. -/
lemma isDominant_hom_iff_of_equiv (f g : X.PartialMap Y) (h : f.equiv g) :
    IsDominant f.hom ↔ IsDominant g.hom := by
  obtain ⟨W, hW, hWl, hWr, h⟩ := h
  have e₁ := isDominant_hom_iff_isDominant_restrict_hom f W hW hWl
  have e₂ := isDominant_hom_iff_isDominant_restrict_hom g W hW hWr
  dsimp only [restrict_domain, restrict_hom] at ⊢ e₁ e₂ h
  rw [e₁, h, ← e₂]

end PartialMap

/-- A rational map is dominant if some (equivalently, any) representative partial map has
dominant underlying morphism. -/
@[mk_iff, stacks 0A1Z]
protected class RationalMap.IsDominant (f : X ⤏ Y) : Prop where
  out : Quotient.liftOn f (fun g ↦ IsDominant g.hom) <| fun _ _ h ↦
    propext (PartialMap.isDominant_hom_iff_of_equiv _ _ h)

@[simp]
lemma PartialMap.isDominant_toRationalMap_iff (f : X.PartialMap Y) :
    f.toRationalMap.IsDominant ↔ IsDominant f.hom :=
  f.toRationalMap.isDominant_iff

instance (f : X.PartialMap Y) [IsDominant f.hom] :
    f.toRationalMap.IsDominant := by
  rwa [f.isDominant_toRationalMap_iff]

instance (f : X ⤏ Y) [f.IsDominant] :
    IsDominant f.representative.hom := by
  rwa [← f.representative.isDominant_toRationalMap_iff, f.toRationalMap_representative]

end Scheme

end AlgebraicGeometry

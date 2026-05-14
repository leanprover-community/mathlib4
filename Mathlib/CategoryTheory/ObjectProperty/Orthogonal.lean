/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Orthogonal of a property of objects

Let `P` be a property of objects in a category with zero morphisms.
We define `P.rightOrthogonal` as the property of objects `Y` such that
any map `f : X ⟶ Y` vanishes when `P X` holds. Similarly, we define
`P.leftOrthogonal` as the property of objects `X` such that
any map `f : X ⟶ Y` vanishes when `P Y` holds.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- In a category with zero morphisms, the right orthogonal of a property of objects `P`
is the property of objects `Y` such that any map `X ⟶ Y` vanishes when `P X` holds. -/
@[stacks 0FXB]
def rightOrthogonal : ObjectProperty C :=
  fun Y ↦ ∀ ⦃X : C⦄ (f : X ⟶ Y), P X → f = 0

lemma rightOrthogonal_iff (Y : C) :
    P.rightOrthogonal Y ↔ ∀ ⦃X : C⦄ (f : X ⟶ Y), P X → f = 0 := Iff.rfl

/-- In a category with zero morphisms, the left orthogonal of a property of objects `P`
is the property of objects `X` such that any map `X ⟶ Y` vanishes when `P Y` holds. -/
@[stacks 0FXB]
def leftOrthogonal : ObjectProperty C :=
  fun X ↦ ∀ ⦃Y : C⦄ (f : X ⟶ Y), P Y → f = 0

lemma leftOrthogonal_iff (X : C) :
    P.leftOrthogonal X ↔ ∀ ⦃Y : C⦄ (f : X ⟶ Y), P Y → f = 0 := Iff.rfl

instance : P.rightOrthogonal.IsClosedUnderIsomorphisms where
  of_iso e h X f hX := by
    rw [← cancel_mono e.inv, zero_comp]
    exact h _ hX

instance : P.leftOrthogonal.IsClosedUnderIsomorphisms where
  of_iso e h Y f hY := by
    rw [← cancel_epi e.hom, comp_zero]
    exact h _ hY

instance [HasZeroObject C] : P.rightOrthogonal.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun _ _ _ ↦ by ext⟩

instance [HasZeroObject C] : P.leftOrthogonal.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun _ _ _ ↦ by ext⟩

end ObjectProperty

end CategoryTheory

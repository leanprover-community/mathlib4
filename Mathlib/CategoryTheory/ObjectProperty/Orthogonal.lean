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

/-- The pair `(rightOrthogonal, leftOrthogonal)` forms a Galois connection between
`ObjectProperty C` and its opposite order. -/
lemma gc_rightOrthogonal_leftOrthogonal :
    GaloisConnection (OrderDual.toDual (α := ObjectProperty C) ∘ rightOrthogonal)
      (leftOrthogonal ∘ OrderDual.ofDual) :=
  fun _ _ ↦ ⟨fun h _ hPX _ f hQY ↦ h _ hQY f hPX, fun h _ hQY _ f hPX ↦ h _ hPX f hQY⟩

lemma le_leftOrthogonal_iff_le_rightOrthogonal (Q : ObjectProperty C) :
    P ≤ Q.leftOrthogonal ↔ Q ≤ P.rightOrthogonal :=
  -- the Galois connection has `rightOrthogonal` as its left adjoint, so its two sides
  -- appear in the opposite order
  (gc_rightOrthogonal_leftOrthogonal P (OrderDual.toDual Q)).symm

lemma le_leftOrthogonal_rightOrthogonal : P ≤ P.rightOrthogonal.leftOrthogonal :=
  gc_rightOrthogonal_leftOrthogonal.le_u_l P

lemma le_rightOrthogonal_leftOrthogonal : P ≤ P.leftOrthogonal.rightOrthogonal :=
  gc_rightOrthogonal_leftOrthogonal.dual.le_u_l P

lemma antitone_rightOrthogonal : Antitone (rightOrthogonal (C := C)) :=
  gc_rightOrthogonal_leftOrthogonal.monotone_l

lemma antitone_leftOrthogonal : Antitone (leftOrthogonal (C := C)) :=
  gc_rightOrthogonal_leftOrthogonal.dual.monotone_l

@[simp]
lemma leftOrthogonal_rightOrthogonal_leftOrthogonal :
    P.leftOrthogonal.rightOrthogonal.leftOrthogonal = P.leftOrthogonal :=
  gc_rightOrthogonal_leftOrthogonal.dual.l_u_l_eq_l P

@[simp]
lemma rightOrthogonal_leftOrthogonal_rightOrthogonal :
    P.rightOrthogonal.leftOrthogonal.rightOrthogonal = P.rightOrthogonal :=
  gc_rightOrthogonal_leftOrthogonal.l_u_l_eq_l P

lemma rightOrthogonal_op : P.op.rightOrthogonal = P.leftOrthogonal.op := by
  ext X
  exact ⟨fun h _ _ hY ↦ congr($(h _ hY).unop), fun h _ _ hY ↦ congr($(h _ hY).op)⟩

lemma leftOrthogonal_op : P.op.leftOrthogonal = P.rightOrthogonal.op := by
  ext X
  exact ⟨fun h _ _ hY ↦ congr($(h _ hY).unop), fun h _ _ hY ↦ congr($(h _ hY).op)⟩

lemma rightOrthogonal_unop (R : ObjectProperty Cᵒᵖ) :
    R.unop.rightOrthogonal = R.leftOrthogonal.unop := by
  ext X
  exact ⟨fun h _ _ hY ↦ congr($(h _ hY).op), fun h _ _ hY ↦ congr($(h _ hY).unop)⟩

lemma leftOrthogonal_unop (R : ObjectProperty Cᵒᵖ) :
    R.unop.leftOrthogonal = R.rightOrthogonal.unop := by
  ext X
  exact ⟨fun h _ _ hY ↦ congr($(h _ hY).op), fun h _ _ hY ↦ congr($(h _ hY).unop)⟩

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

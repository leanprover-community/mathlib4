/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Comon_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cartesian Categories as Copy-Discard Categories

Every cartesian monoidal category is a copy-discard category where:
- Copy is the diagonal map
- Discard is the unique map to terminal

## Main results

* `CopyDiscardCategory` instance for cartesian monoidal categories
* All morphisms in cartesian categories are deterministic

## Tags

cartesian, copy-discard, comonoid, symmetric monoidal
-/

universe v u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]

-- Provide `ComonObj` instances using the canonical cartesian comonoid structure
instance instComonObjOfCartesian (X : C) : ComonObj X :=
  ((cartesianComon C).obj X).comon

-- Use the canonical `BraidedCategory` instance from cartesian structure
instance : BraidedCategory C := BraidedCategory.ofCartesianMonoidalCategory

namespace CartesianCopyDiscard

/-- Every object in a cartesian category has commutative comonoid structure. -/
instance instIsCommComonObj (X : C) : IsCommComonObj X where
  comul_comm := by ext <;> simp

end CartesianCopyDiscard

/-- Cartesian categories have copy-discard structure. -/
instance : CopyDiscardCategory C where
  comonObj X := inferInstance
  isCommComonObj X := inferInstance
  copy_tensor := by cat_disch
  discard_tensor := by cat_disch
  copy_unit := by cat_disch
  discard_unit := by cat_disch

namespace CartesianCopyDiscard

/-- In cartesian categories, all morphisms preserve copy (are deterministic). -/
lemma deterministic {X Y : C} (f : X ⟶ Y) : f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ₘ f) := by ext <;> simp

end CartesianCopyDiscard

end CategoryTheory

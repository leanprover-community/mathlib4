/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic
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

namespace CartesianCopyDiscard

/-- Provide `ComonObj` instances using the canonical cartesian comonoid structure. -/
abbrev instComonObjOfCartesian (X : C) : ComonObj X :=
  ((cartesianComon C).obj X).comon

attribute [local instance] instComonObjOfCartesian

variable [BraidedCategory C]

/-- Every object in a cartesian category has commutative comonoid structure. -/
instance instIsCommComonObjOfCartesian (X : C) : IsCommComonObj X where

/-- Cartesian categories have copy-discard structure. -/
abbrev ofCartesianMonoidalCategory : CopyDiscardCategory C where

attribute [local instance] ofCartesianMonoidalCategory

/-- In cartesian categories, every morphism is deterministic (preserves the comonoid structure). -/
instance instDeterministic {X Y : C} (f : X ⟶ Y) : Deterministic f where

end CartesianCopyDiscard

end CategoryTheory

/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.CopyDiscardCategory.Basic

/-!
# Deterministic Morphisms in Copy-Discard Categories

Morphisms that preserve the copy operation perfectly.

A morphism `f : X → Y` is deterministic if copying then applying `f` to both
copies equals applying `f` then copying: `f ≫ copy_Y = copy_X ≫ (f ⊗ f)`.

In probabilistic settings, these are morphisms without randomness.
In cartesian categories, all morphisms are deterministic.

## Main definitions

* `Deterministic` - Type class for morphisms that preserve copying

## Main results

* Identity morphisms are deterministic
* Composition of deterministic morphisms is deterministic

## Tags

deterministic, copy-discard category, comonoid morphism
-/

namespace CategoryTheory

open MonoidalCategory CopyDiscardCategory

variable {C : Type*} [Category C] [MonoidalCategory C] [CopyDiscardCategory C]

/-- A morphism is deterministic if it preserves the copy operation.

For `f : X → Y`, this means `f ≫ copy_Y = copy_X ≫ (f ⊗ f)`. -/
class Deterministic {X Y : C} (f : X ⟶ Y) : Prop where
  preserves_copy : f ≫ copyMor Y = copyMor X ≫ (f ⊗ₘ f)

namespace Deterministic

variable {X Y Z : C}

/-- The identity morphism is deterministic. -/
instance : Deterministic (𝟙 X) where
  preserves_copy := by simp

/-- Composition of deterministic morphisms is deterministic. -/
instance (f : X ⟶ Y) (g : Y ⟶ Z) [Deterministic f] [Deterministic g] :
    Deterministic (f ≫ g) where
  preserves_copy := by
    rw [Category.assoc, Deterministic.preserves_copy, ← Category.assoc,
        Deterministic.preserves_copy, Category.assoc]
    simp only [← MonoidalCategory.tensor_comp]

/-- Deterministic morphisms commute with copying. -/
lemma copy_natural {f : X ⟶ Y} [Deterministic f] :
    f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ₘ f) := preserves_copy

/-- Alternative form of the determinism condition. -/
lemma preserves_copy' {f : X ⟶ Y} [Deterministic f] :
    f ≫ copyMor Y = copyMor X ≫ (f ⊗ₘ f) := preserves_copy

end Deterministic

end CategoryTheory

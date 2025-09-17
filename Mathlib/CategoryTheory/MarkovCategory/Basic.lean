/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Markov Categories

Copy-discard categories where deletion is natural for all morphisms.

## Main definitions

* `MarkovCategory` - Copy-discard category with natural deletion

## Main results

* `unit_terminal` - The monoidal unit is terminal

## Implementation notes

Natural deletion forces probabilistic interpretation: morphisms preserve normalization. The unit
being terminal follows from naturality of deletion.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

Markov category, probability, categorical probability
-/

namespace CategoryTheory

open MonoidalCategory CopyDiscardCategory ComonObj Limits

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Copy-discard category where discard is natural. -/
class MarkovCategory (C : Type*) [Category C] [MonoidalCategory C]
    extends CopyDiscardCategory C where
  /-- Process then discard equals delete directly. -/
  discard_natural {X Y : C} (f : X ⟶ Y) : f ≫ ε[Y] = ε[X]

namespace MarkovCategory

variable [MarkovCategory C]

/-- Natural discard as simp lemma. -/
@[simp]
lemma discard_natural_simp {X Y : C} (f : X ⟶ Y) : f ≫ ε[Y] = ε[X] :=
  discard_natural f

/-- The monoidal unit is terminal. -/
theorem unit_terminal (X : C) (f : X ⟶ 𝟙_ C) : f = ε[X] := by
  calc f = f ≫ 𝟙 (𝟙_ C) := (Category.comp_id _).symm
       _ = f ≫ ε[𝟙_ C] := by rw [← counit_unit]  -- Use the lemma from CopyDiscardCategory
       _ = ε[X] := discard_natural f

/-- The monoidal unit is a terminal object. -/
instance : IsTerminal (𝟙_ C : C) where
  lift := fun s => ε[s.pt] -- The unique morphism to 𝟙_ C is the counit
  fac := fun _ j => PEmpty.elim j.as -- Vacuous: no objects in empty diagram
  uniq := fun s m _ => (unit_terminal s.pt m) -- Uniqueness by unit_terminal

/-- Morphisms between terminal objects are unique. -/
lemma terminal_unique (f : (𝟙_ C) ⟶ (𝟙_ C)) : f = 𝟙 (𝟙_ C) := by
  rw [unit_terminal (𝟙_ C) f, counit_unit]  -- Use counit_unit instead of del_unit

end MarkovCategory

end CategoryTheory

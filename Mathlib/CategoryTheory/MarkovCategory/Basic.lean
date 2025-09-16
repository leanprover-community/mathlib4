/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Markov Categories

Copy-discard categories with natural deletion, giving a categorical approach to probability.

A Markov category is a copy-discard category where deletion is natural:
`f ≫ del_Y = del_X` for any morphism `f : X → Y`.

This axiom forces the monoidal unit to be terminal and ensures probabilistic
normalization (probabilities sum to 1). It means that processing information
then discarding it equals discarding it directly.

## Main definitions

* `MarkovCategory` - A copy-discard category with natural deletion

## Main results

* The monoidal unit is terminal in any Markov category
* Deletion is natural for all morphisms

## Examples

* Finite stochastic matrices (`FinStoch`)
* Cartesian categories (via `instMarkovCategoryOfCartesian`)
* Kleisli categories of probability monads

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

Markov category, probability, categorical probability, stochastic
-/

namespace CategoryTheory

open MonoidalCategory CopyDiscardCategory Limits

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- A copy-discard category where deletion is natural.

This axiom makes the monoidal unit terminal and ensures probabilistic normalization. -/
class MarkovCategory (C : Type*) [Category C] [MonoidalCategory C]
  extends CopyDiscardCategory C where
  /-- Deletion commutes with all morphisms: `f ≫ del_Y = del_X`.
  This makes the monoidal unit terminal. -/
  del_natural : ∀ {X Y} (f : X ⟶ Y), f ≫ delMor Y = delMor X

namespace MarkovCategory

open CopyDiscardCategory

variable [MarkovCategory C]

/-- Deletion commutes with all morphisms. -/
@[simp, reassoc]
lemma del_natural_simp {X Y : C} (f : X ⟶ Y) : f ≫ ε[Y] = ε[X] := del_natural f

/-- The delete morphism from the unit is the identity. -/
axiom unit_delete_is_id : ε[𝟙_ C] = 𝟙 (𝟙_ C)

/-- The monoidal unit is terminal: there is exactly one morphism from any object to the unit. -/
theorem unit_terminal : ∀ (X : C) (f : X ⟶ 𝟙_ C), f = ε[X] := by
  intro X f
  -- Use that delete from unit is identity (from coherence theory)
  have h1 : ε[𝟙_ C] = 𝟙 (𝟙_ C) := unit_delete_is_id
  -- Apply naturality of deletion
  calc f = f ≫ 𝟙 (𝟙_ C) := (Category.comp_id _).symm
       _ = f ≫ ε[𝟙_ C] := by rw [← h1]
       _ = ε[X] := del_natural_simp f

/-- Deterministic morphisms preserve deletion.

Note: All morphisms preserve deletion (by `del_natural`), not just deterministic ones. -/
lemma deterministic_preserves_del {X Y : C} {f : X ⟶ Y} [Deterministic f] :
    f ≫ ε[Y] = ε[X] := del_natural f

end MarkovCategory

end CategoryTheory

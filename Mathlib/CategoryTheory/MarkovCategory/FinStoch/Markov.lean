/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.MarkovCategory.FinStoch.CopyDiscard
import Mathlib.CategoryTheory.MarkovCategory.Basic

/-!
# FinStoch as a Markov Category

FinStoch forms a Markov category where discard is natural for all morphisms.

## Main results

* `MarkovCategory FinStoch` - FinStoch is a Markov category
* `copy_not_natural` - Copy is not natural (proof that FinStoch is not cartesian)

## Implementation notes

Discard naturality follows from probability normalization: all stochastic matrices have row sums
equal to 1.

## Tags

Markov category, natural transformation, probabilistic
-/

namespace CategoryTheory.MarkovCategory

open FinStoch MonoidalCategory ComonObj

universe u

/-- FinStoch is a Markov category. -/
instance : MarkovCategory FinStoch where
  discard_natural f := by
    -- Discard is natural because probabilities sum to 1
    apply StochasticMatrix.ext
    ext i u
    simp [CategoryStruct.comp, StochasticMatrix.comp, ComonObj.counit, discard, f.row_sum]

/-- Copy is not natural in FinStoch. -/
theorem copy_not_natural : ∃ (X Y : FinStoch) (f : X ⟶ Y),
    f ≫ Δ[Y] ≠ Δ[X] ≫ (f ⊗ₘ f) := by
  -- Coin flip example
  let X : FinStoch := { carrier := Unit, fintype := inferInstance, decidableEq := inferInstance }
  let Y : FinStoch := { carrier := Bool, fintype := inferInstance, decidableEq := inferInstance }
  use X, Y
  -- Uniform: P(true|()) = P(false|()) = 1/2
  let f : X ⟶ Y := {
    toMatrix := fun _ b => (1 : NNReal) / 2
    row_sum := fun _ => by
      simp
      rw [Fintype.card_bool]
      norm_num
  }
  use f
  intro h
  have : (f ≫ Δ[Y]).toMatrix (() : Unit) ((true : Bool), (false : Bool)) =
         (Δ[X] ≫ (f ⊗ₘ f)).toMatrix (() : Unit) ((true : Bool), (false : Bool)) := by
    rw [h]
  simp only [CategoryStruct.comp, StochasticMatrix.comp, ComonObj.comul, copy,
             MonoidalCategoryStruct.tensorHom, StochasticMatrix.tensor] at this
  -- Simplify the left side first
  have left_zero : (∑ x, f.toMatrix () x * if x = true ∧ x = false then 1 else 0) = 0 := by
    simp only [Finset.sum_eq_zero_iff]
    intro x _
    simp
    intro h
    simp_all [instTensorUnit_comul, X, Y, f]
  -- Left: f then copy gives 0 (can't be in two different states)
  -- Right: copy then f⊗f gives 1/4 (independent coin flips)
  rw [left_zero] at this
    -- If the right side has any non-zero terms, we get contradiction
  -- For example, if the sum includes a term where j₁ = j₂ = ()
  have right_nonzero : (∑ x, (match x with | (j₁, j₂) => if () = j₁ ∧ () = j₂ then 1 else 0) *
    (f.toMatrix x.1 true * f.toMatrix x.2 false)) ≠ 0 := by
    -- Show there's at least one non-zero term
    norm_num
  -- Contradiction: 0 ≠ 0
  exact right_nonzero this.symm

end CategoryTheory.MarkovCategory

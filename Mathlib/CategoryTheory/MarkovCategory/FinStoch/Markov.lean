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
This is the key property distinguishing Markov categories from cartesian categories.

## Main results

* `MarkovCategory FinStoch` - FinStoch is a Markov category
* `copy_not_natural` - Copy is not natural (proof that FinStoch is not cartesian)

## Mathematical interpretation

Discard naturality means marginalization commutes with stochastic maps.
This follows from probability normalization: ∑_y P(y|x) = 1.

Copy non-naturality shows that duplicating before vs after a random process
gives different results. The coin flip example demonstrates this concretely.

## Tags

Markov category, natural transformation, probabilistic
-/

namespace CategoryTheory.MarkovCategory

open FinStoch MonoidalCategory ComonObj

universe u

/-- FinStoch is a Markov category. -/
instance : MarkovCategory FinStoch where
  discard_natural f := by
    -- Naturality: f ≫ ε = ε because ∑_y f(y|x) = 1
    apply StochasticMatrix.ext
    ext i u
    simp [CategoryStruct.comp, StochasticMatrix.comp, ComonObj.counit, discard, f.row_sum]

/-- Copy is not natural in FinStoch.
Counterexample: fair coin flip from a deterministic state. -/
theorem copy_not_natural : ∃ (X Y : FinStoch) (f : X ⟶ Y),
    f ≫ Δ[Y] ≠ Δ[X] ≫ (f ⊗ₘ f) := by
  -- Counterexample: fair coin flip
  let X : FinStoch := { carrier := Unit, fintype := inferInstance, decidableEq := inferInstance }
  let Y : FinStoch := { carrier := Bool, fintype := inferInstance, decidableEq := inferInstance }
  use X, Y
  -- Fair coin: P(true|*) = P(false|*) = 1/2
  let f : X ⟶ Y := {
    toMatrix := fun _ b => (1 : NNReal) / 2
    row_sum := fun _ => by
      simp
      rw [Fintype.card_bool]
      norm_num
  }
  use f
  intro h
  -- Compare at output (true, false)
  have : (f ≫ Δ[Y]).toMatrix (() : Unit) ((true : Bool), (false : Bool)) =
         (Δ[X] ≫ (f ⊗ₘ f)).toMatrix (() : Unit) ((true : Bool), (false : Bool)) := by
    rw [h]
  simp only [CategoryStruct.comp, StochasticMatrix.comp, ComonObj.comul, copy,
             MonoidalCategoryStruct.tensorHom, StochasticMatrix.tensor] at this
  -- Left path: flip then copy gives P(true,false) = 0 (can't be in both states)
  have left_zero : (∑ x, f.toMatrix () x * if x = true ∧ x = false then 1 else 0) = 0 := by
    simp only [Finset.sum_eq_zero_iff]
    intro x _
    simp
    intro h
    simp_all [instTensorUnit_comul, X, Y, f]
  rw [left_zero] at this
  -- Right path: copy then flip⊗flip gives P(true,false) = 1/4 (independent flips)
  have right_nonzero : (∑ x, (match x with | (j₁, j₂) => if () = j₁ ∧ () = j₂ then 1 else 0) *
    (f.toMatrix x.1 true * f.toMatrix x.2 false)) ≠ 0 := by
    -- The term at ((),()) contributes: 1 * (1/2 * 1/2) = 1/4 ≠ 0
    norm_num
  -- Contradiction: 0 = 1/4
  exact right_nonzero this.symm

end CategoryTheory.MarkovCategory

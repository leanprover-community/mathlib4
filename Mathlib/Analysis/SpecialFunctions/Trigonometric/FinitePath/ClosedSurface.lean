/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.FinitePath.Coherence

/-!
# Transport of the finite path gap limit to closed surfaces

This file records the finite-sum calculation obtained by assigning the limiting finite path gap to
each of the `2 * g` generators associated with a genus-`g` closed orientable surface.
-/

@[expose] public section

noncomputable section

open Real

namespace Real.FinitePath

/-- The sum of a family of defects indexed by `b₁` generators. -/
def cycleGapSum (b₁ : ℕ) (gap : Fin b₁ → ℝ) : ℝ :=
  ∑ i, gap i

/-- A constant gap on every generator sums to `b₁` times that gap. -/
theorem cycleGapSum_of_constant (b₁ : ℕ) (gap : Fin b₁ → ℝ) (c : ℝ)
    (hgap : ∀ i, gap i = c) : cycleGapSum b₁ gap = (b₁ : ℝ) * c := by
  simp [cycleGapSum, hgap]

/-- The limiting gap summed over the `2 * g` generators associated with genus `g`. -/
def closedSurfaceGap (g : ℕ) : ℝ :=
  cycleGapSum (2 * g) fun _ => gapLimit

/-- Transport through the generator count `2 * g`. -/
theorem closedSurfaceGap_eq_generatorCount_mul (g : ℕ) :
    closedSurfaceGap g = ((2 * g : ℕ) : ℝ) * gapLimit := by
  exact cycleGapSum_of_constant (2 * g) (fun _ => gapLimit) gapLimit fun _ => rfl

/-- The closed genus form of the transported limiting gap. -/
theorem closedSurfaceGap_eq_two_mul_genus_mul (g : ℕ) :
    closedSurfaceGap g = 2 * (g : ℝ) * gapLimit := by
  rw [closedSurfaceGap_eq_generatorCount_mul]
  push_cast
  rfl

/-- The limiting gap written with a single quotient under the square root. -/
theorem gapLimit_eq_sqrt_sub_six_div_three :
    gapLimit = Real.sqrt ((π ^ 2 - 6) / 3) - 1 := by
  unfold gapLimit coherenceLimit
  congr 2
  ring

/-- The fully expanded closed form for the transported gap at genus `g`. -/
theorem closedSurfaceGap_eq_sqrt_sub_six_div_three (g : ℕ) :
    closedSurfaceGap g =
      2 * (g : ℝ) * (Real.sqrt ((π ^ 2 - 6) / 3) - 1) := by
  rw [closedSurfaceGap_eq_two_mul_genus_mul, gapLimit_eq_sqrt_sub_six_div_three]

end Real.FinitePath

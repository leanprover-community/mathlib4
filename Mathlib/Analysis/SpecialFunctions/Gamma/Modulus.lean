/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

import Mathlib.Tactic

/-!
# The modulus of `Gamma` on the line `Re z = 1 / 2`

For real `y`, Euler's reflection formula at `z = 1 / 2 + i y` gives

`Gamma (1 / 2 + i y) * Gamma (1 / 2 - i y) = π / cosh (π y)`,

the product form of the identity `|Gamma (1 / 2 + i y)| ^ 2 = π / cosh (π y)`.
-/

public section

namespace Complex

/-- Sine on the shifted imaginary axis: `sin (π (1 / 2 + i y)) = cosh (π y)`. -/
theorem sin_pi_half_add_I (y : ℝ) :
    Complex.sin ((Real.pi : ℂ) * (((1 : ℂ) / 2) + (y : ℂ) * I)) =
      Complex.cosh ((Real.pi : ℂ) * (y : ℂ)) := by
  rw [show (Real.pi : ℂ) * (((1 : ℂ) / 2) + (y : ℂ) * I) =
      (Real.pi : ℂ) / 2 + ((Real.pi : ℂ) * (y : ℂ)) * I by ring]
  rw [Complex.sin_add, Complex.sin_mul_I, Complex.cos_mul_I]
  simp

/-- **Half-shifted Gamma modulus identity:**
`Gamma (1 / 2 + i y) * Gamma (1 / 2 - i y) = π / cosh (π y)`. -/
theorem Gamma_half_add_mul_Gamma_half_sub (y : ℝ) :
    Complex.Gamma (((1 : ℂ) / 2) + (y : ℂ) * I) *
      Complex.Gamma (((1 : ℂ) / 2) - (y : ℂ) * I) =
        ((Real.pi / Real.cosh (Real.pi * y) : ℝ) : ℂ) := by
  let z : ℂ := ((1 : ℂ) / 2) + (y : ℂ) * I
  have href := Complex.Gamma_mul_Gamma_one_sub z
  have hone : 1 - z = ((1 : ℂ) / 2) - (y : ℂ) * I := by
    dsimp [z]
    ring
  have hsin : Complex.sin ((Real.pi : ℂ) * z) =
      Complex.cosh ((Real.pi : ℂ) * (y : ℂ)) := by
    dsimp [z]
    exact sin_pi_half_add_I y
  rw [hone, hsin] at href
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh] at href
  push_cast at href
  simpa [z] using href

end Complex

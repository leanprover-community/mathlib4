/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Extended Nonnegative Real Exponential

We define `exp` as an extension of the exponential of a real
to the extended reals `EReal`. The function takes values
in the extended nonnegative reals `ℝ≥0∞`, with `exp ⊥ = 0` and `exp ⊤ = ⊤`.

## Main Definitions
- `ENNReal.exp`: The extension of the real exponential to `EReal`.
- `ENNReal.log_orderIso`, `ENNReal.log_equiv`: `log` seen respectively
as an order isomorphism and an homeomorphism.

## Main Results
- `ENNReal.log_strictMono`: `log` is increasing;
- `ENNReal.log_injective`, `ENNReal.log_surjective`, `ENNReal.log_bijective`: `log` is
  injective, surjective, and bijective;
- `ENNReal.log_mul_add`, `ENNReal.log_pow`, `ENNReal.log_rpow`: `log` satisfy
the identities `log (x * y) = log x + log y` and `log (x ^ y) = y * log x`
(with either `y ∈ ℕ` or `y ∈ ℝ`).

## Tags
ENNReal, EReal, logarithm
-/
namespace ENNReal

open scoped NNReal

/-! ### Definition -/
section Definition

/-- Exponential as a function from `EReal` to `ℝ≥0∞`. -/
noncomputable
def exp : EReal → ℝ≥0∞
  | ⊥ => 0
  | ⊤ => ∞
  | (x : ℝ) => ENNReal.ofReal (Real.exp x)

@[simp] lemma exp_bot : exp ⊥ = 0 := rfl
@[simp] lemma exp_zero : exp 0 = 1 := by simp [exp]
@[simp] lemma exp_top : exp ⊤ = ∞ := rfl
@[simp] lemma exp_coe (x : ℝ) : exp x = ENNReal.ofReal (Real.exp x) := rfl

@[simp] lemma exp_eq_zero_iff {x : EReal} : exp x = 0 ↔ x = ⊥ := by
  induction x using EReal.rec <;> simp [Real.exp_pos]

@[simp] lemma exp_eq_top_iff {x : EReal} : exp x = ∞ ↔ x = ⊤ := by
  induction x using EReal.rec <;> simp

end Definition

/-! ### Monotonicity -/
section Monotonicity

lemma exp_strictMono : StrictMono exp := by
  intro x y h
  induction x using EReal.rec
  · rw [exp_bot, pos_iff_ne_zero, ne_eq, exp_eq_zero_iff]
    exact h.ne'
  · induction' y using EReal.rec with y
    · simp at h
    · simp_rw [exp_coe]
      exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨Real.exp_lt_exp_of_lt (mod_cast h), Real.exp_pos y⟩
    · simp
  · exact (not_top_lt h).elim

lemma exp_monotone : Monotone exp := exp_strictMono.monotone

end Monotonicity

/-! ### Algebraic properties -/

section Morphism

lemma exp_neg (x : EReal) : exp (-x) = (exp x)⁻¹ := by
  induction x using EReal.rec
  · simp
  · rw [exp_coe, ← EReal.coe_neg, exp_coe, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
      Real.exp_neg]
  · simp

lemma exp_add (x y : EReal) : exp (x + y) = exp x * exp y := by
  induction x using EReal.rec
  · simp
  · induction y using EReal.rec
    · simp
    · simp only [← EReal.coe_add, exp_coe]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), Real.exp_add]
    · simp only [EReal.coe_add_top, exp_top, exp_coe]
      rw [ENNReal.mul_top]
      simp [Real.exp_pos]
  · induction y using EReal.rec
    · simp
    · simp only [EReal.top_add_coe, exp_top, exp_coe]
      rw [ENNReal.top_mul]
      simp [Real.exp_pos]
    · simp

end Morphism

end ENNReal

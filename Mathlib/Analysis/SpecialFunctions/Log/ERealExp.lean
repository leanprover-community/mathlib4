/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.EReal.Basic

/-!
# Extended Nonnegative Real Exponential

We define `exp` as an extension of the exponential of a real
to the extended reals `EReal`. The function takes values
in the extended nonnegative reals `ℝ≥0∞`, with `exp ⊥ = 0` and `exp ⊤ = ⊤`.

## Main Definitions
- `EReal.exp`: The extension of the real exponential to `EReal`.

## Main Results
- `EReal.exp_strictMono`: `exp` is increasing;
- `EReal.exp_neg`, `EReal.exp_add`: `exp` satisfies
the identities `exp (-x) = (exp x)⁻¹` and `exp (x + y) = exp x * exp y`.

## Tags
ENNReal, EReal, exponential
-/
namespace EReal

open scoped ENNReal

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
  induction x <;> simp [Real.exp_pos]

@[simp] lemma exp_eq_top_iff {x : EReal} : exp x = ∞ ↔ x = ⊤ := by
  induction x <;> simp

end Definition

/-! ### Monotonicity -/
section Monotonicity

@[gcongr]
lemma exp_strictMono : StrictMono exp := by
  intro x y h
  induction x
  · rw [exp_bot, pos_iff_ne_zero, ne_eq, exp_eq_zero_iff]
    exact h.ne'
  · induction y
    · simp at h
    · simp_rw [exp_coe]
      exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨Real.exp_strictMono (mod_cast h), Real.exp_pos _⟩
    · simp
  · exact (not_top_lt h).elim

@[gcongr]
lemma exp_monotone : Monotone exp := exp_strictMono.monotone

@[simp] lemma exp_lt_exp_iff {a b : EReal} : exp a < exp b ↔ a < b := exp_strictMono.lt_iff_lt

@[simp] lemma zero_lt_exp_iff {a : EReal} : 0 < exp a ↔ ⊥ < a := exp_bot ▸ @exp_lt_exp_iff ⊥ a

@[simp] lemma exp_lt_top_iff {a : EReal} : exp a < ⊤ ↔ a < ⊤ := exp_top ▸ @exp_lt_exp_iff a ⊤

@[simp] lemma exp_lt_one_iff {a : EReal} : exp a < 1 ↔ a < 0 := exp_zero ▸ @exp_lt_exp_iff a 0

@[simp] lemma one_lt_exp_iff {a : EReal} : 1 < exp a ↔ 0 < a := exp_zero ▸ @exp_lt_exp_iff 0 a

@[simp] lemma exp_le_exp_iff {a b : EReal} : exp a ≤ exp b ↔ a ≤ b := exp_strictMono.le_iff_le

@[simp] lemma exp_le_one_iff {a : EReal} : exp a ≤ 1 ↔ a ≤ 0 := exp_zero ▸ @exp_le_exp_iff a 0

@[simp] lemma one_le_exp_iff {a : EReal} : 1 ≤ exp a ↔ 0 ≤ a := exp_zero ▸ @exp_le_exp_iff 0 a

@[deprecated exp_monotone (since := "2025-10-20")]
lemma exp_le_exp {a b : EReal} (h : a ≤ b) : exp a ≤ exp b := by simpa

@[deprecated exp_strictMono (since := "2025-10-20")]
lemma exp_lt_exp {a b : EReal} (h : a < b) : exp a < exp b := by simpa

end Monotonicity

/-! ### Algebraic properties -/

section Morphism

lemma exp_neg (x : EReal) : exp (-x) = (exp x)⁻¹ := by
  induction x
  · simp
  · rw [exp_coe, ← EReal.coe_neg, exp_coe, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
      Real.exp_neg]
  · simp

lemma exp_add (x y : EReal) : exp (x + y) = exp x * exp y := by
  induction x
  · simp
  · induction y
    · simp
    · simp only [← EReal.coe_add, exp_coe]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), Real.exp_add]
    · simp only [EReal.coe_add_top, exp_top, exp_coe]
      rw [ENNReal.mul_top]
      simp [Real.exp_pos]
  · induction y
    · simp
    · simp only [EReal.top_add_coe, exp_top, exp_coe]
      rw [ENNReal.top_mul]
      simp [Real.exp_pos]
    · simp

end Morphism

end EReal

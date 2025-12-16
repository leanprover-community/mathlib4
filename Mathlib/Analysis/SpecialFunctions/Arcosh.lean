/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Inverse of the cosh function

In this file we define an inverse of cosh as a function from [0, ∞) to [1, ∞).

## Main definitions

- `Real.arcosh`: An inverse function of `Real.cosh` as a function from [0, ∞) to [1, ∞).

- `Real.coshPartialEquiv`: `Real.cosh` as a `PartialEquiv`.

## Main Results

- `Real.cosh_arcosh`, `Real.arcosh_cosh`: cosh and arcosh are inverse in the appropriate domains.

## Tags

arcosh, arccosh, argcosh, acosh
-/

@[expose] public section


noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `arcosh` is defined using a logarithm, `arcosh x = log (x + √(x ^ 2 - 1))`. -/
@[pp_nodot]
def arcosh (x : ℝ) :=
  log (x + √(x ^ 2 - 1))

theorem exp_arcosh {x : ℝ} (hx : 1 ≤ x) : exp (arcosh x) = x + √(x ^ 2 - 1) := by
  apply exp_log
  positivity

@[simp]
theorem arcosh_zero : arcosh 1 = 0 := by simp [arcosh]

lemma add_sqrt_self_sq_sub_one_inv {x : ℝ} (hx : 1 ≤ x) :
    (x + √(x ^ 2 - 1))⁻¹ = x - √(x ^ 2 - 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_two_sub_pow_two, sq_sqrt (sub_nonneg_of_le (one_le_pow₀ hx)), sub_sub_cancel]

/-- `arcosh` is the right inverse of `cosh` over [1, ∞). -/
theorem cosh_arcosh {x : ℝ} (hx : 1 ≤ x) : cosh (arcosh x) = x := by
  rw [arcosh, cosh_eq, exp_neg, exp_log (by positivity), add_sqrt_self_sq_sub_one_inv hx]
  ring

theorem arcosh_eq_zero_iff {x : ℝ} (hx : 1 ≤ x) : arcosh x = 0 ↔ x = 1 := by
  rw [← exp_injective.eq_iff, exp_arcosh hx, exp_zero]
  grind

theorem sinh_arcosh {x : ℝ} (hx : 1 ≤ x) : sinh (arcosh x) = √(x ^ 2 - 1) := by
  rw [arcosh, sinh_eq, exp_neg, exp_log (by positivity), add_sqrt_self_sq_sub_one_inv hx]
  ring

theorem tanh_arcosh {x : ℝ} (hx : 1 ≤ x) : tanh (arcosh x) = √(x ^ 2 - 1) / x := by
  rw [tanh_eq_sinh_div_cosh, sinh_arcosh hx, cosh_arcosh hx]

/-- `arcosh` is the left inverse of `cosh` over [0, ∞). -/
theorem arcosh_cosh {x : ℝ} (hx : 0 ≤ x) : arcosh (cosh x) = x := by
rw [arcosh, ← exp_eq_exp, exp_log (by positivity), ← eq_sub_iff_add_eq', exp_sub_cosh,
    ← sq_eq_sq₀ (sqrt_nonneg _) (sinh_nonneg_iff.mpr hx), ← sinh_sq, sq_sqrt (pow_two_nonneg _)]

theorem arcosh_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ arcosh x := by
  apply log_nonneg
  calc
    1 ≤ x + 0 := by simpa
    _ ≤ x + √(x ^ 2 - 1) := by gcongr; positivity

theorem arcosh_pos {x : ℝ} (hx : 1 < x) : 0 < arcosh x := by
  apply log_pos
  calc
    1 < x + 0 := by simpa
    _ ≤ x + √(x ^ 2 - 1) := by gcongr; positivity

/-- This holds for `Ioi 0` instead of only `Ici 1` due to junk values. -/
theorem strictMonoOn_arcosh : StrictMonoOn arcosh (Ioi 0) := by
  refine strictMonoOn_log.comp ?_ fun x (hx : 0 < x) ↦ show 0 < x + √(x ^ 2 - 1) by positivity
  exact strictMonoOn_id.add_monotone fun x (hx : 0 < x) y (hy : 0 < y) hxy ↦ by gcongr

/-- This holds for `0 < x, y ≤ 1` due to junk values. -/
theorem arcosh_le_arcosh {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : arcosh x ≤ arcosh y ↔ x ≤ y :=
  strictMonoOn_arcosh.le_iff_le hx hy

/-- This holds for `0 < x, y ≤ 1` due to junk values. -/
theorem arcosh_lt_arcosh {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : arcosh x < arcosh y ↔ x < y :=
  strictMonoOn_arcosh.lt_iff_lt hx hy

/-- `Real.cosh` as a `PartialEquiv`. -/
def coshPartialEquiv : PartialEquiv ℝ ℝ where
  toFun := cosh
  invFun := arcosh
  source := Ici 0
  target := Ici 1
  map_source' r _ := one_le_cosh r
  map_target' _ hr := arcosh_nonneg hr
  left_inv' _ hr := arcosh_cosh hr
  right_inv' _ hr := cosh_arcosh hr

end Real

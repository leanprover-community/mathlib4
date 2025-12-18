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

- `Real.coshPartialEquiv`: `Real.cosh` and `Real.arcosh` bundled as a `PartialEquiv`
  from [0, ∞) to [1, ∞).

- `Real.coshOpenPartialHomeomorph`: `Real.cosh` as an `OpenPartialHomeomorph` from (0, ∞) to (1, ∞).

## Main Results

- `Real.cosh_arcosh`, `Real.arcosh_cosh`: cosh and arcosh are inverse in the appropriate domains.

- `Real.cosh_bijOn`, `Real.cosh_injOn`, `Real.cosh_surjOn`: `Real.cosh` is bijective, injective and
  surjective as a function from [0, ∞) to [1, ∞)

- `Real.arcosh_bijOn`, `Real.arcosh_injOn`, `Real.arcosh_surjOn`: `Real.arcosh` is bijective,
  injective and surjective as a function from [1, ∞) to [0, ∞)

- `Real.continuousOn_arcosh`: arcosh is continuous on [1, ∞)

- `Real.differentiableOn_arcosh`, `Real.contDiffOn_arcosh`: `Real.arcosh` is
  differentiable, and continuously differentiable on (1, ∞)

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

/-- `Real.cosh` as a `PartialEquiv` from [0, ∞) to [1, ∞). -/
def coshPartialEquiv : PartialEquiv ℝ ℝ where
  toFun := cosh
  invFun := arcosh
  source := Ici 0
  target := Ici 1
  map_source' r _ := one_le_cosh r
  map_target' _ hr := arcosh_nonneg hr
  left_inv' _ hr := arcosh_cosh hr
  right_inv' _ hr := cosh_arcosh hr

theorem continuousOn_arcosh : ContinuousOn arcosh (Ici 1) :=
  have {x : ℝ} (hx : x ∈ Ici 1) : 0 < x + √(x ^ 2 - 1) :=
    add_pos_of_pos_of_nonneg (show 0 < x by grind) (sqrt_nonneg _)
  continuousOn_log.comp (Continuous.continuousOn (by continuity)) (by grind [MapsTo])

/-- `Real.cosh` as an `OpenPartialHomemorph` from (0, ∞) to (1, ∞). -/
def coshOpenPartialHomeomorph : OpenPartialHomeomorph ℝ ℝ where
  toFun := cosh
  invFun := arcosh
  source := Ioi 0
  target := Ioi 1
  map_source' _ hr := one_lt_cosh.mpr (ne_of_lt hr).symm
  map_target' _ hr := arcosh_pos hr
  left_inv' _ hr := arcosh_cosh (le_of_lt hr)
  right_inv' _ hr := cosh_arcosh (le_of_lt hr)
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
  continuousOn_toFun := continuous_cosh.continuousOn
  continuousOn_invFun := continuousOn_arcosh.mono Ioi_subset_Ici_self

theorem hasStrictDerivAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) :
    HasStrictDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x := by
  rw [← sinh_arcosh (le_of_lt hx)]
  refine coshOpenPartialHomeomorph.hasStrictDerivAt_symm hx ?_ (hasStrictDerivAt_cosh _)
  rw [ne_eq, sinh_eq_zero]
  exact ne_of_gt (arcosh_pos hx)

theorem hasDerivAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) : HasDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x :=
  (hasStrictDerivAt_arcosh hx).hasDerivAt

theorem differentiableAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) : DifferentiableAt ℝ arcosh x :=
  (hasDerivAt_arcosh hx).differentiableAt

theorem differentiableOn_arcosh : DifferentiableOn ℝ arcosh (Ioi 1) := fun _ hx =>
  (differentiableAt_arcosh hx).differentiableWithinAt

theorem contDiffAt_arcosh {n : WithTop ℕ∞} {x : ℝ} (hx : x ∈ Ioi 1) : ContDiffAt ℝ n arcosh x := by
  refine coshOpenPartialHomeomorph.contDiffAt_symm_deriv ?_ hx (hasDerivAt_cosh _)
    contDiff_cosh.contDiffAt
  rw [ne_eq, sinh_eq_zero]
  exact (arcosh_pos hx).ne'

theorem contDiffOn_arcosh {n : WithTop ℕ∞} : ContDiffOn ℝ n arcosh (Ioi 1) := fun _ hx =>
  (contDiffAt_arcosh hx).contDiffWithinAt

/-- The function `Real.arcosh` is real analytic. -/
@[fun_prop]
lemma analyticAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) : AnalyticAt ℝ arcosh x :=
  (contDiffAt_arcosh hx).analyticAt

/-- The function `Real.arcosh` is real analytic. -/
lemma analyticWithinAt_arcosh {s : Set ℝ} {x : ℝ} (hx : x ∈ Ioi 1) :
    AnalyticWithinAt ℝ arcosh s x :=
  (contDiffAt_arcosh hx).contDiffWithinAt.analyticWithinAt

/-- The function `Real.arcosh` is real analytic. -/
theorem analyticOnNhd_arcosh {s : Set ℝ} (hs : s ⊆ Ioi 1) : AnalyticOnNhd ℝ arcosh s :=
  fun _ hx ↦ analyticAt_arcosh (hs hx)

/-- The function `Real.arcosh` is real analytic. -/
lemma analyticOn_arcosh {s : Set ℝ} (hs : s ⊆ Ioi 1) : AnalyticOn ℝ arcosh s :=
  contDiffOn_arcosh.analyticOn.mono hs

theorem cosh_bijOn : BijOn cosh (Ici 0) (Ici 1) := coshPartialEquiv.bijOn

theorem cosh_injOn : InjOn cosh (Ici 0) := coshPartialEquiv.injOn

theorem cosh_surjOn : SurjOn cosh (Ici 0) (Ici 1) := coshPartialEquiv.surjOn

theorem arcosh_bijOn : BijOn arcosh (Ici 1) (Ici 0) := coshPartialEquiv.symm.bijOn

theorem arcosh_injOn : InjOn arcosh (Ici 1) := coshPartialEquiv.symm.injOn

theorem arcosh_surjOn : SurjOn arcosh (Ici 1) (Ici 0) := coshPartialEquiv.symm.surjOn

end Real

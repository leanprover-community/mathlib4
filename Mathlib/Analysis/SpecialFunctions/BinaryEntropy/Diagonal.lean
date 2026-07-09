/-
Copyright (c) 2026 John Erlbacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Erlbacher
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Real.Sqrt

/-!
# Diagonal reduction for the binary entropy function

The main result is the two-variable entropy inequality of Chase and Lovett
([chaseLovett2022], Lemma 2.2): for `x, y ∈ [0, 1]`,

  `x * binEntropy y + y * binEntropy x ≤ 2 * sqrt (x * y) * binEntropy (sqrt (x * y))`,

i.e. the symmetrized expression on the left is dominated by its diagonal value at the
geometric mean. This reduces two-variable inequalities of Boppana type
(`K * (x * h y + y * h x) ≤ h (x * y)`, see [boppana2023]) to one-variable
inequalities `2 * K * t * h t ≤ h (t ^ 2)`; such inequalities drive the entropic
lower bounds for Frankl's union-closed sets conjecture
(Gilmer, Alweiss–Huang–Sellke, Chase–Lovett, Sawin).

## Proof idea

Substituting `x = exp (-u)`, the inequality becomes midpoint concavity of
`η u = exp u * negMulLog (1 - exp (-u))` on `[0, ∞)`: the `negMulLog (x * y)` parts of
the two sides agree exactly, and the remaining `negMulLog (1 - ·)` parts transfer to `η`
via the identity `x * η (-log x) = negMulLog (1 - x)`. Concavity of `η` reduces, after
computing two derivatives, to the elementary bound `log t ≤ t - 1`. Stating `η` through
`negMulLog` absorbs the `0 * log 0` boundary behaviour at `u = 0`, so no separate
edge-case argument is needed at `x = 1`.

## Main declarations

* `Real.mul_negMulLog_one_sub_add_le`: the `negMulLog (1 - ·)` half of the reduction.
* `Real.mul_binEntropy_add_mul_binEntropy_le`: the Chase–Lovett diagonal reduction.

## References

* [Z. Chase, S. Lovett, *Approximate union-closed sets conjecture*][chaseLovett2022]
* [R. Boppana, *A useful inequality for the binary entropy function*][boppana2023]

## Tags

binary entropy, union-closed sets, entropy inequality
-/

public section

namespace Real

/-! ### The comparison function `η` and its concavity -/

/-- Comparison function for the diagonal reduction:
`η u = exp u * negMulLog (1 - exp (-u))` (`= -(exp u - 1) * log (1 - exp (-u))` for
`u > 0`, continuously extended by `η 0 = 0`). -/
private noncomputable def eta (u : ℝ) : ℝ := exp u * negMulLog (1 - exp (-u))

/-- `η` is continuous (the `negMulLog` form absorbs the `0 * log 0` boundary). -/
private lemma continuous_eta : Continuous eta :=
  continuous_exp.mul
    (continuous_negMulLog.comp (continuous_const.sub (continuous_exp.comp continuous_neg)))

private lemma one_sub_exp_neg_pos {u : ℝ} (hu : 0 < u) : 0 < 1 - exp (-u) := by
  have h : exp (-u) < exp 0 := exp_lt_exp.mpr (by linarith)
  rw [exp_zero] at h
  linarith

/-- Derivative of the inner function `w ↦ 1 - exp (-w)`. -/
private lemma hasDerivAt_inner (u : ℝ) :
    HasDerivAt (fun w : ℝ => 1 - exp (-w)) (exp (-u)) u := by
  simpa [Function.comp_def] using
    ((hasDerivAt_exp (-u)).comp u ((hasDerivAt_id u).neg)).const_sub 1

/-- `η' u = -exp u * log (1 - exp (-u)) - 1` for `u > 0`. -/
private lemma hasDerivAt_eta {u : ℝ} (hu : 0 < u) :
    HasDerivAt eta (-exp u * log (1 - exp (-u)) - 1) u := by
  have hz := one_sub_exp_neg_pos hu
  have hcomp : HasDerivAt (fun w : ℝ => negMulLog (1 - exp (-w)))
      ((-log (1 - exp (-u)) - 1) * exp (-u)) u := by
    simpa [Function.comp_def] using
      (hasDerivAt_negMulLog hz.ne').comp u (hasDerivAt_inner u)
  have he : exp u * exp (-u) = 1 := by rw [← exp_add]; simp
  have hval : exp u * negMulLog (1 - exp (-u))
      + exp u * ((-log (1 - exp (-u)) - 1) * exp (-u))
      = -exp u * log (1 - exp (-u)) - 1 := by
    simp only [negMulLog_def]
    linear_combination -he
  have hprod := (hasDerivAt_exp u).mul hcomp
  rw [hval] at hprod
  exact hprod

/-- `η'' u = -exp u * log (1 - exp (-u)) - 1 / (1 - exp (-u))` for `u > 0`. -/
private lemma hasDerivAt_eta' {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun w : ℝ => -exp w * log (1 - exp (-w)) - 1)
      (-exp u * log (1 - exp (-u)) - 1 / (1 - exp (-u))) u := by
  have hz := one_sub_exp_neg_pos hu
  have hlog : HasDerivAt (fun w : ℝ => log (1 - exp (-w)))
      (exp (-u) / (1 - exp (-u))) u := (hasDerivAt_inner u).log hz.ne'
  have hneg : HasDerivAt (fun w : ℝ => -exp w) (-exp u) u :=
    (hasDerivAt_exp u).neg
  have he : exp u * exp (-u) = 1 := by rw [← exp_add]; simp
  have hval : -exp u * log (1 - exp (-u)) + -exp u * (exp (-u) / (1 - exp (-u)))
      = -exp u * log (1 - exp (-u)) - 1 / (1 - exp (-u)) := by
    have h1 : exp u * (exp (-u) / (1 - exp (-u))) = 1 / (1 - exp (-u)) := by
      rw [← mul_div_assoc, he]
    linarith
  have hprod := (hneg.mul hlog).sub_const 1
  rw [hval] at hprod
  exact hprod

/-- `η'' ≤ 0` on `(0, ∞)` — equivalent to the elementary bound `log t ≤ t - 1`. -/
private lemma eta''_nonpos {u : ℝ} (hu : 0 < u) :
    -exp u * log (1 - exp (-u)) - 1 / (1 - exp (-u)) ≤ 0 := by
  have hw0 : 0 < 1 - exp (-u) := one_sub_exp_neg_pos hu
  have hkey : -log (1 - exp (-u)) ≤ (1 - exp (-u))⁻¹ - 1 := by
    have h := log_le_sub_one_of_pos (inv_pos.2 hw0)
    rwa [log_inv] at h
  have hE : exp u * exp (-u) = 1 := by rw [← exp_add]; simp
  rw [sub_nonpos, le_div_iff₀ hw0]
  have h4 : (-log (1 - exp (-u))) * (exp u * (1 - exp (-u)))
      ≤ ((1 - exp (-u))⁻¹ - 1) * (exp u * (1 - exp (-u))) :=
    mul_le_mul_of_nonneg_right hkey (by positivity)
  have h5 : ((1 - exp (-u))⁻¹ - 1) * (exp u * (1 - exp (-u)))
      = exp u * exp (-u) := by
    field_simp
    ring
  calc -exp u * log (1 - exp (-u)) * (1 - exp (-u))
      = (-log (1 - exp (-u))) * (exp u * (1 - exp (-u))) := by ring
    _ ≤ exp u * exp (-u) := by rw [← h5]; exact h4
    _ = 1 := hE

/-- `η` is concave on `[0, ∞)`. -/
private lemma concaveOn_eta : ConcaveOn ℝ (Set.Ici (0 : ℝ)) eta := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 0)
    (f' := fun u => -exp u * log (1 - exp (-u)) - 1)
    (f'' := fun u => -exp u * log (1 - exp (-u)) - 1 / (1 - exp (-u)))
    continuous_eta.continuousOn (fun u hu => ?_) (fun u hu => ?_) (fun u hu => ?_) <;>
    rw [interior_Ici] at hu
  · exact (hasDerivAt_eta hu).hasDerivWithinAt
  · exact (hasDerivAt_eta' hu).hasDerivWithinAt
  · exact eta''_nonpos hu

/-- Midpoint form of the concavity of `η`. -/
private lemma eta_add_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    eta u + eta v ≤ 2 * eta ((u + v) / 2) := by
  have h := concaveOn_eta.2 (Set.mem_Ici.2 hu) (Set.mem_Ici.2 hv)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have harg : (1 / 2 : ℝ) * u + (1 / 2 : ℝ) * v = (u + v) / 2 := by ring
  rw [harg] at h
  linarith

/-- The transfer identity `x * η (-log x) = negMulLog (1 - x)` for `x > 0`. -/
private lemma mul_eta_neg_log {x : ℝ} (hx : 0 < x) :
    x * eta (-log x) = negMulLog (1 - x) := by
  unfold eta
  rw [neg_neg, exp_log hx, exp_neg, exp_log hx]
  rw [← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]

/-! ### The diagonal reduction -/

/-- The `negMulLog (1 - ·)` half of the diagonal reduction: for `x, y ∈ (0, 1]`,
`x * negMulLog (1 - y) + y * negMulLog (1 - x)
  ≤ 2 * sqrt (x * y) * negMulLog (1 - sqrt (x * y))`. -/
theorem mul_negMulLog_one_sub_add_le {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1) :
    x * negMulLog (1 - y) + y * negMulLog (1 - x)
      ≤ 2 * sqrt (x * y) * negMulLog (1 - sqrt (x * y)) := by
  have hu : 0 ≤ -log x := neg_nonneg.2 (log_nonpos hx0.le hx1)
  have hv : 0 ≤ -log y := neg_nonneg.2 (log_nonpos hy0.le hy1)
  have hxy : 0 < x * y := mul_pos hx0 hy0
  have hs0 : 0 < sqrt (x * y) := sqrt_pos.2 hxy
  have hslog : -log (sqrt (x * y)) = (-log x + -log y) / 2 := by
    rw [log_sqrt hxy.le, log_mul hx0.ne' hy0.ne']
    ring
  have hmid := eta_add_le hu hv
  have h1 : x * y * (eta (-log x) + eta (-log y))
      ≤ x * y * (2 * eta ((-log x + -log y) / 2)) :=
    mul_le_mul_of_nonneg_left hmid hxy.le
  have hA : x * y * eta (-log x) = y * negMulLog (1 - x) := by
    have hid := mul_eta_neg_log hx0
    calc x * y * eta (-log x) = y * (x * eta (-log x)) := by ring
      _ = y * negMulLog (1 - x) := by rw [hid]
  have hB : x * y * eta (-log y) = x * negMulLog (1 - y) := by
    have hid := mul_eta_neg_log hy0
    calc x * y * eta (-log y) = x * (y * eta (-log y)) := by ring
      _ = x * negMulLog (1 - y) := by rw [hid]
  have hC : x * y * (2 * eta ((-log x + -log y) / 2))
      = 2 * sqrt (x * y) * negMulLog (1 - sqrt (x * y)) := by
    have hid := mul_eta_neg_log hs0
    rw [hslog] at hid
    have hss : sqrt (x * y) * sqrt (x * y) = x * y := mul_self_sqrt hxy.le
    linear_combination (-2 : ℝ) * eta ((-log x + -log y) / 2) * hss
      + 2 * sqrt (x * y) * hid
  rw [mul_add, hA, hB, hC] at h1
  linarith

/-- **The Chase–Lovett diagonal reduction** ([chaseLovett2022], Lemma 2.2): for
`x, y ∈ [0, 1]`,
`x * binEntropy y + y * binEntropy x ≤ 2 * sqrt (x * y) * binEntropy (sqrt (x * y))`.
The symmetrized two-variable expression is dominated by its value on the diagonal at the
geometric mean. -/
theorem mul_binEntropy_add_mul_binEntropy_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    x * binEntropy y + y * binEntropy x
      ≤ 2 * sqrt (x * y) * binEntropy (sqrt (x * y)) := by
  rcases eq_or_lt_of_le hx0 with rfl | hx0'
  · simp
  rcases eq_or_lt_of_le hy0 with rfl | hy0'
  · simp
  have hxy : 0 < x * y := mul_pos hx0' hy0'
  have hpsi := mul_negMulLog_one_sub_add_le hx0' hx1 hy0' hy1
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hlogpart : x * negMulLog y + y * negMulLog x
      = 2 * sqrt (x * y) * negMulLog (sqrt (x * y)) := by
    have hss : sqrt (x * y) * sqrt (x * y) = x * y := mul_self_sqrt hxy.le
    unfold negMulLog
    rw [log_sqrt hxy.le, log_mul hx0'.ne' hy0'.ne']
    linear_combination (log x + log y) * hss
  nlinarith [hpsi, hlogpart]

end Real

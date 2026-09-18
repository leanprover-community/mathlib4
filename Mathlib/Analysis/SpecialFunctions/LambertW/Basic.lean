/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The complex Lambert W function

This file defines the branches of the standard Lambert W function, i.e. the multivalued inverse of
`w ↦ w * exp w`, and proves `W_ k` is a bijection from `domain k` onto `range k`.

If `w = W_ k z`, then `z = w * cexp w`. We follow standard usage and say that `z` is in the z-plane
and `w` is in the w-plane.

The boundary of the range of the Lambert W function is described by
`{ w | w.arg + w.im = (2 * k ± 1) * π }`,
with the special case that, when `k = ±1`, the part of the negative real axis `(-∞, -1]`
is also part of the boundary.
So we define the range using a corrected version of
`{ w | w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) }`.

## Main definitions

* `Complex.LambertW.domain k`: the domain of the `k`-th branch in the z-plane.
* `Complex.LambertW.range k`: the range of the `k`-th branch in the w-plane.
* `Complex.LambertW.index hw`: the unique index of the branch containing `w ≠ -1`.
* `Complex.lambertW k`: the `k`-th branch `W_ k` of the Lambert W function.

## Main results

* `Complex.LambertW.existsUnique_mem_range_mul_exp_eq`: every point in the domain of a branch has a
  unique preimage in its range.
* `Complex.LambertW.bijOn_mul_exp_range_domain`:
  `w ↦ w * cexp w` is a bijection from `range k` to `domain k`.
* `Complex.lambertW_mul_exp_of_mem_range`:
  `W_ k (w * cexp w) = w` for `w ∈ range k`.
* `Complex.lambertW_mul_exp_lambertW_of_mem_domain`:
  `W_ k z * cexp (W_ k z) = z` for `z ∈ domain k`.
* `Complex.eq_mul_exp_iff_exists_eq_lambertW`: `z = w * cexp w` if and only if `w = W_ k z` for
  some branch `k` with `z ∈ domain k`.
* `Complex.eq_index_of_mem_lambertW`: the branch index in the previous statement is
  unique whenever `w ≠ -1`.

## Notation

The following notation is localized in `ComplexLambertW`:

* `W_ k` is `Complex.lambertW k`.
* `W₀` is the principal branch `W_ 0`.
* `W₋₁` is `W_ (-1)`.

Use `open scoped ComplexLambertW` to use these.

## Implementation notes

To describe the range of the Lambert W function, `Set.Ioc` is not sufficient, since `w.arg + w.im`
takes the value `π` on the entire negative real axis. Therefore, we use a special-case definition
for the range.

To prove the bijectivity of `w ↦ w * exp w`, we first handle seven basic cases and then
combine them to obtain the cases `k = 0`, `k = -1`, and `k ≠ 0, -1`,
from which the general result follows.

The seven basic cases are:
* `w = 0` ↔ `z = 0`, the trivial case
* `w ∈ [-1, 0)` ↔ `z ∈ [-1 / e, 0)`, `W₀` on ℝ
* `w.arg + w.im = π ∧ w.im > 0`, where `z ∈ (-∞, -1 / e)`, the upper boundary of range of `W₀`
* `w ∈ (-∞, -1]` ↔ `z ∈ [-1 / e, 0)`, `W₋₁` on ℝ
* `w.arg + w.im = -π`, where `z ∈ (-∞, -1 / e)`, the lower boundary of range of `W₀`
* `w.arg + w.im = (2 * k + 1) * π ∧ k ≠ 0, -1` ↔ `z ∈ (-∞, 0)`, with `w` on the
  boundary of the range
* `w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π) ∧ w ≠ 0 ∧ k ≠ 0, -1` ↔
  `z ∈ Complex.slitPlane`, with `w` in the interior of range

For the last two cases, to prove the existence and uniqueness of `w`, we solve the polar equations.
We have `w * exp w = z` ↔ `w + log w = log z + k * (2 * π) * I`.
Let `w = ρ * exp (ϕ * I)`. Taking real and imaginary parts gives
`ρ * exp (ρ * cos ϕ) = ‖z‖` and `ϕ + ρ * sin ϕ = z.arg + k * (2 * π)`.
We therefore define the two auxiliary functions `solutionNormWAux` and `solutionNormZAux`
and prove that `solutionNormZAux` is strictly antitone with the limits needed for
the intermediate value theorem.

## References

* [R. M. Corless, G. H. Gonnet, D. E. G. Hare, D. J. Jeffrey and D. E. Knuth, *On the Lambert W
  function*][corless1996]
* <https://en.wikipedia.org/wiki/Lambert_W_function>
* <https://dlmf.nist.gov/4.13>

## TODO

+ Define the Lambert W function over ℝ
+ Prove some identities and some special values
+ Prove continuity, differentiability, analyticity
+ Prove asymptotic expansion and series expansion
+ Prove tree counting and combinatorics
+ Prove indefinite integral formulas

## Tags

Lambert W, inverse function, bijective
-/

noncomputable section

section LambertWAux

namespace Real

open Filter Topology Set

variable {x : ℝ}

theorem existsUnique_mem_Ico_mul_exp_eq_of_mem_Ico (hx : x ∈ Ico (-(rexp 1)⁻¹) 0) :
    ∃! t ∈ Ico (-1) 0, t * rexp t = x := by
  obtain ⟨t, ht, hteq⟩ : ∃ t ∈ Icc (-1) 0, t * rexp t = x :=
    intermediate_value_Icc (by norm_num) (by fun_prop) ⟨by grind [exp_neg], by simpa using hx.2.le⟩
  exact ⟨t, ⟨⟨ht.left, by grind⟩, hteq⟩, fun y hy => exp_injective (mul_log_strictMonoOn.injOn
    (exp_le_exp.mpr hy.left.left) (exp_le_exp.mpr ht.left) (by grind [log_exp]))⟩

-- TODO : refer to `Real.lambertWNegOne`
public theorem existsUnique_mem_Iic_mul_exp_eq_of_mem_Ico (hx : x ∈ Ico (-(rexp 1)⁻¹) 0) :
    ∃! t ∈ Iic (-1), t * rexp t = x := by
  -- `Iic (-1)` is unbounded, so first pick `S` with `t * rexp t < x` for all `t ≥ S`,
  -- then apply the IVT on `[-(S ⊔ 1), -1]`
  obtain ⟨S, hS⟩ : ∃ S, ∀ b ≥ S, b ^ 1 * rexp (-b) < -x :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 |>.eventually <|
      eventually_lt_nhds <| neg_pos_of_neg hx.right).exists_forall_of_atTop
  obtain ⟨t, ht, hteq⟩ : ∃ t ∈ Icc (-(S ⊔ 1)) (-1), t * rexp t = x :=
    intermediate_value_Icc' (by simp) (by fun_prop)
      ⟨by grind [exp_neg], by grind [hS (S ⊔ 1), pow_one, exp_neg]⟩
  exact ⟨t, ⟨ht.2, hteq⟩, fun y hy => exp_injective <| mul_log_strictAntiOn.injOn
    ⟨exp_nonneg y, exp_le_exp.mpr hy.left⟩ ⟨exp_nonneg t, exp_le_exp.mpr ht.right⟩
      (by grind [log_exp])⟩

theorem existsUnique_nonneg_mul_exp_eq_of_nonneg (hx : 0 ≤ x) :
    ∃! t ≥ 0, t * rexp t = x := by
  obtain ⟨t, ht, hteq⟩ : ∃ t ∈ Icc 0 (x + 1), t * rexp t = x :=
    intermediate_value_Icc (by positivity) (by fun_prop)
      ⟨by simpa, by nlinarith [one_le_exp (show 0 ≤ x + 1 by positivity)]⟩
  exact ⟨t, ⟨ht.1, hteq⟩, fun u hu => exp_injective (mul_log_strictMonoOn.injOn
    (exp_le_exp.mpr (by linarith [hu.1])) (exp_le_exp.mpr (by linarith [ht.1]))
    (by rw [log_exp, log_exp, mul_comm (exp u) u, hu.2, mul_comm (exp t) t, ← hteq]))⟩

end Real

namespace Complex

open Real Set

open scoped ComplexConjugate

variable {x y z w : ℂ} {i : ℤ}

theorem mem_slitPlane_of_notMem (hz : z ≠ 0) (hz' : z ∉ Iio 0 ×ℂ {0}) :
    z ∈ Complex.slitPlane := by
  contrapose! hz
  simp [mem_reProdIm, mem_slitPlane_iff] at hz hz'
  apply Complex.ext ?_ hz.right
  grind [zero_re]

theorem arg_add_im_eq_pi_of_arg_eq_pi (h : x.arg = π) : x.arg + x.im = π := by
  simpa [(arg_eq_pi_iff.mp h).right]

theorem arg_add_im_of_mem (hw : w ∈ Iic (-1) ×ℂ {0}) : w.arg + w.im = π :=
  arg_add_im_eq_pi_of_arg_eq_pi <| arg_eq_pi_iff.mpr ⟨hw.left.trans_lt neg_one_lt_zero, hw.right⟩

theorem arg_pos_of_arg_add_im_pos (h : 0 < w.arg + w.im) : 0 < w.arg := by
  rcases lt_trichotomy w.arg 0 with h | h | h
  · linarith [arg_neg_iff.mp h]
  · linarith [arg_eq_zero_iff.mp h |>.right]
  · exact h

theorem arg_mem_Ioo_of_arg_add_im_pos (hw : w ≠ 0)
    (harg : w.arg ≠ π) (hA : 0 < w.arg + w.im) : w.arg ∈ Ioo 0 (min (w.arg + w.im) π) := by
  replace harg : w.arg < π := lt_of_le_of_ne (arg_le_pi w) harg
  have harg₀ : 0 < w.arg := arg_pos_of_arg_add_im_pos hA
  refine ⟨harg₀, lt_min ?_ harg⟩
  nlinarith [norm_mul_sin_arg w, Real.sin_pos_of_pos_of_lt_pi harg₀ harg, norm_pos_iff.mpr hw]

theorem add_log_im : (x + x.log).im = x.arg + x.im := by
  simp [log, add_comm]

theorem arg_mul_exp_eq_of_mem (hx : x ≠ 0)
    (h : x.arg + x.im ∈ Ioc ((2 * i - 1) * π) ((2 * i + 1) * π)) :
    (x * cexp x).arg = x.arg + x.im - i * (2 * π) := by
  rw [← exp_log hx, ← exp_add, mul_comm, arg_exp, add_im, log_im, toIocMod_eq_iff, exp_log hx]
  exact ⟨by grind [h.left, h.right, Real.pi_pos], i, by ring⟩

theorem mul_exp_mem_of_arg_add_im_eq
    (hw : w.arg + w.im ∈ Ioc ((2 * i - 1) * π) ((2 * i + 1) * π))
    (hz : w * cexp w ∈ Iio 0 ×ℂ {0}) : w.arg + w.im = (2 * i + 1) * π := by
  grind [arg_mul_exp_eq_of_mem (fun h => by simp [h, mem_reProdIm] at hz) hw, arg_eq_pi_iff.mpr hz]

theorem mul_exp_eq_of_arg_add_im_eq (hx : x ≠ 0) (h : x.arg + x.im = (2 * i + 1) * π) :
    x * cexp x = -rexp (x + log x).re := by
  nth_rw 1 [← exp_log hx, ← exp_add, ← add_comm]
  apply Complex.ext
  · rw [exp_re, add_log_im, h, add_mul, one_mul, mul_comm (2 : ℝ), mul_assoc]
    rw_mod_cast [Real.cos_int_mul_two_pi_add_pi i]
    rw [mul_neg_one]
  · rw_mod_cast [exp_im, add_log_im, h, Real.sin_int_mul_pi (2 * i + 1), mul_zero]

/-- If `w.arg + w.im = π` and `w * exp w ∈ [-(exp 1)⁻¹, 0)`, then `w` is real. -/
theorem im_eq_zero_of_arg_add_im_eq_pi_of_mul_exp_mem {w : ℂ}
    (hw1 : w.arg + w.im = π) (hw2 : w * cexp w ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) : w.im = 0 := by
  obtain ⟨hzre1, hzre2⟩ : (w * cexp w).re ∈ Ico (-(rexp 1)⁻¹) 0 := hw2.left
  have hw₀ : w ≠ 0 := fun hw => by simp [hw] at hzre2
  by_contra nh
  -- if `w.im ≠ 0`, we can get `0 < w.im < π` and calculating the norm of
  -- `z` gives `‖w * cexp w‖ = w.im / sin w.im * rexp (-w.im * cot w.im)`
  -- which is strictly greater than `(rexp 1)⁻¹`, contradicting `hw2`.
  -- the proof below shows `- w.im * cot w.im + log (w.im / sin w.im) > -1 + 0` instead.
  obtain ⟨nh, harg⟩ : 0 < w.im ∧ w.im = π - w.arg := by grind [arg_le_pi w]
  have hnormsin : ‖w‖ * Real.sin w.im = w.im := by simp [norm_mul_sin_arg, harg]
  have hsin : 0 < Real.sin w.im := by nlinarith [hnormsin, norm_pos_iff.mpr hw₀]
  have hnorm : ‖w‖ = w.im / Real.sin w.im := by rwa [eq_div_iff hsin.ne']
  have hnormcos : ‖w‖ * -Real.cos w.im = w.re := by simp [norm_mul_cos_arg, harg]
  have him1 : w.im < π := by
    by_contra! hc
    have : Real.sin (w.im - 2 * π) ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by linarith [neg_pi_lt_arg w]) (by linarith)
    grind [Real.sin_sub_two_pi]
  have him2 : w.im * Real.cos w.im < Real.sin w.im := by
    rcases lt_or_ge w.im (π / 2) with h | h
    · have hc : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h⟩
      simpa [Real.tan_eq_sin_div_cos, hc.ne'] using mul_lt_mul_of_pos_right (Real.lt_tan nh h) hc
    · grw [Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [pi_pos]), mul_zero, hsin]
  have H : -1 < (w + log w).re := by
    rw [add_re, log_re, ← hnormcos, hnorm]
    have h1 : -1 < -(w.im * Real.cos w.im / Real.sin w.im) :=
      neg_lt_neg <| div_lt_one hsin |>.mpr him2
    have h2 : 0 < Real.log ‖w‖ :=
      Real.log_pos (by simpa [hnorm, one_lt_div hsin] using Real.sin_lt nh)
    linear_combination (norm := (field_simp; ring_nf)) h1 + h2
    nth_rw 3 [← hnormsin]
    field_simp
    ring_nf
    rfl
  rw [mul_exp_eq_of_arg_add_im_eq (i := 0) hw₀ (by grind), neg_re, ofReal_re,
    ← Real.exp_neg, neg_le_neg_iff] at hzre1
  exact False.elim <| H.not_ge <| Real.exp_le_exp.mp hzre1

theorem im_eq_zero_of_arg_add_im_eq_neg_pi_of_mul_exp_mem
    (hw1 : w.arg + w.im = -π) (hw2 : w * cexp w ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) : w.im = 0 := by
  rw [← neg_eq_zero, ← conj_im]
  apply im_eq_zero_of_arg_add_im_eq_pi_of_mul_exp_mem ?_ ?_
  · rw [conj_im, arg_conj, ite_eq_right (by grind [pi_pos, arg_eq_pi_iff]), ← neg_add, hw1, neg_neg]
  · simp_all [mem_reProdIm, exp_conj, ← map_mul]

end Complex

section Solve

open Real Complex ComplexConjugate Set Filter Topology

variable {ρ θ ϕ : ℝ}

namespace Real

theorem tendsto_div_sin_nhdsGT_zero :
    Tendsto (fun u : ℝ => u / sin u) (𝓝[>] 0) (𝓝 1) := by
  have : Tendsto (slope sin 0) (𝓝[>] 0) (𝓝 (cos 0)) :=
    (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_sin 0)).mono_left (nhdsGT_le_nhdsNE 0)
  simpa [slope_fun_def_field, cos_zero, inv_div] using this.inv₀ (by simp)

theorem tendsto_mul_exp_neg_div_two_atTop :
    Tendsto (fun r : ℝ => r * rexp (-r / 2)) atTop (𝓝 0) := by
  convert (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 |>.comp <|
    tendsto_id.atTop_div_const zero_lt_two).const_mul 2 using 2 <;> simp [field]

/-- The aux function to solve polar equation; its output represents the norm of `w`. -/
def LambertW.solutionNormWAux (θ : ℝ) : ℝ -> ℝ := fun ϕ => (θ - ϕ) / sin ϕ

/-- The aux function to solve polar equation; its output represents the norm of `z`. -/
def LambertW.solutionNormZAux (θ : ℝ) : ℝ -> ℝ := fun ϕ =>
  solutionNormWAux θ ϕ * rexp (solutionNormWAux θ ϕ * cos ϕ)

theorem LambertW.sin_pos_of_mem_Ioo_inf_pi (hϕ : ϕ ∈ Ioo 0 (θ ⊓ π)) : 0 < sin ϕ :=
  sin_pos_of_pos_of_lt_pi hϕ.1 <| hϕ.2.trans_le inf_le_right

theorem LambertW.continuousOn_solutionNormWAux {s : Set ℝ} (hs : ∀ x ∈ s, sin x ≠ 0) :
    ContinuousOn (solutionNormWAux θ) s :=
  continuous_const.sub continuous_id |>.continuousOn |>.div continuous_sin.continuousOn hs

theorem LambertW.continuousOn_solutionNormZAux {s : Set ℝ} (hs : ∀ x ∈ s, sin x ≠ 0) :
    ContinuousOn (solutionNormZAux θ) s :=
  letI h1 := continuousOn_solutionNormWAux hs
  h1.mul (h1.mul continuous_cos.continuousOn).rexp

theorem LambertW.hasDerivAt_solutionNormWAux (θ : ℝ) (hs : sin ϕ ≠ 0) :
    HasDerivAt (solutionNormWAux θ) (-(sin ϕ + (θ - ϕ) * cos ϕ) / sin ϕ ^ 2) ϕ := by
  refine hasDerivAt_id ϕ |>.const_sub θ |>.div (hasDerivAt_sin ϕ) hs |>.congr_deriv ?_
  simp only [id_eq, field, neg_add, SubNegMonoid.sub_eq_add_neg]

theorem LambertW.deriv_solutionNormWAux {ϕ : ℝ} (hs : sin ϕ ≠ 0) :
    deriv (solutionNormWAux θ) ϕ = -(sin ϕ + (θ - ϕ) * cos ϕ) / sin ϕ ^ 2 :=
  hasDerivAt_solutionNormWAux θ hs |>.deriv

theorem LambertW.deriv_solutionNormZAux_neg {ϕ : ℝ} (hϕ : ϕ ∈ Ioo 0 (θ ⊓ π)) :
    deriv (solutionNormZAux θ) ϕ < 0 := by
  have hs₀ : 0 < sin ϕ := sin_pos_of_mem_Ioo_inf_pi hϕ
  have : DifferentiableAt ℝ (solutionNormWAux θ) ϕ :=
    (hasDerivAt_solutionNormWAux θ hs₀.ne').differentiableAt
  have hderiv : deriv (solutionNormZAux θ) ϕ = -rexp (solutionNormWAux θ ϕ * cos ϕ) *
      ((sin ϕ + (θ - ϕ) * cos ϕ) ^ 2 / sin ϕ ^ 3 + (θ - ϕ) ^ 2 / sin ϕ) := by
    unfold solutionNormZAux
    rw [deriv_fun_mul this (by fun_prop), _root_.deriv_exp (by fun_prop),
      deriv_fun_mul (by fun_prop) differentiableAt_cos, deriv_cos,
      deriv_solutionNormWAux hs₀.ne',
      ← div_mul_cancel₀ (solutionNormWAux θ ϕ) hs₀.ne', solutionNormWAux]
    field_simp
    ring
  rw [hderiv, neg_mul, Left.neg_neg_iff]
  have hθϕ : 0 < θ - ϕ := sub_pos.mpr <| hϕ.right.trans_le inf_le_left
  positivity

theorem LambertW.strictAntiOn_solutionNormZAux :
    StrictAntiOn (solutionNormZAux θ) (Ioo 0 (θ ⊓ π)) :=
  strictAntiOn_of_deriv_neg (convex_Ioo 0 (θ ⊓ π))
    (continuousOn_solutionNormZAux fun _ hx => sin_pos_of_mem_Ioo_inf_pi hx |>.ne')
    fun _ hϕ => deriv_solutionNormZAux_neg (by rwa [interior_Ioo] at hϕ)

theorem LambertW.injOn_solutionNormZAux (θ : ℝ) :
    InjOn (solutionNormZAux θ) (Ioo 0 (θ ⊓ π)) :=
  strictAntiOn_solutionNormZAux.injOn

theorem LambertW.tendsto_solutionNormWAux_nhdsGT_zero (hθ : 0 < θ) :
    Tendsto (solutionNormWAux θ) (𝓝[>] 0) atTop :=
  continuous_const.sub continuous_id |>.tendsto 0 |>.mono_left nhdsWithin_le_nhds
    |>.pos_mul_atTop (sub_pos.mpr hθ) <| tendsto_inv_nhdsGT_zero.comp tendsto_sin_nhdsGT_zero

theorem LambertW.tendsto_solutionNormWAux_nhdsLT_pi (hθ : π < θ) :
    Tendsto (solutionNormWAux θ) (𝓝[<] π) atTop :=
  continuous_const.sub continuous_id |>.tendsto π |>.mono_left nhdsWithin_le_nhds
    |>.pos_mul_atTop (sub_pos.mpr hθ) <| tendsto_inv_nhdsGT_zero.comp tendsto_sin_nhdsLT_pi

theorem LambertW.tendsto_solutionNormWAux_pi_nhdsLT_pi :
    Tendsto (solutionNormWAux π) (𝓝[<] π) (𝓝 1) := by
  unfold solutionNormWAux
  have : Tendsto (fun ϕ : ℝ => π - ϕ) (𝓝[<] π) (𝓝[>] 0) :=
    sub_self π ▸ le_of_eq (Filter.map_subLeft_nhdsLT (c := π) (a := π))
  simpa [Function.comp_def] using tendsto_div_sin_nhdsGT_zero.comp this

theorem LambertW.tendsto_solutionNormZAux_nhdsGT_zero (hθ : 0 < θ) :
    Tendsto (solutionNormZAux θ) (𝓝[>] 0) atTop := by
  refine tendsto_atTop_mono' (𝓝[>] 0) ?_ <| tendsto_solutionNormWAux_nhdsGT_zero hθ
  filter_upwards [Ioo_mem_nhdsGT (a := θ ⊓ (π / 2)) (by grind [pi_pos])] with ϕ hϕ
  have hrϕ : 0 ≤ solutionNormWAux θ ϕ := div_nonneg (by grind) (by grind [sin_pos_of_pos_of_lt_pi])
  exact le_mul_of_one_le_right hrϕ <| one_le_exp <| mul_nonneg hrϕ <|
    cos_pos_of_mem_Ioo ⟨by grind [pi_pos], hϕ.right.trans_le inf_le_right⟩ |>.le

theorem LambertW.tendsto_solutionNormZAux_nhdsLT_self (hθ1 : 0 < θ) (hθ2 : θ < π) :
    Tendsto (solutionNormZAux θ) (𝓝[<] θ) (𝓝 0) := by
  have : ContinuousAt (solutionNormZAux θ) θ := by
    unfold solutionNormZAux solutionNormWAux
    fun_prop (disch := exact sin_pos_of_pos_of_lt_pi hθ1 hθ2 |>.ne')
  simpa [solutionNormZAux, solutionNormWAux] using this.tendsto.mono_left nhdsWithin_le_nhds

theorem LambertW.tendsto_solutionNormZAux_nhdsLT_pi (hθ : π < θ) :
    Tendsto (solutionNormZAux θ) (𝓝[<] π) (𝓝 0) := by
  apply squeeze_zero' (g := fun ϕ => solutionNormWAux θ ϕ * rexp (-(solutionNormWAux θ ϕ) / 2))
  · filter_upwards [Ioo_mem_nhdsLT pi_pos] with x hx using
      mul_nonneg (div_nonneg (by grind) (by grind [sin_pos_of_pos_of_lt_pi])) (exp_nonneg _)
  · -- On `(π - π / 3, π)` we have `cos ϕ ≤ cos (π - π / 3) = -(1 / 2)`;
    -- the point is written as `π - π / 3` (not `2 / 3 * π`) so that `cos_pi_sub` applies.
    filter_upwards [Ioo_mem_nhdsLT (a := π - π / 3) (by grind [pi_pos])] with ϕ hϕ
    have hr : 0 ≤ solutionNormWAux θ ϕ := div_nonneg (by grind [hϕ.right]) <| le_of_lt <|
      sin_pos_of_pos_of_lt_pi (by grind [pi_pos, hϕ.left]) hϕ.right
    have hcos : cos ϕ ≤ -(1 / 2) := by
      grw [cos_le_cos_of_nonneg_of_le_pi (by grind) hϕ.right.le hϕ.left.le,
        cos_pi_sub, cos_pi_div_three]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith)) hr
  · exact tendsto_mul_exp_neg_div_two_atTop.comp (tendsto_solutionNormWAux_nhdsLT_pi hθ)

theorem LambertW.tendsto_solutionNormZAux_nhdsLT_inf_pi (hθ1 : θ ≠ π) (hθ2 : 0 < θ) :
    Tendsto (solutionNormZAux θ) (𝓝[<] (θ ⊓ π)) (𝓝 0) := by
  rcases le_or_gt π θ with hθ' | hθ'
  · rw [min_eq_right hθ']
    exact tendsto_solutionNormZAux_nhdsLT_pi <| lt_of_le_of_ne hθ' <| Ne.symm hθ1
  · simpa [min_eq_left_of_lt hθ'] using tendsto_solutionNormZAux_nhdsLT_self hθ2 hθ'

theorem LambertW.tendsto_solutionNormZAux_pi_nhdsLT_pi :
    Tendsto (solutionNormZAux π) (𝓝[<] π) (𝓝 (rexp 1)⁻¹) := by
  unfold solutionNormZAux
  simpa [exp_neg] using tendsto_solutionNormWAux_pi_nhdsLT_pi.mul <|
    continuous_exp.tendsto (1 * -1) |>.comp <| tendsto_solutionNormWAux_pi_nhdsLT_pi.mul <|
      tendsto_nhds_of_tendsto_nhdsWithin tendsto_cos_nhdsLT_pi

theorem LambertW.existsUnique_solutionNormZAux_pi (hρ : (rexp 1)⁻¹ < ρ) :
    ∃! ϕ ∈ Ioo 0 π, solutionNormZAux π ϕ = ρ := by
  obtain ⟨φ, hφ, hφρ⟩ : ∃ φ ∈ Ioo 0 π, solutionNormZAux π φ = ρ :=
    isPreconnected_Ioo.intermediate_value_Ioi
      (le_principal_iff.mpr (Ioo_mem_nhdsLT pi_pos)) (le_principal_iff.mpr (Ioo_mem_nhdsGT pi_pos))
      (continuousOn_solutionNormZAux fun x hx => sin_pos_of_mem_Ioo hx |>.ne')
      tendsto_solutionNormZAux_pi_nhdsLT_pi (tendsto_solutionNormZAux_nhdsGT_zero pi_pos) hρ
  exact ⟨φ, ⟨hφ, hφρ⟩, fun φ' hφ' => (min_self π ▸ injOn_solutionNormZAux π)
    hφ'.left hφ (hφ'.right.trans hφρ.symm)⟩

theorem LambertW.existsUnique_solutionNormZAux (hθ1 : θ ≠ π) (hθ2 : 0 < θ) (hρ : 0 < ρ) :
    ∃! ϕ ∈ Ioo 0 (θ ⊓ π), solutionNormZAux θ ϕ = ρ := by
  obtain ⟨ϕ, hϕ⟩ : ∃ ϕ ∈ Ioo 0 (min θ π), solutionNormZAux θ ϕ = ρ :=
    isPreconnected_Ioo.intermediate_value_Ioi
      (le_principal_iff.mpr <| Ioo_mem_nhdsLT <| lt_min hθ2 pi_pos)
      (le_principal_iff.mpr <| Ioo_mem_nhdsGT <| lt_min hθ2 pi_pos)
      (continuousOn_solutionNormZAux fun x hx => sin_pos_of_mem_Ioo_inf_pi hx |>.ne')
      (tendsto_solutionNormZAux_nhdsLT_inf_pi hθ1 hθ2) (tendsto_solutionNormZAux_nhdsGT_zero hθ2) hρ
  exact ⟨ϕ, hϕ, fun _ hϕ' => by grind [injOn_solutionNormZAux θ, InjOn]⟩

end Real

namespace Complex

theorem arg_mul_exp_ofReal_mul_I (hρ : 0 < ρ) (hϕ : ϕ ∈ Ioc (-π) π) :
    ((ρ : ℂ) * cexp (ϕ * I)).arg = ϕ := by
  grind [arg_real_mul _ hρ, arg_exp_mul_I, toIocMod_eq_self]

theorem LambertW.existsUnique_aux (hθ : 0 < θ) (hρ : 0 < ρ)
    (H : ∃! ϕ ∈ Ioo 0 (θ ⊓ π), (θ - ϕ) / Real.sin ϕ *
      rexp ((θ - ϕ) / Real.sin ϕ * Real.cos ϕ) = ρ) :
    ∃! w : ℂ, (w.arg ≠ π ∧ w.arg + w.im = θ) ∧ w * cexp w = ρ * cexp (θ * I) := by
  set r : ℝ → ℝ := fun ϕ => (θ - ϕ) / Real.sin ϕ with hr
  obtain ⟨ϕ, ⟨hϕ, hrρ⟩, Huniq⟩ := H
  have hsin : ∀ ϕ ∈ Ioo 0 (θ ⊓ π), 0 < Real.sin ϕ := fun _ hϕ =>
    Real.sin_pos_of_pos_of_lt_pi hϕ.left <| hϕ.right.trans_le inf_le_right
  have hsϕ : 0 < Real.sin ϕ := hsin ϕ hϕ
  have hϕπ : ϕ < π := hϕ.2.trans_le inf_le_right
  have hrsin : r ϕ * Real.sin ϕ = θ - ϕ := div_mul_cancel₀ _ hsϕ.ne'
  have hr₀ : 0 < r ϕ := div_pos (by linarith [hϕ.2.trans_le (inf_le_left (a := θ) (b := π))]) hsϕ
  have hϕ : ϕ ∈ Ioc (-π) π := ⟨by linarith [pi_pos, hϕ.left], hϕπ.le⟩
  refine ⟨r ϕ * cexp (ϕ * I),
    ⟨⟨by simpa only [arg_mul_exp_ofReal_mul_I hr₀ hϕ] using hϕπ.ne, ?_⟩, ?_⟩, ?_⟩
  · rw [arg_mul_exp_ofReal_mul_I hr₀ hϕ, mul_im, ofReal_im, zero_mul, add_zero,
      exp_ofReal_mul_I_im, ofReal_re, hrsin, add_sub_cancel]
  · calc
      _ = ↑(r ϕ * rexp (r ϕ * Real.cos ϕ)) * cexp (↑(ϕ + r ϕ * Real.sin ϕ) * I) := by
        nth_rw 2 [exp_mul_I]
        simp [mul_add, exp_add, ofReal_add, add_mul, exp_add, field, mul_assoc]
      _ = ρ * cexp (θ * I) := by grind
  · rintro w' ⟨⟨hne, hw'θ⟩, hw'ρ⟩
    have hw'₀ : w' ≠ 0 := fun nh =>
      mul_ne_zero (ofReal_ne_zero.mpr hρ.ne') (exp_ne_zero _) <| by rw [← hw'ρ, nh, zero_mul]
    have hargmem : w'.arg ∈ Ioo 0 (θ ⊓ π) :=
      hw'θ ▸ arg_mem_Ioo_of_arg_add_im_pos hw'₀ hne (hw'θ ▸ hθ)
    have hw'r : ‖w'‖ = r w'.arg := by
      rwa [hr, eq_div_iff (hsin _ hargmem).ne', norm_mul_sin_arg w', eq_sub_iff_add_eq']
    have hρ' : r w'.arg * rexp (r w'.arg * Real.cos w'.arg) = ρ := by
      apply congrArg norm at hw'ρ
      rw [norm_mul, norm_exp, ← norm_mul_cos_arg, hw'r] at hw'ρ
      simpa [norm_exp, norm_real, abs_of_pos hρ] using hw'ρ
    rw [← norm_mul_exp_arg_mul_I w', hw'r, Huniq w'.arg ⟨hargmem, hρ'⟩]

theorem LambertW.existsUnique_arg_add_im_eq_of_pos (hθ1 : θ ≠ π) (hθ2 : 0 < θ)
    (hρ : 0 < ρ) : ∃! w : ℂ, w.arg + w.im = θ ∧ w * cexp w = ρ * cexp (θ * I) := by
  refine (existsUnique_congr fun w => and_congr_left fun _ =>
    and_iff_right_of_imp fun h1 h => ?_).mp <| LambertW.existsUnique_aux hθ2 hρ <|
      Real.LambertW.existsUnique_solutionNormZAux hθ1 hθ2 hρ
  exact hθ1 <| h1 ▸ arg_add_im_eq_pi_of_arg_eq_pi h

theorem LambertW.existsUnique_arg_add_im_eq_pi (hρ : (rexp 1)⁻¹ < ρ) :
    ∃! w : ℂ, w.arg + w.im = π ∧ w * cexp w = ρ * cexp (π * I) ∧ w.im > 0 := by
  refine (existsUnique_congr fun w => ⟨fun ⟨⟨hne, h1⟩, h2⟩ => ?_, fun ⟨h1, h2, h3⟩ => ?_⟩).mp <|
    existsUnique_aux pi_pos (inv_pos.mpr (Real.exp_pos 1) |>.trans hρ) <|
      (min_self π).symm ▸ Real.LambertW.existsUnique_solutionNormZAux_pi hρ
  · exact ⟨h1, h2, by grind [arg_le_pi]⟩
  · exact ⟨⟨by grind, h1⟩, h2⟩

theorem LambertW.existsUnique_arg_add_im_eq (hθ1 : θ ≠ π) (hθ2 : θ ≠ -π) (hρ : 0 < ρ) :
    ∃! w : ℂ, w.arg + w.im = θ ∧ w * cexp w = ρ * cexp (θ * I) := by
  rcases lt_trichotomy θ 0 with hθ' | rfl | hθ'
  · obtain ⟨w, ⟨hw1, hw2⟩, H⟩ : ∃! w : ℂ, w.arg + w.im = -θ ∧ w * cexp w = ρ * cexp (↑(-θ) * I) :=
      existsUnique_arg_add_im_eq_of_pos (θ := -θ) (by grind) (by linarith) hρ
    refine ⟨conj w, ⟨?_, ?_⟩, ?_⟩
    · simp [arg_conj, show w.arg ≠ π by grind [arg_eq_pi_iff], ← neg_add, hw1]
    · rw [exp_conj, ← map_mul, hw2, map_mul, conj_ofReal,
        ← exp_conj, map_mul, conj_I, conj_ofReal, ofReal_neg, neg_mul_neg]
    · intro w' ⟨hw'ϕ, hw'ρ⟩
      have hw'ϕ1 : w'.arg ≠ π := by grind [arg_add_im_eq_pi_of_arg_eq_pi]
      specialize H (conj w') ⟨?_, ?_⟩
      · simp [arg_conj, hw'ϕ1, ← hw'ϕ, add_comm]
      · simp [← map_mul, hw'ρ]
        simp [← exp_conj, conj_ofReal, conj_I]
      rw [← H, conj_conj]
  · rw [ofReal_zero, zero_mul, exp_zero, mul_one]
    obtain ⟨x, hx, H⟩ : ∃! t ≥ 0, t * rexp t = ρ := existsUnique_nonneg_mul_exp_eq_of_nonneg hρ.le
    refine ⟨x, ⟨by simp [arg_eq_zero_iff, hx.left.le],
      Complex.ext (by simp [exp_ofReal_re, hx]) (by simp)⟩, fun x' ⟨hx'1, hx'2⟩ => ?_⟩
    have him : x'.im = 0 := by grind [arg_neg_iff]
    rw [Complex.ext (z := x') (w := x'.re) rfl him] at hx'2 ⊢
    rw [← ofReal_exp, ← ofReal_mul, ofReal_inj] at hx'2
    have : 0 < x'.re := by grind [arg_eq_zero_iff]
    rw [H x'.re ⟨this.le, hx'2⟩]
  · exact existsUnique_arg_add_im_eq_of_pos hθ1 hθ' hρ

end Complex

end Solve

end LambertWAux

namespace Complex

open Real Set Filter Topology

open scoped ComplexConjugate

variable {k : ℤ} {z w : ℂ}

namespace LambertW

section LambertWRangeDomain

section Definition

/-- The domain of the `k`-th branch of the Lambert W function: the whole plane for the principal
branch `k = 0`, and the punctured plane for other branches. -/
@[expose]
public def domain (k : ℤ) : Set ℂ :=
  if k = 0 then univ else {0}ᶜ

@[simp]
public theorem domain_zero : domain 0 = univ := rfl

public theorem domain_of_ne_zero (hk : k ≠ 0) : domain k = {0}ᶜ := ite_eq_right hk

/-- The range of the `k`-th branch of the Lambert W function, i.e., the set of points `w` in
the w-plane whose image `w * exp w` in the z-plane lies in the domain of this branch.

For `k ≠ 0, -1` it consists of the `w` with
`w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π)`.
The two exceptional branches are corrected on the negative real axis:
`range 0` omits `Iio (-1) ×ℂ {0}` while
`range (-1)` adds `Iic (-1) ×ℂ {0}`.

To visualize this, one can use
```mathematica
ContourPlot[y + Arg[x + y I], {x, -20, 20}, {y, -20, 20},
 Contours -> Function[{min, max}, Range[Floor[min / (2 * Pi)] * 2 * Pi - Pi, max + Pi, 2 * Pi]],
 ContourLabels -> Function[{x, y, z}, Text[Framed[Floor[z / Pi]], {x, y}, Background -> White]]]
```
-/
@[expose]
public def range (k : ℤ) : Set ℂ := match k with
  | 0 => {w | w.arg + w.im ∈ Ioc (-π) π} \ Iio (-1) ×ℂ {0}
  | -1 => {w | w.arg + w.im ∈ Ioc (-3 * π) (-π)} ∪ Iic (-1) ×ℂ {0}
  | _ => {w | w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π)}

end Definition

section RangeAndDomain

public theorem mem_domain_zero : z ∈ domain 0 := trivial

public theorem mem_domain_of_ne_zero (hz : z ≠ 0) : z ∈ domain k :=
  em (k = 0) |>.elim (fun hk => hk ▸ trivial) (fun hk => domain_of_ne_zero hk ▸ hz)

public theorem mem_range_zero_iff :
    w ∈ range 0 ↔ w.arg + w.im ∈ Ioc (-π) π ∧ ¬(w.re < -1 ∧ w.im = 0) := by
  simp [range, mem_reProdIm]

public theorem mem_range_neg_one_iff :
    w ∈ range (-1) ↔ w.arg + w.im ∈ Ioc (-3 * π) (-π) ∨ (w.re ≤ -1 ∧ w.im = 0) := by
  simp [range, mem_reProdIm]

public theorem mem_range_iff_of_ne (hk : k ≠ 0) (hk' : k ≠ -1) :
    w ∈ range k ↔ w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) := by
  simp [range]

public theorem zero_mem_range_zero : 0 ∈ range 0 := by
  simp [mem_range_zero_iff, pi_pos, pi_nonneg]

public theorem zero_notMem_range_neg_one : 0 ∉ range (-1) := by simp [range, mem_reProdIm]

public theorem zero_notMem_range (hk : k ≠ 0) : 0 ∉ range k := by
  by_cases hk' : k = -1
  · exact hk' ▸ zero_notMem_range_neg_one
  rw [mem_range_iff_of_ne hk hk', arg_zero, zero_im, add_zero, ← zero_mul π]
  simp [field, -zero_mul]
  norm_cast
  omega

public theorem ne_zero_of_mem_range (hk : k ≠ 0) (hz : z ∈ range k) : z ≠ 0 := fun nh =>
  False.elim <| zero_notMem_range hk <| nh ▸ hz

@[simp]
public theorem zero_mem_range_iff : 0 ∈ range k ↔ k = 0 := by
  grind [zero_notMem_range, zero_mem_range_zero]

@[simp]
public theorem neg_one_mem_range_neg_one : -1 ∈ range (-1) := by
  simp [mem_range_neg_one_iff]

@[simp]
public theorem neg_one_mem_range_zero : -1 ∈ range 0 := by
  simp [mem_range_zero_iff, pi_pos]

theorem mem_range_iff_of_mem (hw : w ∈ Iic (-1) ×ℂ {0}) :
    w ∈ range k ↔ k = -1 ∨ (k = 0 ∧ w.re = -1) := by
  simp only [mem_reProdIm, mem_Iic, mem_singleton_iff] at hw
  constructor
  · intro h
    rcases (show k = 0 ∨ k = -1 ∨ (k ≠ 0 ∧ k ≠ -1) by tauto) with rfl | rfl | ⟨hk, hk'⟩
    · grind [mem_range_zero_iff]
    · exact Or.inl rfl
    · rw [mem_range_iff_of_ne hk hk', arg_add_im_of_mem hw] at h
      simp [field] at h
      norm_cast at h
      omega
  · rintro (rfl | ⟨rfl, hre⟩)
    · exact mem_range_neg_one_iff.mpr (Or.inr ⟨hw.1, hw.2⟩)
    · exact mem_range_zero_iff.mpr <| by grind [arg_add_im_of_mem hw, pi_pos]

theorem mem_range_iff_of_notMem (hw : w ∉ Iic (-1) ×ℂ {0}) :
    w ∈ range k ↔ w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) := by
  rcases (show k = 0 ∨ k = -1 ∨ (k ≠ 0 ∧ k ≠ -1) by tauto) with rfl | rfl | ⟨hk, hk'⟩
  · grind [mem_reProdIm, mem_range_zero_iff]
  · grind [mem_reProdIm, mem_range_neg_one_iff]
  · exact mem_range_iff_of_ne hk hk'

public theorem iUnion_range : ⋃ k, range k = univ := by
  refine eq_univ_iff_forall.mpr fun w => mem_iUnion.mpr ?_
  by_cases hw : w ∈ Iic (-1) ×ℂ {0}
  · use -1, Or.inr hw
  · refine ⟨toIocDiv two_pi_pos (-π) (w.arg + w.im), mem_range_iff_of_notMem hw |>.mpr ?_⟩
    grind [sub_toIocDiv_zsmul_mem_Ioc two_pi_pos (-π) (w.arg + w.im)]

theorem eq_of_mem_range_of_mem_range {i j : ℤ}
    (hi : w ∈ range i) (hj : w ∈ range j) (hw : w ≠ -1) : i = j := by
  by_cases hw' : w ∈ Iic (-1) ×ℂ {0}
  · have hre : w.re ≠ -1 := fun hre => hw (Complex.ext hre (by simpa using hw'.right))
    grind [mem_range_iff_of_mem hw']
  · rw [mem_range_iff_of_notMem hw'] at hi hj
    have := toIocDiv_eq_iff two_pi_pos (a := -π) (b := w.arg + w.im) (n := i) |>.mpr
    have := toIocDiv_eq_iff two_pi_pos (a := -π) (b := w.arg + w.im) (n := j) |>.mpr
    grind

/-- See also `Complex.LambertW.index`. -/
public theorem existsUnique_mem_range_of_ne_neg_one (hw : w ≠ -1) :
    ∃! k : ℤ, w ∈ range k := by
  obtain ⟨k, hk⟩ : ∃ k, w ∈ range k := mem_iUnion.mp <| eq_univ_iff_forall.mp iUnion_range w
  exact ⟨k, hk, fun k' hk' => eq_of_mem_range_of_mem_range hk' hk hw⟩

end RangeAndDomain

theorem arg_add_im_mem_Ioo_of_mem_range_zero_of_mul_exp_mem
    (hw : w ∈ range 0) (hz : w * cexp w ∈ Complex.slitPlane) :
    w.arg + w.im ∈ Ioo (-π) π := by
  refine ⟨hw.left.left, lt_of_le_of_ne hw.left.right
    fun nh => mem_slitPlane_iff_arg.mp hz |>.left ?_⟩
  grind [arg_mul_exp_eq_of_mem (x := w) (i := 0) (by aesop) (by simpa using hw.left)]

theorem arg_add_im_eq_pi_of_mem_range_zero
    (hw1 : w ∈ range 0) (hz : w * cexp w ∈ Iio 0 ×ℂ {0}) :
    w.arg + w.im = π := by
  grind [mul_exp_mem_of_arg_add_im_eq (w := w) (i := 0) (by simpa using hw1.left)]

theorem im_pos_of_arg_add_im_eq_pi_of_mul_exp_mem
    (hw2 : w.arg + w.im = π) (hz : w * cexp w ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    0 < w.im := by
  apply lt_of_le_of_ne <| arg_nonneg_iff.mp <| le_of_lt <| arg_pos_of_arg_add_im_pos <| hw2 ▸ pi_pos
  intro nh
  rw [← nh, add_zero, arg_eq_pi_iff] at hw2
  simp only [mem_reProdIm, mem_Iio, mem_singleton_iff] at hz
  exact hz.left.not_ge (by simpa [nh.symm, exp_re] using neg_exp_one_inv_le_mul_exp w.re)

theorem mem_of_mem_range_zero_of_mul_exp_mem
    (hw1 : w ∈ range 0) (hw2 : w.arg + w.im = π) (hz : w * cexp w ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    w ∈ Ico (-1) 0 ×ℂ {0} := by
  have : w.im = 0 := im_eq_zero_of_arg_add_im_eq_pi_of_mul_exp_mem hw2 hz
  rw [this, add_zero, arg_eq_pi_iff] at hw2
  exact ⟨⟨by simpa [hw2, mem_reProdIm] using hw1.right, hw2.left⟩, this⟩

theorem arg_add_im_mem_Ioo_of_mem_range_neg_one_of_mul_exp_notMem
    (hw : w ∈ range (-1)) (hz : w * cexp w ∉ Iio 0 ×ℂ {0}) :
    w.arg + w.im ∈ Ioo (-3 * π) (-π) := by
  replace hw : w.arg + w.im ∈ Ioc (-3 * π) (-π) := by
    apply mem_range_neg_one_iff.mp hw |>.resolve_right fun nh => hz ?_
    simp [mem_reProdIm, exp_re, exp_im, nh.right, mul_neg_iff, Real.exp_pos w.re, LT.lt.not_gt]
    grind
  refine ⟨hw.left, lt_of_le_of_ne hw.right fun nh => ?_⟩
  have : (w * cexp w).arg = w.arg + w.im - ↑(-1 : ℤ) * (2 * π) :=
    arg_mul_exp_eq_of_mem (x := w) (i := -1) (fun nh => by simp [nh, pi_pos.not_ge] at hw)
      (by simp [nh, field]; norm_num)
  rw [nh] at this
  conv_rhs at this => ring_nf
  exact hz <| arg_eq_pi_iff.mp this

theorem arg_add_im_mem_Ioc_of_mem_range_neg_one_of_mul_exp_mem
    (hw : w ∈ range (-1)) (hz : w * cexp w ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    w.arg + w.im ∈ Ioc (-3 * π) (-π) :=
  mem_range_neg_one_iff.mp hw |>.resolve_right fun nh => absurd hz.left <|
    by simp [exp_im, exp_re, nh, neg_exp_one_inv_le_mul_exp]

theorem mem_Iic_of_mem_range_neg_one_of_mul_exp_mem
    (hw : w ∈ range (-1)) (hz : w * cexp w ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    w ∈ Iic (-1) ×ℂ {0} := mem_range_neg_one_iff.mp hw |>.resolve_left fun nh => by
  have : (w * cexp w).arg = w.arg + w.im - ↑(-1 : ℤ) * (2 * π) :=
    arg_mul_exp_eq_of_mem (x := w) (i := -1)
    (fun nh => by simp [mem_reProdIm, nh] at hz) (by grind)
  rw [arg_eq_pi_iff (z := w * cexp w) |>.mpr <| by grind [mem_reProdIm.mp hz]] at this
  replace : w.im = 0 := im_eq_zero_of_arg_add_im_eq_neg_pi_of_mul_exp_mem (by grind) hz
  grind [arg_mem_Ioc]

--  The seven basic cases (without the trivial one).

theorem existsUnique_eq_pi_mul_exp_eq (hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = π ∧ w * cexp w = z ∧ w.im > 0 := by
  have hzre : z.re < 0 := hz.left.trans <| neg_lt_zero.mpr <| by positivity
  have hρ : (rexp 1)⁻¹ < ‖z‖ := by
    simpa [norm_eq_sqrt_sq_add_sq, show z.im = 0 from hz.right,
      sqrt_sq_eq_abs, abs_of_neg hzre, lt_neg] using hz.left
  have hz' : z = ‖z‖ * cexp (π * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z, arg_eq_pi_iff.mpr ⟨hzre, hz.right⟩]
  obtain ⟨w, ⟨hw, hwz⟩, H⟩ : ∃! w : ℂ, w.arg + w.im = π ∧
      w * cexp w = ↑‖z‖ * cexp (↑π * I) ∧ w.im > 0 := existsUnique_arg_add_im_eq_pi hρ
  exact ⟨w, ⟨hw, hz' ▸ hwz⟩, fun w' ⟨hw', hw'z, hw'im⟩ => H w' ⟨hw', hw'z.trans hz', hw'im⟩⟩

theorem existsUnique_mem_reProdIm_exp_eq {s : Set ℝ}
    (hz : z.im = 0) (H : ∃! t ∈ s, t * rexp t = z.re) :
    ∃! w : ℂ, w ∈ s ×ℂ {0} ∧ w * cexp w = z := by
  obtain ⟨x, ⟨hx1, hx2⟩, H⟩ : ∃! t ∈ s, t * rexp t = z.re := H
  refine ⟨x, ⟨by simpa [mem_reProdIm], ?_⟩, fun w' ⟨hw'1, hw'2⟩ => ?_⟩
  · simpa [Complex.ext_iff, exp_re, hx2] using hz.symm
  · apply Complex.ext (z := w') (w := x) (H w'.re ⟨hw'1.left, ?_⟩) hw'1.right
    simp [← hw'2, exp_re, mem_singleton_iff.mp <| mem_reProdIm.mp hw'1 |>.right]

theorem existsUnique_mem_Ico_exp_eq (hz : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    ∃! w : ℂ, w ∈ Ico (-1) 0 ×ℂ {0} ∧ w * cexp w = z :=
  existsUnique_mem_reProdIm_exp_eq hz.right <| existsUnique_mem_Ico_mul_exp_eq_of_mem_Ico hz.left

theorem existsUnique_mem_Iic_exp_eq (hz : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0}) :
    ∃! w : ℂ, w ∈ Iic (-1) ×ℂ {0} ∧ w * cexp w = z :=
  existsUnique_mem_reProdIm_exp_eq hz.right <| existsUnique_mem_Iic_mul_exp_eq_of_mem_Ico hz.left

theorem existsUnique_eq_neg_pi_mul_exp_eq (hz : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = -π ∧ w * cexp w = z := by
  obtain ⟨w, ⟨hw, hwz, hwim⟩, H⟩ : ∃! w : ℂ, w.arg + w.im = π ∧ w * cexp w = z ∧ w.im > 0 :=
    existsUnique_eq_pi_mul_exp_eq hz
  refine ⟨conj w, ⟨?_, ?_⟩, ?_⟩
  · grind [arg_conj, conj_im, arg_eq_pi_iff]
  · rw [exp_conj, ← map_mul, hwz, conj_eq_iff_im, hz.right]
  · intro w' ⟨hw', hw'z⟩
    rw [← H (conj w') ⟨?_, ?_, ?_⟩, conj_conj]
    · grind [arg_conj, conj_im, arg_eq_pi_iff, pi_pos]
    · rw [exp_conj, ← map_mul, hw'z, conj_eq_iff_im, hz.right]
    · grind [arg_mem_Ioc w', pi_pos, conj_im]

theorem existsUnique_eq_mul_exp_eq (hk : k ≠ 0) (hk' : k ≠ -1) (hz : z ∈ Iio 0 ×ℂ {0}) :
    ∃! w : ℂ, w.arg + w.im = (2 * k + 1) * π ∧ w * cexp w = z := by
  set θ := (2 * k + 1) * π with hθ
  have hθ1 : θ ≠ π := fun nh => hk (by exact_mod_cast (show (k : ℝ) = 0 by grind [pi_pos]))
  have hθ2 : θ ≠ -π := fun nh => hk' (by exact_mod_cast (show (k : ℝ) = -1 by grind [pi_pos]))
  have hargz : z.arg = π := arg_eq_pi_iff.mpr ⟨hz.left, hz.right⟩
  set ρ := ‖z‖
  have hθz : cexp (θ * I) = cexp (z.arg * I) := by
    rw [hθ, hargz, ofReal_mul, ofReal_add, add_mul, add_mul, add_comm, ofReal_mul, ofReal_intCast,
      ofReal_ofNat, mul_comm 2, mul_assoc (k * 2 : ℂ), mul_assoc (k : ℂ), ← mul_assoc 2,
      exp_periodic.int_mul k, ofReal_one, one_mul]
  have hz' : z = ρ * cexp (θ * I) := by rw [← norm_mul_exp_arg_mul_I z, hθz]
  obtain ⟨w, ⟨hw, hwz⟩, H⟩ : ∃! w : ℂ, w.arg + w.im = θ ∧ w * cexp w = ρ * cexp (θ * I) :=
    existsUnique_arg_add_im_eq hθ1 hθ2 <| norm_pos_iff.mpr fun h => by simp [h, mem_reProdIm] at hz
  exact ⟨w, ⟨hw, hz' ▸ hwz⟩, fun w' ⟨hw', hw'z⟩ => H w' ⟨hw', by rw [hw'z, hz']⟩⟩

theorem existsUnique_mem_Ioo_mul_exp_eq (k : ℤ) (hz : z ∈ Complex.slitPlane) :
    ∃! w : ℂ, w.arg + w.im ∈ Ioo ((2 * k - 1) * π) ((2 * k + 1) * π) ∧ w * cexp w = z := by
  set θ := z.arg + k * (2 * π) with hθ
  have hθ' : z.arg ∈ Ioo (-π) π :=
    ⟨arg_mem_Ioc z |>.left, lt_of_le_of_ne (arg_mem_Ioc z |>.right) <| slitPlane_arg_ne_pi hz⟩
  have hθ1 : θ ≠ π := by
    rcases (show k ≤ 0 ∨ k ≥ 1 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind
  have hθ2 : θ ≠ -π := by
    rcases (show k ≤ -1 ∨ k ≥ 0 by omega) with hk | hk <;> [apply ne_of_lt; apply ne_of_gt]
      <;> grw [hθ, hk] <;> grind
  have hθz : cexp (θ * I) = cexp (z.arg * I) := by
    rw [hθ, ofReal_add, add_mul, ofReal_mul, ofReal_intCast, ofReal_mul, ofReal_ofNat,
      mul_assoc, exp_periodic.int_mul k]
  set ρ := ‖z‖
  have hz' : z = ρ * cexp (θ * I) := by rw [← norm_mul_exp_arg_mul_I z, hθz]
  obtain ⟨w, ⟨hw, hwz⟩, H⟩ : ∃! w : ℂ, w.arg + w.im = θ ∧ w * cexp w = ρ * cexp (θ * I) :=
    existsUnique_arg_add_im_eq hθ1 hθ2 (norm_pos_iff.mpr <| slitPlane_ne_zero hz)
  refine ⟨w, by grind, fun w' ⟨hw', hw'z⟩ => H w' ⟨?_, ?_⟩⟩
  · grind [arg_mul_exp_eq_of_mem (by grind [slitPlane_ne_zero]) ⟨hw'.left, hw'.right.le⟩]
  · exact hw'z.trans hz'

-- Combine basic cases to obtain the cases `k = 0`, `k = -1`, and `k ≠ 0, -1`.

theorem existsUnique_mem_range_zero (z : ℂ) :
    ∃! w : ℂ, w ∈ range 0 ∧ w * cexp w = z := by
  by_cases hz : z = 0
  · exact ⟨0, ⟨zero_mem_range_zero, by simp [hz]⟩, fun w hw => by simpa [hz] using hw.right⟩
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  · rcases lt_or_ge z.re (-(rexp 1)⁻¹) with hz'' | hz''
    · replace hz'' : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := ⟨hz'', hz'.right⟩
      refine existsUnique_congr ?_ |>.mp (existsUnique_eq_pi_mul_exp_eq hz'')
      grind [mem_range_zero_iff, pi_pos, arg_add_im_eq_pi_of_mem_range_zero,
        im_pos_of_arg_add_im_eq_pi_of_mul_exp_mem]
    · replace hz'' : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0} := ⟨⟨hz'', hz'.left⟩, hz'.right⟩
      refine existsUnique_congr ?_ |>.mp (existsUnique_mem_Ico_exp_eq hz'')
      grind [mem_range_zero_iff, mem_reProdIm, arg_eq_pi_iff, pi_pos,
        mem_of_mem_range_zero_of_mul_exp_mem, arg_add_im_eq_pi_of_mem_range_zero]
  · replace hz : z ∈ Complex.slitPlane := mem_slitPlane_of_notMem hz hz'
    refine existsUnique_congr (fun w => ⟨fun hw => ?_, fun ⟨hw, hwz⟩ => ?_⟩) |>.mp <|
      existsUnique_mem_Ioo_mul_exp_eq 0 hz
    · grind [mem_range_zero_iff, arg_eq_pi_iff]
    · exact ⟨by simpa using arg_add_im_mem_Ioo_of_mem_range_zero_of_mul_exp_mem hw (hwz ▸ hz), hwz⟩

theorem existsUnique_mem_range_neg_one (hz : z ≠ 0) :
    ∃! w : ℂ, w ∈ range (-1) ∧ w * cexp w = z := by
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  · rcases lt_or_ge z.re (-(rexp 1)⁻¹) with hz'' | hz''
    · replace hz'' : z ∈ Iio (-(rexp 1)⁻¹) ×ℂ {0} := ⟨hz'', hz'.2⟩
      refine existsUnique_congr (fun w => ⟨fun ⟨hw, hwz⟩ => ?_, fun ⟨hw, hwz⟩ => ?_⟩) |>.mp <|
        existsUnique_eq_neg_pi_mul_exp_eq hz''
      · exact ⟨mem_range_neg_one_iff.mpr <| Or.inl ⟨by grind [pi_pos], hw.le⟩, hwz⟩
      · have : w.arg + w.im ∈ Ioc (-3 * π) (-π) :=
          arg_add_im_mem_Ioc_of_mem_range_neg_one_of_mul_exp_mem hw (hwz ▸ hz'')
        exact ⟨by grind [mul_exp_mem_of_arg_add_im_eq (w := w) (i := -1)], hwz⟩
    · replace hz'' : z ∈ Ico (-(rexp 1)⁻¹) 0 ×ℂ {0} := ⟨⟨hz'', hz'.left⟩, hz'.right⟩
      refine existsUnique_congr (fun w => ⟨fun ⟨hw, hwz⟩ => ?_, fun ⟨hw, hwz⟩ => ?_⟩) |>.mp <|
        existsUnique_mem_Iic_exp_eq hz''
      · exact ⟨mem_range_neg_one_iff.mpr <| Or.inr hw, hwz⟩
      · exact ⟨mem_Iic_of_mem_range_neg_one_of_mul_exp_mem hw (hwz ▸ hz''), hwz⟩
  · replace hz : z ∈ Complex.slitPlane := mem_slitPlane_of_notMem hz hz'
    refine existsUnique_congr (fun w => ⟨fun ⟨⟨hwl, hwr⟩, hwz⟩ => ?_, fun ⟨hw, hwz⟩ => ?_⟩) |>.mp <|
      existsUnique_mem_Ioo_mul_exp_eq (-1) hz
    · have : w.arg + w.im ∈ Ioo (-3 * π) (-π) :=
        arg_add_im_mem_Ioo_of_mem_range_neg_one_of_mul_exp_notMem hw (hwz ▸ hz')
      exact ⟨by grind, hwz⟩
    · simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, mul_neg, mul_one] at hwl hwr
      exact ⟨mem_range_neg_one_iff.mpr <| Or.inl ⟨by grind, by grind⟩, hwz⟩

theorem existsUnique_mem_range_of_ne (hk : k ≠ 0) (hk' : k ≠ -1) (hz : z ≠ 0) :
    ∃! w : ℂ, w ∈ range k ∧ w * cexp w = z := by
  by_cases hz' : z ∈ Iio 0 ×ℂ {0}
  · refine existsUnique_congr (fun w => ⟨fun ⟨hw, hwz⟩ => ?_, fun ⟨hw, hwz⟩ => ?_⟩) |>.mp <|
      existsUnique_eq_mul_exp_eq hk hk' hz'
    · exact ⟨mem_range_iff_of_ne hk hk' |>.mpr ⟨by grind [pi_pos], hw.le⟩, hwz⟩
    · exact ⟨mul_exp_mem_of_arg_add_im_eq (mem_range_iff_of_ne hk hk' |>.mp hw) (hwz ▸ hz'), hwz⟩
  · replace hz : z ∈ Complex.slitPlane := mem_slitPlane_of_notMem hz hz'
    refine existsUnique_congr (fun w => ⟨fun ⟨⟨hwl, hwr⟩, hwz⟩ => ?_, fun ⟨hw, hwz⟩ => ?_⟩) |>.mp <|
      existsUnique_mem_Ioo_mul_exp_eq k hz
    · exact ⟨mem_range_iff_of_ne hk hk' |>.mpr ⟨hwl, hwr.le⟩, hwz⟩
    · have hw' : w.arg + w.im ∈ Ioc ((2 * k - 1) * π) ((2 * k + 1) * π) :=
        mem_range_iff_of_ne hk hk' |>.mp hw
      refine ⟨⟨hw'.left, lt_of_le_of_ne hw'.2 fun h_eq => hz' <| hwz ▸ arg_eq_pi_iff.mp ?_⟩, hwz⟩
      rw [mul_exp_eq_of_arg_add_im_eq (ne_zero_of_mem_range hk hw) h_eq, ← ofReal_neg,
        arg_ofReal_of_neg <| neg_neg_iff_pos.mpr <| Real.exp_pos _]

/-- The `w` is `W_ k z`, see also `Complex.lambertW`. -/
public theorem existsUnique_mem_range_mul_exp_eq (hz : z ∈ domain k) :
    ∃! w ∈ range k, w * cexp w = z := by
  rcases (show k = 0 ∨ k = -1 ∨ (k ≠ 0 ∧ k ≠ -1) by tauto) with rfl | rfl | ⟨hk, hk'⟩
  · exact existsUnique_mem_range_zero z
  · exact existsUnique_mem_range_neg_one (by rwa [domain_of_ne_zero (by decide)] at hz)
  · exact existsUnique_mem_range_of_ne hk hk' (by rwa [domain_of_ne_zero hk] at hz)

--  Public theorems about bijectivity.

public theorem mul_exp_mem_domain (hw : w ∈ range k) : w * cexp w ∈ domain k := by
  grind [domain, ne_zero_of_mem_range, exp_ne_zero]

public theorem image_mul_exp_range :
    (fun w => w * cexp w) '' range k = domain k :=
  eq_of_subset_of_subset (image_subset_iff.mpr fun _ hw => mul_exp_mem_domain hw)
    fun _ hz => (existsUnique_mem_range_mul_exp_eq hz).exists

public theorem mapsTo_mul_exp_range :
    MapsTo (fun w => w * cexp w) (range k) (domain k) := fun _ hw => mul_exp_mem_domain hw

public theorem injOn_mul_exp_range :
    InjOn (fun w => w * cexp w) (range k) := by
  intro w₁ hw₁ w₂ hw₂ (h : w₁ * cexp w₁ = w₂ * cexp w₂)
  exact (existsUnique_mem_range_mul_exp_eq (mul_exp_mem_domain hw₁)).unique ⟨hw₁, rfl⟩ ⟨hw₂, h.symm⟩

public theorem surjOn_mul_exp_range :
    SurjOn (fun w => w * cexp w) (range k) (domain k) := by
  simpa only [← image_mul_exp_range] using surjOn_image _ _

/-- `w => w * exp w` is a bijection from `range k` onto `domain k`. -/
public theorem bijOn_mul_exp_range_domain :
    BijOn (fun w => w * cexp w) (range k) (domain k) :=
  ⟨mapsTo_mul_exp_range, injOn_mul_exp_range, surjOn_mul_exp_range⟩

end LambertWRangeDomain

end LambertW

section LambertW

open LambertW

/-- The index of the Lambert W branch containing `w`, i.e. the unique integer `k` s.t.
`w` lies in `Complex.LambertW.range k`.

The exceptional point `w = -1` is excluded because it lies in both `range 0` and
`range (-1)`, so the index would not be unique there. -/
public def LambertW.index (hw : w ≠ -1) : ℤ :=
  existsUnique_mem_range_of_ne_neg_one hw |>.choose

@[simp]
public theorem LambertW.mem_range_index (hw : w ≠ -1) : w ∈ range (index hw) :=
  existsUnique_mem_range_of_ne_neg_one hw |>.choose_spec.left

public theorem LambertW.index_eq_iff (hw : w ≠ -1) : index hw = k ↔ w ∈ range k :=
  existsUnique_mem_range_of_ne_neg_one hw |>.choose_eq_iff

/-- The `k`-th branch `W_ k` of the standard Lambert W function, i.e. the inverse
of `w => w * exp w` on `Complex.LambertW.range k`.

For `k = 0`, the principal branch `W₀` is a total function on `ℂ`.
For `k ≠ 0`, `W_ k 0` is the junk value from `Function.invFunOn`.

The branch cut of `W₀` is `(-∞, -1 / e]`, while the branch cut for other branches is `(-∞, 0]`.
The boundary choice for the range of `W_ k` follows the standard
choice given by the rule of *counter-clockwise continuity*.
-/
@[pp_nodot, expose, wikidata Q429331, dlmf 4.13]
public def lambertW (k : ℤ) : ℂ -> ℂ :=
  Function.invFunOn (fun w => w * cexp w) (LambertW.range k)

@[inherit_doc] scoped[ComplexLambertW] notation "W_ " => Complex.lambertW
recommended_spelling "lambertW" for "W_" in [lambertW, ComplexLambertW.«termW_»]

open scoped ComplexLambertW

/-- The principal branch `W₀` of the Lambert W function. -/
scoped[ComplexLambertW] notation "W₀" => W_ 0
recommended_spelling "lambertW_zero" for "W₀" in [ComplexLambertW.«termW₀»]

/-- Notation for the branch `W₋₁` of the Lambert W function. -/
scoped[ComplexLambertW] notation "W₋₁" => W_ (-1)
recommended_spelling "lambertW_neg_one" for "W₋₁" in [ComplexLambertW.«termW₋₁»]

public theorem invOn_lambertW_mul_exp_range_domain :
    InvOn (W_ k) (fun w => w * cexp w) (LambertW.range k) (domain k) :=
  bijOn_mul_exp_range_domain.invOn_invFunOn

public theorem invOn_mul_exp_lambertW_domain_range :
    InvOn (fun w => w * cexp w) (W_ k) (domain k) (LambertW.range k) :=
  invOn_lambertW_mul_exp_range_domain.symm

public theorem bijOn_lambertW_domain_range :
    BijOn (W_ k) (domain k) (LambertW.range k) :=
  bijOn_mul_exp_range_domain.symm invOn_mul_exp_lambertW_domain_range

public theorem lambertW_mem_range_of_mem_domain (hz : z ∈ domain k) : W_ k z ∈ range k :=
  bijOn_lambertW_domain_range.mapsTo hz

/-- `W_ k` is a left inverse of `w => w * exp w` on its range. -/
public theorem lambertW_mul_exp_of_mem_range (hw : w ∈ range k) : W_ k (w * exp w) = w :=
  invOn_lambertW_mul_exp_range_domain.left hw

/-- `W_ k` is a right inverse of `w => w * exp w` on its domain. -/
public theorem lambertW_mul_exp_lambertW_of_mem_domain (hz : z ∈ domain k) :
    W_ k z * cexp (W_ k z) = z :=
  invOn_mul_exp_lambertW_domain_range.left hz

@[simp]
public theorem lambertW_zero_mul_exp_lambertW_zero : W₀ z * cexp (W₀ z) = z :=
  lambertW_mul_exp_lambertW_of_mem_domain trivial

public theorem exists_eq_lambertW_of_eq_mul_exp (hw : z = w * cexp w) :
    ∃ k : ℤ, w = W_ k z ∧ z ∈ domain k := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ : w ∈ ⋃ k, LambertW.range k := eq_univ_iff_forall.mp iUnion_range w
  refine ⟨k, hw ▸ lambertW_mul_exp_of_mem_range hk |>.symm, ?_⟩
  by_cases hz : z = 0
  · simp_all
  by_cases hk : k = 0
  · simp [hk]
  · simpa [domain_of_ne_zero hk]

/-- For the equation `z = w * exp w`, holds if and only if
`w = W_ k z` for some `k` with `z ∈ domain k`. -/
public theorem eq_mul_exp_iff_exists_eq_lambertW :
    z = w * cexp w ↔ ∃ k : ℤ, w = W_ k z ∧ z ∈ domain k := by
  refine ⟨exists_eq_lambertW_of_eq_mul_exp, fun ⟨k, hk, hz⟩ => ?_⟩
  rw [hk, lambertW_mul_exp_lambertW_of_mem_domain hz]

/-- If `z = w * cexp w` and `hw : w ≠ -1`, then `w` is the value of the Lambert W branch
indexed by `index hw` at `z`, and `z` lies in the domain of that branch. -/
public theorem eq_lambertW_index_of_eq_mul_exp (hw : z = w * cexp w) (hw' : w ≠ -1) :
    w = W_ (index hw') z ∧ z ∈ domain (index hw') := by
  have hw'' : w ∈ range (index hw') := mem_range_index hw'
  constructor
  · rw [hw, lambertW_mul_exp_of_mem_range hw'']
  · by_cases hk₀ : index hw' = 0
    · simp [hk₀]
    · grind [mem_domain_of_ne_zero, ne_zero_of_mem_range, exp_ne_zero]

/-- If `hw : w ≠ -1`, `w = W_ k z`, and `z ∈ domain k`, then the branch index `k` equals
`index hw`. In other words, the branch index is uniquely determined by `w`. -/
public theorem eq_index_of_mem_lambertW (hw : w ≠ -1) (hw' : w = W_ k z) (hz : z ∈ domain k) :
    k = index hw := by
  apply index_eq_iff hw |>.mpr ?_ |>.symm
  simpa only [hw'] using lambertW_mem_range_of_mem_domain hz

/-- The principal branch `W₀` takes the value `-1` at the branch point `-(cexp 1)⁻¹ = -1 / e`. -/
public theorem lambertW_zero_neg_exp_one_inv : W₀ (-(cexp 1)⁻¹) = -1 := by
  rw [← neg_one_mul, ← exp_neg, lambertW_mul_exp_of_mem_range neg_one_mem_range_zero]

/-- The branch `W₋₁` takes the value `-1` at the branch point `-(cexp 1)⁻¹ = -1 / e`. -/
public theorem lambertW_neg_one_neg_exp_one_inv : W₋₁ (-(cexp 1)⁻¹) = -1 := by
  rw [← neg_one_mul (cexp 1)⁻¹, ← exp_neg, lambertW_mul_exp_of_mem_range neg_one_mem_range_neg_one]

end LambertW

end Complex

/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.AdaptationNote

#align_import analysis.special_functions.log.deriv from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Derivative and series expansion of real logarithm

In this file we prove that `Real.log` is infinitely smooth at all nonzero `x : ℝ`. We also prove
that the series `∑' n : ℕ, x ^ (n + 1) / (n + 1)` converges to `(-Real.log (1 - x))` for all
`x : ℝ`, `|x| < 1`.

## Tags

logarithm, derivative
-/


open Filter Finset Set

open scoped Topology

namespace Real

variable {x : ℝ}

theorem hasStrictDerivAt_log_of_pos (hx : 0 < x) : HasStrictDerivAt log x⁻¹ x := by
  have : HasStrictDerivAt log (exp <| log x)⁻¹ x :=
    (hasStrictDerivAt_exp <| log x).of_local_left_inverse (continuousAt_log hx.ne')
        (ne_of_gt <| exp_pos _) <|
      Eventually.mono (lt_mem_nhds hx) @exp_log
  rwa [exp_log hx] at this
#align real.has_strict_deriv_at_log_of_pos Real.hasStrictDerivAt_log_of_pos

theorem hasStrictDerivAt_log (hx : x ≠ 0) : HasStrictDerivAt log x⁻¹ x := by
  cases' hx.lt_or_lt with hx hx
  · convert (hasStrictDerivAt_log_of_pos (neg_pos.mpr hx)).comp x (hasStrictDerivAt_neg x) using 1
    · ext y; exact (log_neg_eq_log y).symm
    · field_simp [hx.ne]
  · exact hasStrictDerivAt_log_of_pos hx
#align real.has_strict_deriv_at_log Real.hasStrictDerivAt_log

theorem hasDerivAt_log (hx : x ≠ 0) : HasDerivAt log x⁻¹ x :=
  (hasStrictDerivAt_log hx).hasDerivAt
#align real.has_deriv_at_log Real.hasDerivAt_log

theorem differentiableAt_log (hx : x ≠ 0) : DifferentiableAt ℝ log x :=
  (hasDerivAt_log hx).differentiableAt
#align real.differentiable_at_log Real.differentiableAt_log

theorem differentiableOn_log : DifferentiableOn ℝ log {0}ᶜ := fun _x hx =>
  (differentiableAt_log hx).differentiableWithinAt
#align real.differentiable_on_log Real.differentiableOn_log

@[simp]
theorem differentiableAt_log_iff : DifferentiableAt ℝ log x ↔ x ≠ 0 :=
  ⟨fun h => continuousAt_log_iff.1 h.continuousAt, differentiableAt_log⟩
#align real.differentiable_at_log_iff Real.differentiableAt_log_iff

theorem deriv_log (x : ℝ) : deriv log x = x⁻¹ :=
  if hx : x = 0 then by
    rw [deriv_zero_of_not_differentiableAt (differentiableAt_log_iff.not_left.2 hx), hx, inv_zero]
  else (hasDerivAt_log hx).deriv
#align real.deriv_log Real.deriv_log

@[simp]
theorem deriv_log' : deriv log = Inv.inv :=
  funext deriv_log
#align real.deriv_log' Real.deriv_log'

theorem contDiffOn_log {n : ℕ∞} : ContDiffOn ℝ n log {0}ᶜ := by
  suffices ContDiffOn ℝ ⊤ log {0}ᶜ from this.of_le le_top
  refine (contDiffOn_top_iff_deriv_of_isOpen isOpen_compl_singleton).2 ?_
  simp [differentiableOn_log, contDiffOn_inv]
#align real.cont_diff_on_log Real.contDiffOn_log

theorem contDiffAt_log {n : ℕ∞} : ContDiffAt ℝ n log x ↔ x ≠ 0 :=
  ⟨fun h => continuousAt_log_iff.1 h.continuousAt, fun hx =>
    (contDiffOn_log x hx).contDiffAt <| IsOpen.mem_nhds isOpen_compl_singleton hx⟩
#align real.cont_diff_at_log Real.contDiffAt_log

end Real

section LogDifferentiable

open Real

section deriv

variable {f : ℝ → ℝ} {x f' : ℝ} {s : Set ℝ}

theorem HasDerivWithinAt.log (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun y => log (f y)) (f' / f x) s x := by
  rw [div_eq_inv_mul]
  exact (hasDerivAt_log hx).comp_hasDerivWithinAt x hf
#align has_deriv_within_at.log HasDerivWithinAt.log

theorem HasDerivAt.log (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
    HasDerivAt (fun y => log (f y)) (f' / f x) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.log hx
#align has_deriv_at.log HasDerivAt.log

theorem HasStrictDerivAt.log (hf : HasStrictDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictDerivAt (fun y => log (f y)) (f' / f x) x := by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log hx).comp x hf
#align has_strict_deriv_at.log HasStrictDerivAt.log

theorem derivWithin.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => log (f x)) s x = derivWithin f s x / f x :=
  (hf.hasDerivWithinAt.log hx).derivWithin hxs
#align deriv_within.log derivWithin.log

@[simp]
theorem deriv.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    deriv (fun x => log (f x)) x = deriv f x / f x :=
  (hf.hasDerivAt.log hx).deriv
#align deriv.log deriv.log

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ}
  {s : Set E}

theorem HasFDerivWithinAt.log (hf : HasFDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasFDerivWithinAt (fun x => log (f x)) ((f x)⁻¹ • f') s x :=
  (hasDerivAt_log hx).comp_hasFDerivWithinAt x hf
#align has_fderiv_within_at.log HasFDerivWithinAt.log

theorem HasFDerivAt.log (hf : HasFDerivAt f f' x) (hx : f x ≠ 0) :
    HasFDerivAt (fun x => log (f x)) ((f x)⁻¹ • f') x :=
  (hasDerivAt_log hx).comp_hasFDerivAt x hf
#align has_fderiv_at.log HasFDerivAt.log

theorem HasStrictFDerivAt.log (hf : HasStrictFDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictFDerivAt (fun x => log (f x)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAt_log hx).comp_hasStrictFDerivAt x hf
#align has_strict_fderiv_at.log HasStrictFDerivAt.log

theorem DifferentiableWithinAt.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun x => log (f x)) s x :=
  (hf.hasFDerivWithinAt.log hx).differentiableWithinAt
#align differentiable_within_at.log DifferentiableWithinAt.log

@[simp]
theorem DifferentiableAt.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    DifferentiableAt ℝ (fun x => log (f x)) x :=
  (hf.hasFDerivAt.log hx).differentiableAt
#align differentiable_at.log DifferentiableAt.log

theorem ContDiffAt.log {n} (hf : ContDiffAt ℝ n f x) (hx : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => log (f x)) x :=
  (contDiffAt_log.2 hx).comp x hf
#align cont_diff_at.log ContDiffAt.log

theorem ContDiffWithinAt.log {n} (hf : ContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun x => log (f x)) s x :=
  (contDiffAt_log.2 hx).comp_contDiffWithinAt x hf
#align cont_diff_within_at.log ContDiffWithinAt.log

theorem ContDiffOn.log {n} (hf : ContDiffOn ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => log (f x)) s := fun x hx => (hf x hx).log (hs x hx)
#align cont_diff_on.log ContDiffOn.log

theorem ContDiff.log {n} (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => log (f x) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.log (h x)
#align cont_diff.log ContDiff.log

theorem DifferentiableOn.log (hf : DifferentiableOn ℝ f s) (hx : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun x => log (f x)) s := fun x h => (hf x h).log (hx x h)
#align differentiable_on.log DifferentiableOn.log

@[simp]
theorem Differentiable.log (hf : Differentiable ℝ f) (hx : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun x => log (f x) := fun x => (hf x).log (hx x)
#align differentiable.log Differentiable.log

theorem fderivWithin.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => log (f x)) s x = (f x)⁻¹ • fderivWithin ℝ f s x :=
  (hf.hasFDerivWithinAt.log hx).fderivWithin hxs
#align fderiv_within.log fderivWithin.log

@[simp]
theorem fderiv.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    fderiv ℝ (fun x => log (f x)) x = (f x)⁻¹ • fderiv ℝ f x :=
  (hf.hasFDerivAt.log hx).fderiv
#align fderiv.log fderiv.log

end fderiv

end LogDifferentiable

namespace Real

/-- The function `x * log (1 + t / x)` tends to `t` at `+∞`. -/
theorem tendsto_mul_log_one_plus_div_atTop (t : ℝ) :
    Tendsto (fun x => x * log (1 + t / x)) atTop (𝓝 t) := by
  have h₁ : Tendsto (fun h => h⁻¹ * log (1 + t * h)) (𝓝[≠] 0) (𝓝 t) := by
    simpa [hasDerivAt_iff_tendsto_slope, slope_fun_def] using
      (((hasDerivAt_id (0 : ℝ)).const_mul t).const_add 1).log (by simp)
  have h₂ : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_inv_atTop_zero'.mono_right (nhdsWithin_mono _ fun x hx => (Set.mem_Ioi.mp hx).ne')
  simpa only [(· ∘ ·), inv_inv] using h₁.comp h₂
#align real.tendsto_mul_log_one_plus_div_at_top Real.tendsto_mul_log_one_plus_div_atTop

/-- A crude lemma estimating the difference between `log (1-x)` and its Taylor series at `0`,
where the main point of the bound is that it tends to `0`. The goal is to deduce the series
expansion of the logarithm, in `hasSum_pow_div_log_of_abs_lt_1`.

Porting note (#11215): TODO: use one of generic theorems about Taylor's series
to prove this estimate.
-/
theorem abs_log_sub_add_sum_range_le {x : ℝ} (h : |x| < 1) (n : ℕ) :
    |(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + log (1 - x)| ≤ |x| ^ (n + 1) / (1 - |x|) := by
  /- For the proof, we show that the derivative of the function to be estimated is small,
    and then apply the mean value inequality. -/
  let F : ℝ → ℝ := fun x => (∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + log (1 - x)
  let F' : ℝ → ℝ := fun x ↦ -x ^ n / (1 - x)
  -- Porting note: In `mathlib3`, the proof used `deriv`/`DifferentiableAt`. `simp` failed to
  -- compute `deriv`, so I changed the proof to use `HasDerivAt` instead
  -- First step: compute the derivative of `F`
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (F' y) y := fun y hy ↦ by
    have : HasDerivAt F ((∑ i ∈ range n, ↑(i + 1) * y ^ i / (↑i + 1)) + (-1) / (1 - y)) y :=
      .add (.sum fun i _ ↦ (hasDerivAt_pow (i + 1) y).div_const ((i : ℝ) + 1))
        (((hasDerivAt_id y).const_sub _).log <| sub_ne_zero.2 hy.2.ne')
    convert this using 1
    calc
      -y ^ n / (1 - y) = ∑ i ∈ Finset.range n, y ^ i + -1 / (1 - y) := by
        field_simp [geom_sum_eq hy.2.ne, sub_ne_zero.2 hy.2.ne, sub_ne_zero.2 hy.2.ne']
        ring
      _ = ∑ i ∈ Finset.range n, ↑(i + 1) * y ^ i / (↑i + 1) + -1 / (1 - y) := by
        congr with i
        rw [Nat.cast_succ, mul_div_cancel_left₀ _ (Nat.cast_add_one_pos i).ne']
  -- second step: show that the derivative of `F` is small
  have B : ∀ y ∈ Icc (-|x|) |x|, |F' y| ≤ |x| ^ n / (1 - |x|) := fun y hy ↦
    calc
      |F' y| = |y| ^ n / |1 - y| := by simp [F', abs_div]
      _ ≤ |x| ^ n / (1 - |x|) := by
        have : |y| ≤ |x| := abs_le.2 hy
        have : 1 - |x| ≤ |1 - y| := le_trans (by linarith [hy.2]) (le_abs_self _)
        gcongr
        exact sub_pos.2 h
  -- third step: apply the mean value inequality
  have C : ‖F x - F 0‖ ≤ |x| ^ n / (1 - |x|) * ‖x - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy ↦ (A _ ?_).hasDerivWithinAt) B (convex_Icc _ _) ?_ ?_
    · exact Icc_subset_Ioo (neg_lt_neg h) h hy
    · simp
    · simp [le_abs_self x, neg_le.mp (neg_le_abs x)]
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, div_mul_eq_mul_div, pow_succ] using C
#align real.abs_log_sub_add_sum_range_le Real.abs_log_sub_add_sum_range_le

/-- Power series expansion of the logarithm around `1`. -/
theorem hasSum_pow_div_log_of_abs_lt_one {x : ℝ} (h : |x| < 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / (n + 1)) (-log (1 - x)) := by
  rw [Summable.hasSum_iff_tendsto_nat]
  · show Tendsto (fun n : ℕ => ∑ i ∈ range n, x ^ (i + 1) / (i + 1)) atTop (𝓝 (-log (1 - x)))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [norm_eq_abs, sub_neg_eq_add]
    refine squeeze_zero (fun n => abs_nonneg _) (abs_log_sub_add_sum_range_le h) ?_
    suffices Tendsto (fun t : ℕ => |x| ^ (t + 1) / (1 - |x|)) atTop (𝓝 (|x| * 0 / (1 - |x|))) by
      simpa
    simp only [pow_succ']
    refine (tendsto_const_nhds.mul ?_).div_const _
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) h
  show Summable fun n : ℕ => x ^ (n + 1) / (n + 1)
  refine .of_norm_bounded _ (summable_geometric_of_lt_one (abs_nonneg _) h) fun i => ?_
  calc
    ‖x ^ (i + 1) / (i + 1)‖ = |x| ^ (i + 1) / (i + 1) := by
      have : (0 : ℝ) ≤ i + 1 := le_of_lt (Nat.cast_add_one_pos i)
      rw [norm_eq_abs, abs_div, ← pow_abs, abs_of_nonneg this]
    _ ≤ |x| ^ (i + 1) / (0 + 1) := by
      gcongr
      exact i.cast_nonneg
    _ ≤ |x| ^ i := by
      simpa [pow_succ] using mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) i) (le_of_lt h)
#align real.has_sum_pow_div_log_of_abs_lt_1 Real.hasSum_pow_div_log_of_abs_lt_one
@[deprecated] alias hasSum_pow_div_log_of_abs_lt_1 := hasSum_pow_div_log_of_abs_lt_one -- 2024-01-31

/-- Power series expansion of `log(1 + x) - log(1 - x)` for `|x| < 1`. -/
theorem hasSum_log_sub_log_of_abs_lt_one {x : ℝ} (h : |x| < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * x ^ (2 * k + 1))
      (log (1 + x) - log (1 - x)) := by
  set term := fun n : ℕ => -1 * ((-x) ^ (n + 1) / ((n : ℝ) + 1)) + x ^ (n + 1) / (n + 1)
  have h_term_eq_goal :
      term ∘ (2 * ·) = fun k : ℕ => 2 * (1 / (2 * k + 1)) * x ^ (2 * k + 1) := by
    ext n
    dsimp only [term, (· ∘ ·)]
    rw [Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1)) x]
    push_cast
    ring_nf
  rw [← h_term_eq_goal, (mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff]
  · have h₁ := (hasSum_pow_div_log_of_abs_lt_one (Eq.trans_lt (abs_neg x) h)).mul_left (-1)
    convert h₁.add (hasSum_pow_div_log_of_abs_lt_one h) using 1
    ring_nf
  · intro m hm
    rw [range_two_mul, Set.mem_setOf_eq, ← Nat.even_add_one] at hm
    dsimp [term]
    rw [Even.neg_pow hm, neg_one_mul, neg_add_self]
#align real.has_sum_log_sub_log_of_abs_lt_1 Real.hasSum_log_sub_log_of_abs_lt_one
@[deprecated] alias hasSum_log_sub_log_of_abs_lt_1 := hasSum_log_sub_log_of_abs_lt_one -- 2024-01-31

#adaptation_note /-- after v4.7.0-rc1, there is a performance problem in `field_simp`.
(Part of the code was ignoring the `maxDischargeDepth` setting:
 now that we have to increase it, other paths becomes slow.) -/
/-- Expansion of `log (1 + a⁻¹)` as a series in powers of `1 / (2 * a + 1)`. -/
theorem hasSum_log_one_add_inv {a : ℝ} (h : 0 < a) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1))
      (log (1 + a⁻¹)) := by
  have h₁ : |1 / (2 * a + 1)| < 1 := by
    rw [abs_of_pos, div_lt_one]
    · linarith
    · linarith
    · exact div_pos one_pos (by linarith)
  convert hasSum_log_sub_log_of_abs_lt_one h₁ using 1
  have h₂ : (2 : ℝ) * a + 1 ≠ 0 := by linarith
  have h₃ := h.ne'
  rw [← log_div]
  · congr
    field_simp
    linarith
  · field_simp
    linarith
  · field_simp
#align real.has_sum_log_one_add_inv Real.hasSum_log_one_add_inv

end Real

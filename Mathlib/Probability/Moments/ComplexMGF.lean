/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# The complex-valued moment generating function


## Main definitions

* `complexMGF X μ`: the function `z : ℂ ↦ μ[fun ω ↦ cexp (z * X ω)]`.

## Main results

* `complexMGF_ofReal_eq_mgf`: for `x : ℝ`, `complexMGF X μ x = mgf X μ x`.
* `hasDerivAt_complexMGF`: for all `z : ℂ` such that the real part `z.re` belongs to the interior
  of the interval of definition of the mgf, `complexMGF X μ` is differentiable at `z`
  with derivative `μ[X * exp (z * X)]`.
* `differentiableOn_complexMGF`: `complexMGF X μ` is holomorphic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.
* `analyticOn_complexMGF`: `complexMGF X μ` is analytic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.

## TODO

* `x : ℝ ↦ complexMGF X μ (I * x)` is equal to the characteristic function of
  the random variable `X`.
* If two random variables have same `mgf`, then they have the same `complexMGF`.
* As a consequence, if two random variables have same `mgf`, then they have the same
  characteristic function and the same distribution.

-/


open MeasureTheory Filter Finset Real Complex

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {p : ℕ} {μ : Measure Ω} {t u v : ℝ}
  {z ε : ℂ}

/-- Complex extension of the moment generating function. -/
noncomputable
def complexMGF (X : Ω → ℝ) (μ : Measure Ω) (z : ℂ) : ℂ := μ[fun ω ↦ cexp (z * X ω)]

lemma abs_complexMGF_le_mgf : abs (complexMGF X μ z) ≤ mgf X μ z.re := by
  rw [complexMGF, ← re_add_im z]
  simp_rw [add_mul, Complex.exp_add, re_add_im, ← Complex.norm_eq_abs]
  calc ‖∫ ω, cexp (z.re * X ω) * cexp (z.im * I * X ω) ∂μ‖
  _ ≤ ∫ ω, ‖cexp (z.re * X ω) * cexp (z.im * I * X ω)‖ ∂μ := norm_integral_le_integral_norm _
  _ = ∫ ω, abs (cexp (z.re * X ω)) ∂μ := by
    simp only [norm_mul, Complex.norm_eq_abs]
    congr with ω
    simp only [ne_eq, map_eq_zero, Complex.exp_ne_zero, not_false_eq_true, mul_eq_left₀]
    rw [mul_comm _ I, mul_assoc, mul_comm]
    exact mod_cast abs_exp_ofReal_mul_I _
  _ = ∫ ω, rexp (z.re * X ω) ∂μ := by simp [Complex.abs_exp]

lemma complexMGF_ofReal_eq_mgf (x : ℝ) : complexMGF X μ x = mgf X μ x := by
  rw [complexMGF]
  norm_cast
  have : ∫ ω, (rexp (x * X ω) : ℂ) ∂μ = ∫ ω, rexp (x * X ω) ∂μ := integral_ofReal
  rw [this]
  simp only [mgf]

lemma integrable_cexp_iff {Y : Ω → ℂ} (hY : AEMeasurable Y μ) :
    Integrable (fun ω ↦ cexp (Y ω)) μ ↔ Integrable (fun ω ↦ rexp ((Y ω).re)) μ := by
  rw [← integrable_norm_iff]
  swap; · exact (Complex.measurable_exp.comp_aemeasurable hY).aestronglyMeasurable
  congr! with ω
  simp only [Complex.norm_eq_abs, Complex.abs_exp]

lemma convexMGF_add_sub_convexMGF (ht : t ≠ 0)
    (h_int_pos : Integrable (fun ω ↦ rexp ((z.re + t) * X ω)) μ)
    (h_int_neg : Integrable (fun ω ↦ rexp ((z.re - t) * X ω)) μ)
    (hε : |ε.re| ≤ |t|) :
    complexMGF X μ (z + ε) - complexMGF X μ z - ε * ∫ ω, X ω * cexp (z * X ω) ∂μ
      = μ[fun ω ↦ cexp (z * X ω) * (cexp (ε * X ω) - 1 - ε * X ω)] := by
  have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ h_int_pos h_int_neg
  swap; · rw [← sub_ne_zero]; simp [ht]
  have hε_int_pos : Integrable (fun ω ↦ rexp ((z.re + ε.re) * X ω)) μ := by
    refine integrable_exp_mul_of_le_of_le (a := z.re - |t|) (b := z.re + |t|) ?_ ?_ ?_ ?_
    · rcases le_total 0 t with ht | ht
      · rwa [_root_.abs_of_nonneg ht]
      · simpa [abs_of_nonpos ht]
    · rcases le_total 0 t with ht | ht
      · rwa [_root_.abs_of_nonneg ht]
      · rwa [abs_of_nonpos ht]
    · rw [sub_eq_add_neg]
      gcongr
      rw [neg_le]
      exact (neg_le_abs _).trans hε
    · gcongr
      exact (le_abs_self _).trans hε
  have h_int_zε : Integrable (fun ω ↦ cexp ((z + ε) * X ω)) μ := by
    rw [integrable_cexp_iff]
    swap; · exact (Complex.measurable_ofReal.comp_aemeasurable hX).const_mul _
    simp only [mul_re, add_re, ofReal_re, add_im, ofReal_im, mul_zero, sub_zero]
    exact hε_int_pos
  have h_int_z : Integrable (fun ω ↦ cexp (z * X ω)) μ := by
    rw [integrable_cexp_iff]
    swap; · exact (Complex.measurable_ofReal.comp_aemeasurable hX).const_mul _
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    convert integrable_pow_abs_mul_exp_of_integrable_exp_mul ht h_int_pos h_int_neg 0 using 2
    simp
  simp_rw [complexMGF, add_mul, Complex.exp_add, mul_comm _ (cexp (ε * X _))]
  rw [← integral_mul_left, ← integral_sub, ← integral_sub]
  · congr with ω
    simp_rw [mul_sub, sub_sub, mul_one]
    ring
  · refine Integrable.sub ?_ h_int_z
    · simp_rw [← Complex.exp_add, ← add_mul, add_comm ε]
      exact h_int_zε
  · refine Integrable.const_mul ?_ _
    rw [← integrable_norm_iff]
    swap
    · refine AEMeasurable.aestronglyMeasurable ?_
      refine (Complex.measurable_ofReal.comp_aemeasurable hX).mul ?_
      refine Complex.measurable_exp.comp_aemeasurable ?_
      exact (Complex.measurable_ofReal.comp_aemeasurable hX).const_mul _
    simp only [norm_mul, Complex.norm_eq_abs, abs_ofReal, Complex.abs_exp, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero]
    convert integrable_pow_abs_mul_exp_of_integrable_exp_mul ht h_int_pos h_int_neg 1
    simp
  · simp_rw [← Complex.exp_add, ← add_mul, add_comm ε]
    exact h_int_zε
  · exact h_int_z

theorem exp_bound_exp (x : ℂ) (n : ℕ) :
    abs (cexp x - ∑ m ∈ range n, x ^ m / m.factorial) ≤ abs x ^ n * rexp (abs x) := by
  rw [← CauSeq.lim_const (abv := Complex.abs) (∑ m ∈ range n, _), Complex.exp, sub_eq_add_neg,
    ← CauSeq.lim_neg, CauSeq.lim_add, ← lim_abs]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  show abs ((∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial)
    ≤ abs x ^ n * rexp (abs x)
  rw [sum_range_sub_sum_range hj]
  calc
    abs (∑ m ∈ range j with n ≤ m, (x ^ m / m.factorial : ℂ))
      = abs (∑ m ∈ range j with n ≤ m, (x ^ n * (x ^ (m - n) / m.factorial) : ℂ)) := by
      refine congr_arg abs (sum_congr rfl fun m hm => ?_)
      rw [mem_filter, mem_range] at hm
      rw [← mul_div_assoc, ← pow_add, add_tsub_cancel_of_le hm.2]
    _ ≤ ∑ m ∈ range j with n ≤ m, abs (x ^ n * (x ^ (m - n) / m.factorial)) :=
      IsAbsoluteValue.abv_sum Complex.abs ..
    _ ≤ ∑ m ∈ range j with n ≤ m, abs x ^ n * (abs x ^ (m - n) / (m - n).factorial) := by
      simp_rw [map_mul, map_pow, map_div₀, abs_natCast]
      gcongr with i hi
      · rw [IsAbsoluteValue.abv_pow abs]
      · simp
    _ = abs x ^ n * ∑ m ∈ range j with n ≤ m, (abs x ^ (m - n) / (m - n).factorial) := by
      rw [← mul_sum]
    _ = abs x ^ n * ∑ m ∈ range (j - n), (abs x ^ m / m.factorial) := by
      congr 1
      refine (sum_bij (fun m hm ↦ m + n) ?_ ?_ ?_ ?_).symm
      · intro a ha
        simp only [mem_filter, mem_range, le_add_iff_nonneg_left, zero_le, and_true]
        simp only [mem_range] at ha
        rwa [← lt_tsub_iff_right]
      · intro a ha b hb hab
        simpa using hab
      · intro b hb
        simp only [mem_range, exists_prop]
        simp only [mem_filter, mem_range] at hb
        refine ⟨b - n, ?_, ?_⟩
        · rw [tsub_lt_tsub_iff_right hb.2]
          exact hb.1
        · rw [tsub_add_cancel_of_le hb.2]
      · simp
    _ ≤ abs x ^ n * rexp (abs x) := by
      gcongr
      refine sum_le_exp_of_nonneg ?_ _
      exact AbsoluteValue.nonneg abs x

lemma abs_exp_sub_le_sq_mul_exp (z : ℂ) :
    abs (cexp z - 1 - z) ≤ abs z ^ 2 * rexp (abs z) :=
  calc
  _ = abs (cexp z - ∑ n in range 2, z ^ n / n.factorial) := by simp [sum_range, sub_add_eq_sub_sub]
  _ ≤ abs z ^ 2 * rexp (abs z) := exp_bound_exp z 2

lemma abs_convexMGF_add_sub_convexMGF_le
    (h_int_pos : Integrable (fun ω ↦ rexp ((z.re + t) * X ω)) μ)
    (h_int_neg : Integrable (fun ω ↦ rexp ((z.re - t) * X ω)) μ)
    (hε : abs ε < |t|) :
    abs (complexMGF X μ (z + ε) - complexMGF X μ z - ε * ∫ ω, X ω * cexp (z * X ω) ∂μ)
      ≤ (abs ε)^2 * μ[fun ω ↦ X ω ^ 2 * rexp (z.re * X ω + abs ε * |X ω|)] := by
  have ht : t ≠ 0 := by
    suffices |t| ≠ 0 by simpa
    refine (lt_of_le_of_lt ?_ hε).ne'
    exact AbsoluteValue.nonneg abs ε
  rw [convexMGF_add_sub_convexMGF ht h_int_pos h_int_neg ((abs_re_le_abs ε).trans hε.le),
    ← integral_mul_left, ← Complex.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp only [norm_mul, Complex.norm_eq_abs, Complex.abs_exp, mul_re, ofReal_re, ofReal_im, mul_zero,
    sub_zero, _root_.sq_abs]
  refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ ?_) ?_ (ae_of_all _ fun ω ↦ ?_)
  · positivity
  · refine Integrable.const_mul ?_ _
    convert integrable_pow_abs_mul_exp_add_of_integrable_exp_mul h_int_pos h_int_neg
      (AbsoluteValue.nonneg abs ε) hε 2 using 3
    simp
  · simp_rw [Real.exp_add, mul_comm (rexp (z.re * X ω)), ← mul_assoc]
    gcongr
    convert abs_exp_sub_le_sq_mul_exp (ε * X ω)
    · simp [mul_pow]
    · simp

/-- For all `z : ℂ` such that the real part `z.re` belongs to the interior
  of the interval of definition of the mgf, `complexMGF X μ` is differentiable at `z`
  with derivative `μ[X * exp (z * X)]`. -/
theorem hasDerivAt_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (complexMGF X μ) (μ[fun ω ↦ X ω * cexp (z * X ω)]) z := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hz
  obtain ⟨l, u, hlu, h_subset⟩ := hz
  let t := ((z.re - l) ⊓ (u - z.re)) / 2
  have h_pos : 0 < (z.re - l) ⊓ (u - z.re) := by simp [hlu.1, hlu.2]
  have ht : 0 < t := half_pos h_pos
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [smul_eq_mul]
  calc (fun h ↦ complexMGF X μ (z + h) - complexMGF X μ z - h * ∫ ω, X ω * cexp (z * X ω) ∂μ)
  _ =O[𝓝 0] fun h ↦ (abs h)^2 * μ[fun ω ↦ X ω ^ 2 * rexp (z.re * X ω + abs h * |X ω|)] := by
    refine Eventually.isBigO ?_
    simp only [Complex.norm_eq_abs, _root_.sq_abs]
    rw [eventually_nhds_iff]
    refine ⟨{x | abs x < t}, fun y hy ↦ ?_, ?_, by simp [ht]⟩
    · refine abs_convexMGF_add_sub_convexMGF_le ?_ ?_ (hy.trans_le (le_abs_self _))
      · exact h_subset (add_half_inf_sub_mem_Ioo hlu)
      · exact h_subset (sub_half_inf_sub_mem_Ioo hlu)
    · refine isOpen_lt ?_ (by fun_prop)
      exact Complex.continuous_abs -- fun_prop fails
  _ =o[𝓝 0] fun h ↦ h * 1 := by
    refine (Asymptotics.isLittleO_norm_pow_id one_lt_two).mul_isBigO ?_
    refine Tendsto.isBigO_one _ (c := μ[fun ω ↦ X ω ^ 2 * rexp (z.re * X ω)]) ?_
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ω ↦ X ω ^ 2 * rexp (z.re * X ω + t/2 * |X ω|)) ?_ ?_ ?_ ?_
    · refine .of_forall fun h ↦ AEMeasurable.aestronglyMeasurable ?_
      exact AEMeasurable.mul (by fun_prop) (Real.measurable_exp.comp_aemeasurable (by fun_prop))
    · rw [eventually_nhds_iff]
      refine ⟨{x | abs x < t/2}, fun y hy ↦ ?_, ?_, by simp [ht]⟩
      · refine ae_of_all _ fun ω ↦ ?_
        simp only [norm_mul, norm_pow, Real.norm_eq_abs, _root_.sq_abs, Real.abs_exp]
        gcongr
        exact hy.le
      · exact isOpen_lt Complex.continuous_abs (by fun_prop)
    · convert integrable_pow_abs_mul_exp_add_of_integrable_exp_mul ?_ ?_ (half_pos ht).le (t := t)
        ?_ 2 using 3
      · simp
      · exact h_subset (add_half_inf_sub_mem_Ioo hlu)
      · exact h_subset (sub_half_inf_sub_mem_Ioo hlu)
      · simp [_root_.abs_of_nonneg ht.le, ht]
    · refine ae_of_all _ fun ω ↦ ?_
      refine Tendsto.const_mul _ ?_
      refine (Real.continuous_exp.tendsto _).comp ?_
      nth_rw 2 [← add_zero (z.re * X ω)]
      refine tendsto_const_nhds.add ?_
      rw [← zero_mul (|X ω|)]
      refine Tendsto.mul_const _ ?_
      convert continuous_abs.tendsto 0
      simp
  _ = fun h ↦ h := by simp

/-- `complexMGF X μ` is holomorphic on the vertical strip
`{z | z.re ∈ interior (integrableExpSet X μ)}`. -/
theorem differentiableOn_complexMGF :
    DifferentiableOn ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} := by
  intro z hz
  have h := hasDerivAt_complexMGF hz
  rw [hasDerivAt_iff_hasFDerivAt] at h
  exact h.hasFDerivWithinAt.differentiableWithinAt

/-- `complexMGF X μ` is analytic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`. -/
theorem analyticOn_complexMGF :
    AnalyticOn ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} :=
  differentiableOn_complexMGF.analyticOn (isOpen_interior.preimage Complex.continuous_re)

end ProbabilityTheory

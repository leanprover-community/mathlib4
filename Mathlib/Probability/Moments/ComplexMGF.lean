/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntegral
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
* `analyticOnNhd_complexMGF`: `complexMGF X μ` is analytic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.
* `eqOn_complexMGF_of_mgf`: if two random variables have the same moment generating function,
  defined on an interval with nonempty interior, then they have the same `complexMGF`
  on the vertical strip `{z | z.re ∈ interior (integrableExpSet X μ)}`.

## TODO

Once we have a definition for the characteristic function, we will be able to prove the following.

* `x : ℝ ↦ complexMGF X μ (I * x)` is equal to the characteristic function of
  the random variable `X`.
* As a consequence, if two random variables have same `mgf`, then they have the same
  characteristic function and the same distribution.

-/


open MeasureTheory Filter Finset Real Complex

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {p : ℕ} {μ : Measure Ω} {t u v : ℝ}
  {z ε : ℂ}

lemma integrable_cexp_iff {Y : Ω → ℂ} (hY : AEMeasurable Y μ) :
    Integrable (fun ω ↦ cexp (Y ω)) μ ↔ Integrable (fun ω ↦ rexp ((Y ω).re)) μ := by
  rw [← integrable_norm_iff]
  swap; · exact (Complex.measurable_exp.comp_aemeasurable hY).aestronglyMeasurable
  congr! with ω
  simp only [Complex.norm_eq_abs, Complex.abs_exp]

/-- Complex extension of the moment generating function. -/
noncomputable
def complexMGF (X : Ω → ℝ) (μ : Measure Ω) (z : ℂ) : ℂ := μ[fun ω ↦ cexp (z * X ω)]

lemma complexMGF_undef (hX : AEMeasurable X μ) (h : ¬ Integrable (fun ω ↦ rexp (z.re * X ω)) μ) :
    complexMGF X μ z = 0 := by
  rw [complexMGF, integral_undef]
  rw [integrable_cexp_iff]
  · simpa using h
  · exact (Complex.measurable_ofReal.comp_aemeasurable hX).const_mul _

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

lemma re_complexMGF_ofReal (x : ℝ) : (complexMGF X μ x).re = mgf X μ x := by
  simp [complexMGF_ofReal_eq_mgf]

lemma re_complexMGF_ofReal' : (fun x : ℝ ↦ (complexMGF X μ x).re) = mgf X μ := by
  ext x
  exact re_complexMGF_ofReal x

lemma convexMGF_add_sub_range (ht : t ≠ 0)
    (h_int_pos : Integrable (fun ω ↦ rexp ((z.re + t) * X ω)) μ)
    (h_int_neg : Integrable (fun ω ↦ rexp ((z.re - t) * X ω)) μ)
    (hε : |ε.re| ≤ |t|) (n : ℕ) :
    complexMGF X μ (z + ε) - ∑ m in range n, ε ^ m / m.factorial * ∫ ω, X ω ^ m * cexp (z * X ω) ∂μ
      = μ[fun ω ↦ cexp (z * X ω)
        * (cexp (ε * X ω) - ∑ m in range n, ε ^ m / m.factorial * X ω ^ m)] := by
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
  have h_int_mul i : Integrable (fun ω ↦ X ω ^ i * cexp (z * X ω)) μ := by
    rw [← integrable_norm_iff]
    swap
    · refine AEMeasurable.aestronglyMeasurable ?_
      refine ((Complex.measurable_ofReal.comp_aemeasurable hX).pow_const _).mul ?_
      refine Complex.measurable_exp.comp_aemeasurable ?_
      exact (Complex.measurable_ofReal.comp_aemeasurable hX).const_mul _
    simp only [norm_mul, Complex.norm_eq_abs, abs_ofReal, Complex.abs_exp, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero]
    convert integrable_pow_abs_mul_exp_of_integrable_exp_mul ht h_int_pos h_int_neg i
    simp
  simp_rw [complexMGF, add_mul, Complex.exp_add, mul_comm _ (cexp (ε * X _))]
  calc ∫ ω, cexp (ε * X ω) * cexp (z * X ω) ∂μ -
      ∑ m ∈ range n, ε ^ m / m.factorial * ∫ ω, X ω ^ m * cexp (z * X ω) ∂μ
  _ = ∫ ω, cexp (ε * X ω) * cexp (z * X ω) ∂μ -
      ∑ m ∈ range n, ∫ ω, ε ^ m / m.factorial * X ω ^ m * cexp (z * X ω) ∂μ := by
    congr with m
    rw [← integral_mul_left]
    simp_rw [mul_assoc]
  _ = ∫ ω, cexp (ε * X ω) * cexp (z * X ω) ∂μ -
      ∫ ω, ∑ m ∈ range n, ε ^ m / m.factorial * X ω ^ m * cexp (z * X ω) ∂μ := by
    congr
    rw [integral_finset_sum _ fun i hi ↦ ?_]
    simp_rw [mul_assoc]
    refine Integrable.const_mul ?_ _
    exact h_int_mul _
  _ = ∫ ω, cexp (z * X ω) * (cexp (ε * X ω) - ∑ m ∈ range n, ε ^ m / m.factorial * X ω ^ m) ∂μ := by
    rw [← integral_sub]
    · congr with ω
      simp_rw [mul_sub]
      congr 1
      · rw [mul_comm]
      · rw [mul_sum]
        congr with m
        ring
    · simp_rw [← Complex.exp_add, ← add_mul, add_comm ε]
      exact h_int_zε
    · refine integrable_finset_sum _ fun m hm ↦ ?_
      simp_rw [mul_assoc]
      refine Integrable.const_mul ?_ _
      exact h_int_mul _

lemma abs_exp_sub_range_le_exp_sub_range_abs (x : ℂ) (n : ℕ) :
  abs (cexp x - ∑ m ∈ range n, x ^ m / m.factorial)
    ≤ rexp (abs x) - ∑ m ∈ range n, (abs x) ^ m / m.factorial := by
  rw [← CauSeq.lim_const (abv := Complex.abs) (∑ m ∈ range n, _), Complex.exp, sub_eq_add_neg,
    ← CauSeq.lim_neg, CauSeq.lim_add, ← lim_abs]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  calc abs ((∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial)
  _ ≤ (∑ m ∈ range j, abs x ^ m / m.factorial) - ∑ m ∈ range n, abs x ^ m / m.factorial := by
    rw [sum_range_sub_sum_range hj, sum_range_sub_sum_range hj]
    refine (IsAbsoluteValue.abv_sum Complex.abs ..).trans_eq ?_
    congr with i
    simp
  _ ≤ rexp (abs x) - ∑ m ∈ range n, (abs x) ^ m / m.factorial := by
    gcongr
    exact sum_le_exp_of_nonneg (by exact AbsoluteValue.nonneg abs x) _

lemma abs_exp_le_exp_abs (z : ℂ) : abs (cexp z) ≤ rexp (abs z) := by
  convert abs_exp_sub_range_le_exp_sub_range_abs z 0 using 1 <;> simp

lemma exp_bound_exp (x : ℂ) (n : ℕ) :
    abs (cexp x - ∑ m ∈ range n, x ^ m / m.factorial) ≤ abs x ^ n * rexp (abs x) := by
  rw [← CauSeq.lim_const (abv := Complex.abs) (∑ m ∈ range n, _), Complex.exp, sub_eq_add_neg,
    ← CauSeq.lim_neg, CauSeq.lim_add, ← lim_abs]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  show abs ((∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial) ≤ _
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

lemma abs_convexMGF_add_sub_range_le
    (h_int_pos : Integrable (fun ω ↦ rexp ((z.re + t) * X ω)) μ)
    (h_int_neg : Integrable (fun ω ↦ rexp ((z.re - t) * X ω)) μ)
    (hε : abs ε < |t|) (n : ℕ):
    abs (complexMGF X μ (z + ε)
        - ∑ m in range n, ε ^ m / m.factorial * ∫ ω, X ω ^ m * cexp (z * X ω) ∂μ)
      ≤ (abs ε) ^ n * μ[fun ω ↦ |X ω| ^ n * rexp (z.re * X ω + abs ε * |X ω|)] := by
  have ht : t ≠ 0 := by
    suffices |t| ≠ 0 by simpa
    refine (lt_of_le_of_lt ?_ hε).ne'
    exact AbsoluteValue.nonneg abs ε
  rw [convexMGF_add_sub_range ht h_int_pos h_int_neg ((abs_re_le_abs ε).trans hε.le),
    ← integral_mul_left, ← Complex.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp only [norm_mul, Complex.norm_eq_abs, Complex.abs_exp, mul_re, ofReal_re, ofReal_im, mul_zero,
    sub_zero, _root_.sq_abs]
  refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ ?_) ?_ (ae_of_all _ fun ω ↦ ?_)
  · positivity
  · refine Integrable.const_mul ?_ _
    exact integrable_pow_abs_mul_exp_add_of_integrable_exp_mul h_int_pos h_int_neg
      (AbsoluteValue.nonneg abs ε) hε n
  · simp_rw [Real.exp_add, mul_comm (rexp (z.re * X ω)), ← mul_assoc]
    gcongr
    convert exp_bound_exp (ε * X ω) n using 4 with m hm
    · rw [mul_pow]
      ring
    · simp [mul_pow]
    · simp

lemma tendsto_todo_pow_abs (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    Tendsto (fun h ↦ μ[fun ω ↦ |X ω| ^ n * rexp (z.re * X ω + abs h * |X ω|)]) (𝓝 0)
      (𝓝 μ[fun ω ↦ |X ω| ^ n * rexp (z.re * X ω)]) := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hz
  obtain ⟨l, u, hlu, h_subset⟩ := hz
  let t := ((z.re - l) ⊓ (u - z.re)) / 2
  have h_pos : 0 < (z.re - l) ⊓ (u - z.re) := by simp [hlu.1, hlu.2]
  have ht : 0 < t := half_pos h_pos
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ω ↦ |X ω| ^ n * rexp (z.re * X ω + t/2 * |X ω|)) ?_ ?_ ?_ ?_
  · refine .of_forall fun h ↦ AEMeasurable.aestronglyMeasurable ?_
    exact AEMeasurable.mul (by fun_prop) (Real.measurable_exp.comp_aemeasurable (by fun_prop))
  · rw [eventually_nhds_iff]
    refine ⟨{x | abs x < t/2}, fun y hy ↦ ?_, ?_, by simp [ht]⟩
    · refine ae_of_all _ fun ω ↦ ?_
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, _root_.abs_abs, Real.abs_exp]
      gcongr
      exact hy.le
    · exact isOpen_lt Complex.continuous_abs (by fun_prop)
  · convert integrable_pow_abs_mul_exp_add_of_integrable_exp_mul ?_ ?_ (half_pos ht).le (t := t)
      ?_ n using 3
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

lemma isBigO_abs_convexMGF_add_sub_range (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    (fun ε ↦ complexMGF X μ (z + ε)
        - ∑ m in range n, ε ^ m / m.factorial * ∫ ω, X ω ^ m * cexp (z * X ω) ∂μ)
      =O[𝓝 0] fun ε ↦ (abs ε) ^ n := by
  let hz' := hz
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hz'
  obtain ⟨l, u, hlu, h_subset⟩ := hz'
  let t := ((z.re - l) ⊓ (u - z.re)) / 2
  have h_pos : 0 < (z.re - l) ⊓ (u - z.re) := by simp [hlu.1, hlu.2]
  have ht : 0 < t := half_pos h_pos
  calc
  _ =O[𝓝 0] fun ε : ℂ ↦ (abs ε) ^ n * μ[fun ω ↦ |X ω| ^ n * rexp (z.re * X ω + abs ε * |X ω|)] := by
    refine Eventually.isBigO ?_
    rw [eventually_nhds_iff]
    refine ⟨{x | abs x < t}, fun y hy ↦ ?_, ?_, by simp [ht]⟩
    · simp only [Real.norm_eq_abs, Complex.abs_abs]
      refine abs_convexMGF_add_sub_range_le ?_ ?_ (hy.trans_le (le_abs_self _)) n
      · exact h_subset (add_half_inf_sub_mem_Ioo hlu)
      · exact h_subset (sub_half_inf_sub_mem_Ioo hlu)
    · refine isOpen_lt ?_ (by fun_prop)
      exact Complex.continuous_abs -- fun_prop fails
  _ =O[𝓝 0] fun ε ↦ (abs ε) ^ n * 1 := by
    refine Asymptotics.IsBigO.mul (Asymptotics.isBigO_refl _ _) ?_
    refine Tendsto.isBigO_one _ (c := μ[fun ω ↦ |X ω| ^ n * rexp (z.re * X ω)]) ?_
    exact tendsto_todo_pow_abs hz n
  _ = fun ε ↦ (abs ε) ^ n := by simp

/-- For all `z : ℂ` such that the real part `z.re` belongs to the interior
  of the interval of definition of the mgf, `complexMGF X μ` is differentiable at `z`
  with derivative `μ[X * exp (z * X)]`. -/
theorem hasDerivAt_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (complexMGF X μ) μ[fun ω ↦ X ω * cexp (z * X ω)] z := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [smul_eq_mul]
  calc (fun h ↦ complexMGF X μ (z + h) - complexMGF X μ z - h * ∫ ω, X ω * cexp (z * X ω) ∂μ)
  _ =O[𝓝 0] fun h ↦ (abs h)^2 := by
    convert isBigO_abs_convexMGF_add_sub_range hz 2 using 2
    simp [sum_range, sub_add_eq_sub_sub, complexMGF]
  _ =o[𝓝 0] fun h ↦ h := Asymptotics.isLittleO_norm_pow_id one_lt_two

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
theorem analyticOnNhd_complexMGF :
    AnalyticOnNhd ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} :=
  differentiableOn_complexMGF.analyticOnNhd (isOpen_interior.preimage Complex.continuous_re)

lemma analyticAt_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) :
    AnalyticAt ℂ (complexMGF X μ) z := analyticOnNhd_complexMGF z hz

lemma hasDerivAt_integral_pow_mul_exp (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (fun z ↦ μ[fun ω ↦ X ω ^ n * cexp (z * X ω)])
        μ[fun ω ↦ X ω ^ (n + 1) * cexp (z * X ω)] z := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  let hz' := hz
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hz
  obtain ⟨l, u, hlu, h_subset⟩ := hz
  let t := ((z.re - l) ⊓ (u - z.re)) / 2
  have h_pos : 0 < (z.re - l) ⊓ (u - z.re) := by simp [hlu.1, hlu.2]
  have ht : 0 < t := half_pos h_pos
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun ω ↦ |X ω| ^ (n + 1) * rexp (z.re * X ω + t/2 * |X ω|))
    (F := fun z ω ↦ X ω ^ n * cexp (z * X ω))
    (F' := fun z ω ↦ X ω ^ (n + 1) * cexp (z * X ω)) (half_pos ht) ?_ ?_ ?_ ?_ ?_ ?_).2
  · refine .of_forall fun z ↦ AEMeasurable.aestronglyMeasurable ?_
    exact AEMeasurable.mul (by fun_prop) (Complex.measurable_exp.comp_aemeasurable (by fun_prop))
  · rw [← integrable_norm_iff]
    swap
    · refine AEMeasurable.aestronglyMeasurable ?_
      refine ((Complex.measurable_ofReal.comp_aemeasurable hX).pow_const _).mul ?_
      refine Complex.measurable_exp.comp_aemeasurable ?_
      exact (Complex.measurable_ofReal.comp_aemeasurable hX).const_mul _
    simp only [norm_mul, Complex.norm_eq_abs, abs_ofReal, Complex.abs_exp, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero]
    convert integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet hz n
    simp
  · refine AEMeasurable.aestronglyMeasurable ?_
    exact AEMeasurable.mul (by fun_prop) (Complex.measurable_exp.comp_aemeasurable (by fun_prop))
  · refine ae_of_all _ fun ω ε hε ↦ ?_
    simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, Complex.norm_eq_abs]
    rw [Complex.abs_ofReal, Complex.abs_exp]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    gcongr
    have : ε = z + (ε - z) := by simp
    rw [this, add_re, add_mul]
    gcongr _ + ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    gcongr
    refine (abs_re_le_abs _).trans ?_
    simp only [Metric.mem_ball, dist_eq_norm, Complex.norm_eq_abs] at hε
    exact hε.le
  · refine integrable_pow_abs_mul_exp_add_of_integrable_exp_mul ?_ ?_ ?_ ?_ (t := t) (n + 1)
    · exact h_subset (add_half_inf_sub_mem_Ioo hlu)
    · exact h_subset (sub_half_inf_sub_mem_Ioo hlu)
    · positivity
    · refine lt_of_lt_of_le ?_ (le_abs_self _)
      simp [ht]
  · refine ae_of_all _ fun ω ε hε ↦ ?_
    simp only
    simp_rw [pow_succ, mul_assoc]
    refine HasDerivAt.const_mul _ ?_
    simp_rw [← smul_eq_mul, Complex.exp_eq_exp_ℂ]
    convert hasDerivAt_exp_smul_const (X ω : ℂ) ε using 1
    rw [smul_eq_mul, mul_comm]

lemma hasDerivAt_integral_pow_mul_exp_real (ht : t ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (fun t ↦ μ[fun ω ↦ X ω ^ n * rexp (t * X ω)])
      μ[fun ω ↦ X ω ^ (n + 1) * rexp (t * X ω)] t := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet ht
  have h_re_of_mem n t (ht' : t ∈ interior (integrableExpSet X μ)) :
      (∫ ω, X ω ^ n * cexp (t * X ω) ∂μ).re = ∫ ω, X ω ^ n * rexp (t * X ω) ∂μ := by
    simp_rw [← RCLike.re_eq_complex_re]
    rw [← integral_re]
    · norm_cast
    · rw [← integrable_norm_iff]
      swap
      · refine AEMeasurable.aestronglyMeasurable ?_
        refine ((Complex.measurable_ofReal.comp_aemeasurable hX).pow_const _).mul ?_
        refine Complex.measurable_exp.comp_aemeasurable ?_
        exact (Complex.measurable_ofReal.comp_aemeasurable hX).const_mul _
      simp only [norm_mul, Complex.norm_eq_abs, abs_ofReal, Complex.abs_exp, mul_re, ofReal_re,
        ofReal_im, mul_zero, sub_zero, Complex.abs_pow]
      exact integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet ht' n
  have h_re n : ∀ᶠ t' : ℝ in 𝓝 t, (∫ ω, X ω ^ n * cexp (t' * X ω) ∂μ).re
      = ∫ ω, X ω ^ n * rexp (t' * X ω) ∂μ := by
    filter_upwards [isOpen_interior.eventually_mem ht] with t ht' using h_re_of_mem n t ht'
  rw [← EventuallyEq.hasDerivAt_iff (h_re _), ← h_re_of_mem _ t ht]
  have h := hasDerivAt_integral_pow_mul_exp (X := X) (μ := μ) (z := t) ?_ n
  swap; · simp [ht]
  exact h.real_of_complex

lemma hasDeriAt_iteratedDeriv_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (iteratedDeriv n (complexMGF X μ)) μ[fun ω ↦ X ω ^ (n + 1) * cexp (z * X ω)] z := by
  induction n generalizing z with
  | zero => simp [hasDerivAt_complexMGF hz]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (complexMGF X μ))
        =ᶠ[𝓝 z] fun z ↦ μ[fun ω ↦ X ω ^ (n + 1) * cexp (z * X ω)] := by
      have h_mem : ∀ᶠ y in 𝓝 z, y.re ∈ interior (integrableExpSet X μ) := by
        refine IsOpen.eventually_mem ?_ hz
        exact isOpen_interior.preimage Complex.continuous_re
      filter_upwards [h_mem] with y hy using HasDerivAt.deriv (hn hy)
    rw [EventuallyEq.hasDerivAt_iff this]
    exact hasDerivAt_integral_pow_mul_exp hz (n + 1)

lemma iteratedDeriv_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    iteratedDeriv n (complexMGF X μ) z = μ[fun ω ↦ X ω ^ n * cexp (z * X ω)] := by
  induction n generalizing z with
  | zero => simp [complexMGF]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDeriAt_iteratedDeriv_complexMGF hz n).deriv

lemma integrableExpSet_eq_of_mgf {Y : Ω → ℝ} (hXY : mgf X μ = mgf Y μ) :
    integrableExpSet X μ = integrableExpSet Y μ := by
  ext t
  simp only [integrableExpSet, Set.mem_setOf_eq]
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [← mgf_pos_iff' hμ, ← mgf_pos_iff' hμ, hXY]

/-- If two random variables have the same moment generating function, defined on an interval with
nonempty interior, then they have the same `complexMGF` on the vertical strip
`{z | z.re ∈ interior (integrableExpSet X μ)}`. -/
lemma eqOn_complexMGF_of_mgf {Y : Ω → ℝ} (hXY : mgf X μ = mgf Y μ)
    (ht : t ∈ interior (integrableExpSet X μ)) :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ)
      {z | z.re ∈ interior (integrableExpSet X μ)} := by
  have hX : AnalyticOnNhd ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} :=
    analyticOnNhd_complexMGF
  have hY : AnalyticOnNhd ℂ (complexMGF Y μ) {z | z.re ∈ interior (integrableExpSet Y μ)} :=
    analyticOnNhd_complexMGF
  rw [integrableExpSet_eq_of_mgf hXY] at hX ht ⊢
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hX hY ?_ (z₀ := (t : ℂ))
    (by simp [ht]) ?_
  · exact (convex_integrableExpSet.interior.linear_preimage reLm).isPreconnected
  · have h_real : ∃ᶠ (x : ℝ) in 𝓝[≠] t, complexMGF X μ x = complexMGF Y μ x := by
      refine .of_forall fun y ↦ ?_
      rw [complexMGF_ofReal_eq_mgf, complexMGF_ofReal_eq_mgf, hXY]
    rw [frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · rw [tendsto_ofReal_iff]
        exact hx_tendsto.1
      · simpa using hx_tendsto.2
    · simp [hx_eq]

end ProbabilityTheory

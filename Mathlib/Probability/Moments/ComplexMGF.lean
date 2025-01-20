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

The moment generating function (mgf) is `t : ℝ ↦ μ[fun ω ↦ rexp (t * X ω)]`. It can be extended to
a complex function `z : ℂ ↦ μ[fun ω ↦ cexp (z * X ω)]`, which we call `complexMGF X μ`.
That function is holomorphic on the vertical strip with base the interior of the interval
of definition of the mgf.
On the vertical line that goes through 0, `complexMGF X μ` is equal to the characteristic function.
This allows us to link properties of the characteristic function and the mgf (mostly deducing
properties of the mgf from those of the characteristic function).

## Main definitions

* `complexMGF X μ`: the function `z : ℂ ↦ μ[fun ω ↦ cexp (z * X ω)]`.

## Main results

* `complexMGF_ofReal`: for `x : ℝ`, `complexMGF X μ x = mgf X μ x`.

* `hasDerivAt_complexMGF`: for all `z : ℂ` such that the real part `z.re` belongs to the interior
  of the interval of definition of the mgf, `complexMGF X μ` is differentiable at `z`
  with derivative `μ[X * exp (z * X)]`.
* `differentiableOn_complexMGF`: `complexMGF X μ` is holomorphic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.
* `analyticOnNhd_complexMGF`: `complexMGF X μ` is analytic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.

* `eqOn_complexMGF_of_mgf`: if two random variables have the same moment generating function,
  then they have the same `complexMGF` on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.

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

/-- Complex extension of the moment generating function. -/
noncomputable
def complexMGF (X : Ω → ℝ) (μ : Measure Ω) (z : ℂ) : ℂ := μ[fun ω ↦ cexp (z * X ω)]

lemma complexMGF_undef (hX : AEMeasurable X μ) (h : ¬ Integrable (fun ω ↦ rexp (z.re * X ω)) μ) :
    complexMGF X μ z = 0 := by
  rw [complexMGF, integral_undef]
  rw [← integrable_norm_iff (AEMeasurable.aestronglyMeasurable <| by fun_prop)]
  simpa [Complex.norm_eq_abs, Complex.abs_exp] using h

lemma complexMGF_id_map (hX : AEMeasurable X μ) : complexMGF id (μ.map X) = complexMGF X μ := by
  ext t
  rw [complexMGF, integral_map hX]
  · rfl
  · exact AEMeasurable.aestronglyMeasurable <| by fun_prop

lemma abs_complexMGF_le_mgf : abs (complexMGF X μ z) ≤ mgf X μ z.re := by
  rw [complexMGF, ← re_add_im z]
  simp_rw [add_mul, Complex.exp_add, re_add_im, ← Complex.norm_eq_abs]
  calc ‖∫ ω, cexp (z.re * X ω) * cexp (z.im * I * X ω) ∂μ‖
  _ ≤ ∫ ω, ‖cexp (z.re * X ω) * cexp (z.im * I * X ω)‖ ∂μ := norm_integral_le_integral_norm _
  _ = ∫ ω, rexp (z.re * X ω) ∂μ := by simp [Complex.abs_exp]

lemma complexMGF_ofReal (x : ℝ) : complexMGF X μ x = mgf X μ x := by
  rw [complexMGF]
  norm_cast
  have : ∫ ω, (rexp (x * X ω) : ℂ) ∂μ = ∫ ω, rexp (x * X ω) ∂μ := integral_ofReal
  rw [this]
  simp only [mgf]

lemma re_complexMGF_ofReal (x : ℝ) : (complexMGF X μ x).re = mgf X μ x := by
  simp [complexMGF_ofReal]

lemma re_complexMGF_ofReal' : (fun x : ℝ ↦ (complexMGF X μ x).re) = mgf X μ := by
  ext x
  exact re_complexMGF_ofReal x

section Analytic

lemma complexMGF_add_sub_sum (ht : t ≠ 0)
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
    rw [← integrable_norm_iff (AEMeasurable.aestronglyMeasurable <| by fun_prop)]
    simpa only [Complex.norm_eq_abs, Complex.abs_exp, mul_re, add_re, ofReal_re, add_im, ofReal_im,
      mul_zero, sub_zero]
  have h_int_mul i : Integrable (fun ω ↦ X ω ^ i * cexp (z * X ω)) μ := by
    rw [← integrable_norm_iff]
    swap; · exact AEMeasurable.aestronglyMeasurable (by fun_prop)
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

lemma abs_complexMGF_add_sub_sum_le
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
  rw [complexMGF_add_sub_sum ht h_int_pos h_int_neg ((abs_re_le_abs ε).trans hε.le),
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
    convert abs_exp_sub_sum_le_abs_mul_exp (ε * X ω) n using 4 with m hm
    · rw [mul_pow]
      ring
    · simp [mul_pow]
    · simp

lemma tendsto_integral_pow_abs_mul_exp (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
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
  · exact .of_forall fun h ↦ AEMeasurable.aestronglyMeasurable (by fun_prop)
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

lemma isBigO_abs_complexMGF_sub_sum (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    (fun ε ↦ complexMGF X μ (z + ε)
        - ∑ m in range n, ε ^ m / m.factorial * ∫ ω, X ω ^ m * cexp (z * X ω) ∂μ)
      =O[𝓝 0] fun ε ↦ (abs ε) ^ n := by
  have hz' := hz
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
      refine abs_complexMGF_add_sub_sum_le ?_ ?_ (hy.trans_le (le_abs_self _)) n
      · exact h_subset (add_half_inf_sub_mem_Ioo hlu)
      · exact h_subset (sub_half_inf_sub_mem_Ioo hlu)
    · exact isOpen_lt (by fun_prop) (by fun_prop)
  _ =O[𝓝 0] fun ε ↦ (abs ε) ^ n * 1 := by
    refine Asymptotics.IsBigO.mul (Asymptotics.isBigO_refl _ _) ?_
    refine Tendsto.isBigO_one _ (c := μ[fun ω ↦ |X ω| ^ n * rexp (z.re * X ω)]) ?_
    exact tendsto_integral_pow_abs_mul_exp hz n
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
    convert isBigO_abs_complexMGF_sub_sum hz 2 using 2
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

/-- `complexMGF X μ` is analytic at any point `z` with `z.re ∈ interior (integrableExpSet X μ)`. -/
lemma analyticAt_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) :
    AnalyticAt ℂ (complexMGF X μ) z := analyticOnNhd_complexMGF z hz

end Analytic

section Deriv

/-! ### Derivatives of `complexMGF` -/

/-- For `z : ℂ` with `z.re ∈ interior (integrableExpSet X μ)`, the derivative of the function
`z' ↦ μ[X ^ n * cexp (z' * X)]` at `z` is `μ[X ^ (n + 1) * cexp (z * X)]`. -/
lemma hasDerivAt_integral_pow_mul_exp (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (fun z ↦ μ[fun ω ↦ X ω ^ n * cexp (z * X ω)])
        μ[fun ω ↦ X ω ^ (n + 1) * cexp (z * X ω)] z := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  have hz' := hz
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hz'
  obtain ⟨l, u, hlu, h_subset⟩ := hz'
  let t := ((z.re - l) ⊓ (u - z.re)) / 2
  have h_pos : 0 < (z.re - l) ⊓ (u - z.re) := by simp [hlu.1, hlu.2]
  have ht : 0 < t := half_pos h_pos
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun ω ↦ |X ω| ^ (n + 1) * rexp (z.re * X ω + t/2 * |X ω|))
    (F := fun z ω ↦ X ω ^ n * cexp (z * X ω))
    (F' := fun z ω ↦ X ω ^ (n + 1) * cexp (z * X ω)) (half_pos ht) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact .of_forall fun z ↦ AEMeasurable.aestronglyMeasurable (by fun_prop)
  · rw [← integrable_norm_iff]
    swap; · exact AEMeasurable.aestronglyMeasurable (by fun_prop)
    simp only [norm_mul, Complex.norm_eq_abs, abs_ofReal, Complex.abs_exp, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero]
    convert integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet hz n
    simp
  · exact AEMeasurable.aestronglyMeasurable (by fun_prop)
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

/-- For `t : ℝ` with `t ∈ interior (integrableExpSet X μ)`, the derivative of the function
`x ↦ μ[X ^ n * rexp (x * X)]` at `t` is `μ[X ^ (n + 1) * rexp (t * X)]`. -/
lemma hasDerivAt_integral_pow_mul_exp_real (ht : t ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (fun t ↦ μ[fun ω ↦ X ω ^ n * rexp (t * X ω)])
      μ[fun ω ↦ X ω ^ (n + 1) * rexp (t * X ω)] t := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet ht
  have h_re_of_mem n t (ht' : t ∈ interior (integrableExpSet X μ)) :
      (∫ ω, X ω ^ n * cexp (t * X ω) ∂μ).re = ∫ ω, X ω ^ n * rexp (t * X ω) ∂μ := by
    rw [← RCLike.re_eq_complex_re, ← integral_re]
    · norm_cast
    · rw [← integrable_norm_iff]
      swap; · exact AEMeasurable.aestronglyMeasurable (by fun_prop)
      simp only [norm_mul, Complex.norm_eq_abs, abs_ofReal, Complex.abs_exp, mul_re, ofReal_re,
        ofReal_im, mul_zero, sub_zero, Complex.abs_pow]
      exact integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet ht' n
  have h_re n : ∀ᶠ t' : ℝ in 𝓝 t, (∫ ω, X ω ^ n * cexp (t' * X ω) ∂μ).re
      = ∫ ω, X ω ^ n * rexp (t' * X ω) ∂μ := by
    filter_upwards [isOpen_interior.eventually_mem ht] with t ht' using h_re_of_mem n t ht'
  rw [← EventuallyEq.hasDerivAt_iff (h_re _), ← h_re_of_mem _ t ht]
  exact (hasDerivAt_integral_pow_mul_exp (by simp [ht]) n).real_of_complex

lemma hasDerivAt_iteratedDeriv_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
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

/-- For `z : ℂ` with `z.re ∈ interior (integrableExpSet X μ)`, the n-th derivative of the function
`complexMGF X μ` at `z` is `μ[X ^ n * cexp (z * X)]`. -/
lemma iteratedDeriv_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    iteratedDeriv n (complexMGF X μ) z = μ[fun ω ↦ X ω ^ n * cexp (z * X ω)] := by
  induction n generalizing z with
  | zero => simp [complexMGF]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_complexMGF hz n).deriv

end Deriv

section EqOfMGF

/-! We prove that if two random variables have the same `mgf`, then
they also have the same `complexMGF`.-/

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Y : Ω' → ℝ} {μ' : Measure Ω'}

/-- If two random variables have the same moment generating function then they have
the same `integrableExpSet`. -/
lemma integrableExpSet_eq_of_mgf' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0) :
    integrableExpSet X μ = integrableExpSet Y μ' := by
  ext t
  simp only [integrableExpSet, Set.mem_setOf_eq]
  by_cases hμ : μ = 0
  · simp [hμ, hμμ'.mp hμ]
  have hμ' : μ' ≠ 0 := (not_iff_not.mpr hμμ').mp hμ
  rw [← mgf_pos_iff' hμ, ← mgf_pos_iff' hμ', hXY]

/-- If two random variables have the same moment generating function then they have
the `integrableExpSet`. -/
lemma integrableExpSet_eq_of_mgf [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hXY : mgf X μ = mgf Y μ') :
    integrableExpSet X μ = integrableExpSet Y μ' :=
  integrableExpSet_eq_of_mgf' hXY <| by simp [IsProbabilityMeasure.ne_zero]

/-- If two random variables have the same moment generating function then they have
the same `complexMGF` on the vertical strip `{z | z.re ∈ interior (integrableExpSet X μ)}`. -/
-- todo: the equality also holds on `(integrableExpSet X μ)ᶜ` since both are zero there. What about
-- the two (at most) vertical lines corresponding to the extemities of the interval?
lemma eqOn_complexMGF_of_mgf' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0) :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ') {z | z.re ∈ interior (integrableExpSet X μ)} := by
  by_cases h_empty : interior (integrableExpSet X μ) = ∅
  · simp [h_empty]
  rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at h_empty
  obtain ⟨t, ht⟩ := h_empty
  have hX : AnalyticOnNhd ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} :=
    analyticOnNhd_complexMGF
  have hY : AnalyticOnNhd ℂ (complexMGF Y μ') {z | z.re ∈ interior (integrableExpSet Y μ')} :=
    analyticOnNhd_complexMGF
  rw [integrableExpSet_eq_of_mgf' hXY hμμ'] at hX ht ⊢
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hX hY
    (convex_integrableExpSet.interior.linear_preimage reLm).isPreconnected
    (z₀ := (t : ℂ)) (by simp [ht]) ?_
  have h_real : ∃ᶠ (x : ℝ) in 𝓝[≠] t, complexMGF X μ x = complexMGF Y μ' x := by
    refine .of_forall fun y ↦ ?_
    rw [complexMGF_ofReal, complexMGF_ofReal, hXY]
  rw [frequently_iff_seq_forall] at h_real ⊢
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
  refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  · simp [hx_eq]

/-- If two random variables have the same moment generating function then they have
the same `complexMGF` on the vertical strip `{z | z.re ∈ interior (integrableExpSet X μ)}`. -/
lemma eqOn_complexMGF_of_mgf [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hXY : mgf X μ = mgf Y μ') :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ') {z | z.re ∈ interior (integrableExpSet X μ)} :=
  eqOn_complexMGF_of_mgf' hXY <| by simp [IsProbabilityMeasure.ne_zero]

end EqOfMGF

end ProbabilityTheory

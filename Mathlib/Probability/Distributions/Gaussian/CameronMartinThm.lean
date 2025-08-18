/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.CameronMartin
import Mathlib.Probability.HasLaw

/-!
# Cameron-Martin Theorem

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

-- todo: use the CM ↔ RKHS isometry to add a coe to fun for CameronMartin, and write this lemma
-- for CameronMartin?
lemma hasLaw_cameronMartinRKHS (x : cameronMartinRKHS μ) :
    HasLaw x (gaussianReal 0 (‖x‖₊ ^ 2)) μ where
  map_eq := by
    by_cases hx0 : x = 0
    · simp only [hx0, ZeroMemClass.coe_zero, nnnorm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, gaussianReal_zero_var]
      suffices μ.map (fun _ ↦ (0 : ℝ)) = Measure.dirac 0 by convert this; simp
      simp
    have hx_norm_pos : 0 < ‖x‖ := by simp [norm_pos_iff, hx0]
    unfold cameronMartinRKHS at x
    have h := x.2
    rw [Submodule.mem_topologicalClosure_iff, mem_closure_iff_seq_limit] at h
    obtain ⟨L, hL_mem, hL_tendsto⟩ := h
    simp only [Submodule.map_top, SetLike.mem_coe, LinearMap.mem_range] at hL_mem
    let L' := fun n ↦ (‖x‖ / ‖L n‖) • L n
    have hL'_mem n : ∃ y, StrongDual.centeredToLp μ 2 y = L' n := by
      choose y' hy' using hL_mem
      refine ⟨(‖x‖ / ‖L n‖) • y' n, ?_⟩
      simp [hy' n, L']
    have hL'_tendsto : Tendsto L' atTop (𝓝 x) := by
      unfold L'
      have h_norm : Tendsto (fun n ↦ ‖L n‖) atTop (𝓝 ‖x‖) := hL_tendsto.norm
      suffices Tendsto (fun n ↦ (‖x‖ / ‖L n‖) • L n) atTop (𝓝 ((‖x‖ / ‖x‖) • x)) by
        rwa [div_self hx_norm_pos.ne', one_smul] at this
      refine Tendsto.smul ?_ hL_tendsto
      exact Tendsto.div tendsto_const_nhds h_norm hx_norm_pos.ne'
    choose y hy using hL'_mem
    have hy_map' (n : ℕ) : μ.map (y n) = gaussianReal (μ[y n]) (‖x‖₊ ^ 2) := by
      rw [IsGaussian.map_eq_gaussianReal]
      congr
      sorry
    have hL'_map n : μ.map (L' n) = gaussianReal 0 (‖x‖₊ ^ 2) := by
      have h_eq : L' n =ᵐ[μ] fun x ↦ y n x - μ[y n] := by
        rw [← hy]
        filter_upwards [centeredToLp_apply (μ := μ) memLp_two_id (y n)] with z hz
        simp only [hz, map_sub, sub_right_inj]
        rw [IsGaussian.integral_dual]
      rw [Measure.map_congr h_eq]
      sorry
    have hL'_prob n : IsProbabilityMeasure (μ.map (L' n)) := by
      rw [hL'_map n]
      infer_instance
    let ν n : ProbabilityMeasure ℝ := ⟨μ.map (L' n), hL'_prob n⟩
    have hν_tendsto_1 : Tendsto ν atTop (𝓝 ⟨gaussianReal 0 (‖x‖₊ ^ 2), inferInstance⟩) := by
      unfold ν
      simp_rw [hL'_map]
      exact tendsto_const_nhds
    have hx_prob : IsProbabilityMeasure (μ.map (x : E → ℝ)) :=
      isProbabilityMeasure_map (by fun_prop)
    have hν_tendsto_2 : Tendsto ν atTop (𝓝 ⟨μ.map x, hx_prob⟩) := by
      sorry -- implied by convergence in L2
    have h_eq := tendsto_nhds_unique hν_tendsto_2 hν_tendsto_1
    rw [Subtype.ext_iff] at h_eq
    exact h_eq

lemma variance_cameronMartinRKHS (x : cameronMartinRKHS μ) :
    Var[x; μ] = ‖x‖₊ ^ 2 := by
  have : Var[fun y ↦ y; μ.map x] = ‖x‖₊ ^ 2 := by simp [(hasLaw_cameronMartinRKHS x).map_eq]
  rwa [variance_map aemeasurable_id' (by fun_prop)] at this

lemma covariance_cameronMartinRKHS (x y : cameronMartinRKHS μ) :
    cov[x, y; μ] = ⟪x, y⟫_ℝ := by
  rw [covariance_eq_variance_add_sub_div_two (Lp.memLp x.1) (Lp.memLp y.1)]
  have : (x : E → ℝ) + (y : E → ℝ) =ᵐ[μ] (x + y : cameronMartinRKHS μ) := by
    simp only [Submodule.coe_add, AddSubgroup.coe_add]
    exact (AEEqFun.coeFn_add _ _).symm
  rw [variance_congr this]
  simp_rw [variance_cameronMartinRKHS]
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  simp [pow_two]

lemma isProbabilityMeasure_withDensity_cameronMartin (x : CameronMartin μ) :
    IsProbabilityMeasure (μ.withDensity fun y ↦
      .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) y - ‖x‖ ^ 2 / 2))) where
  measure_univ := by
    rw [withDensity_apply _ .univ, setLIntegral_univ]
    calc ∫⁻ a, .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) a - ‖x‖ ^ 2 / 2)) ∂μ
    _ = .ofReal (.exp (- ‖x‖ ^ 2 / 2))
        * ∫⁻ a, .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) a)) ∂μ := by
      simp_rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [lintegral_mul_const _ (by fun_prop), mul_comm, neg_div]
    _ = .ofReal (.exp (- ‖x‖ ^ 2 / 2))
        * ∫⁻ a, .ofReal (.exp a) ∂(μ.map (cmIsometryEquiv μ x)) := by
      rw [lintegral_map (by fun_prop) (by fun_prop)]
    _ = .ofReal (.exp (- ‖x‖ ^ 2 / 2)) * ∫⁻ a, .ofReal (.exp a) ∂(gaussianReal 0 (‖x‖₊ ^ 2)) := by
      rw [(hasLaw_cameronMartinRKHS (cmIsometryEquiv μ x)).map_eq, (cmIsometryEquiv μ).nnnorm_map]
    _ = .ofReal (.exp (- ‖x‖ ^ 2 / 2)) * .ofReal (.exp (‖x‖ ^ 2 / 2)) := by
      congr
      have h := mgf_id_gaussianReal (μ := (0 : ℝ)) (v := ‖x‖₊ ^ 2)
      rw [funext_iff] at h
      specialize h 1
      simp only [mgf, id_eq, one_mul, mul_one, NNReal.coe_pow, coe_nnnorm, one_pow, zero_add] at h
      rw [← h, ofReal_integral_eq_lintegral_ofReal]
      · simpa using (integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := ‖x‖₊ ^ 2) 1)
      · exact ae_of_all _ fun _ ↦ Real.exp_nonneg _
    _ = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      ring_nf
      simp

lemma todo_ae_eq (x : CameronMartin μ) (L : StrongDual ℝ E) (t : ℝ) :
    (cmIsometryEquiv μ (L - t • x) : E → ℝ)
      =ᵐ[μ] fun u ↦ L u - μ[L] - t * (cmIsometryEquiv μ x : E → ℝ) u := by
  simp only [map_sub, map_smul, AddSubgroupClass.coe_sub, SetLike.val_smul]
  sorry

lemma some_equality_in_Real'' (x : CameronMartin μ) (L : StrongDual ℝ E) (t : ℝ) :
    ∫ u, Complex.exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * Complex.I
        - ‖x‖ ^ 2 / 2) ∂μ
      = .exp (- ‖x‖ ^ 2 / 2)
        * ∫ u, .exp ((cmIsometryEquiv μ (L - t • x) : E → ℝ) u * Complex.I
          + μ[L] * Complex.I) ∂μ := by
  calc ∫ u, Complex.exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * Complex.I
        - ‖x‖ ^ 2 / 2) ∂μ
  _ = .exp (- ‖x‖ ^ 2 / 2)
      * ∫ u, .exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * Complex.I) ∂μ := by
    simp_rw [sub_eq_add_neg, Complex.exp_add]
    rw [integral_mul_const, mul_comm (Complex.exp _), neg_div]
  _ = .exp (- ‖x‖ ^ 2 / 2)
      * ∫ u, .exp ((L u - μ[L] - t * (cmIsometryEquiv μ x : E → ℝ) u)
        * Complex.I + μ[L] * Complex.I) ∂μ := by
    congr with u
    congr
    ring
  _ = .exp (- ‖x‖ ^ 2 / 2)
      * ∫ u, .exp ((cmIsometryEquiv μ (L - t • x) : E → ℝ) u * Complex.I
        + μ[L] * Complex.I) ∂μ := by
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [todo_ae_eq x L t] with u hu
    rw [hu, integral_complex_ofReal]
    simp

lemma some_equality_in_Real' (x : CameronMartin μ) (L : StrongDual ℝ E) (t : ℝ) :
    ∫ u, Complex.exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * Complex.I
        - ‖x‖ ^ 2 / 2) ∂μ
      = .exp (- ‖x‖ ^ 2 / 2 + μ[L] * Complex.I)
        * ∫ u : ℝ, .exp (u * Complex.I) ∂(gaussianReal 0 (‖L - t • x‖₊ ^ 2)) := by
  calc ∫ u, Complex.exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * Complex.I
        - ‖x‖ ^ 2 / 2) ∂μ
  _ = .exp (- ‖x‖ ^ 2 / 2)
      * ∫ u, .exp ((cmIsometryEquiv μ (L - t • x) : E → ℝ) u * Complex.I
        + μ[L] * Complex.I) ∂μ := by
    exact some_equality_in_Real'' x L t
  _ = .exp (- ‖x‖ ^ 2 / 2)
      * ∫ u : ℝ, .exp (u * Complex.I + μ[L] * Complex.I)
        ∂(μ.map (cmIsometryEquiv μ (L - t • x))) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  _ = .exp (- ‖x‖ ^ 2 / 2)
      * ∫ u : ℝ, .exp (u * Complex.I + μ[L] * Complex.I)
        ∂(gaussianReal 0 (‖L - t • x‖₊ ^ 2)) := by
    rw [(hasLaw_cameronMartinRKHS (cmIsometryEquiv μ (L - t • x))).map_eq,
      (cmIsometryEquiv μ).nnnorm_map]
  _ = .exp (- ‖x‖ ^ 2 / 2 + μ[L] * Complex.I)
      * ∫ u : ℝ, .exp (u * Complex.I) ∂(gaussianReal 0 (‖L - t • x‖₊ ^ 2)) := by
    rw [Complex.exp_add, mul_assoc]
    congr 1
    simp_rw [Complex.exp_add]
    rw [integral_mul_const, mul_comm _ (Complex.exp _)]

lemma some_equality_in_Real (x : CameronMartin μ) (L : StrongDual ℝ E) (t : ℝ) :
    ∫ u, Complex.exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * Complex.I
        - ‖x‖ ^ 2 / 2) ∂μ
      = .exp (t * L x.toInitialSpace - (1 + t ^ 2) / 2 * ‖x‖ ^ 2
        + μ[L] * Complex.I - Var[L; μ] / 2) := by
  calc ∫ u, Complex.exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * Complex.I
        - ‖x‖ ^ 2 / 2) ∂μ
  _ = .exp (- ‖x‖ ^ 2 / 2 + μ[L] * Complex.I)
      * ∫ u : ℝ, .exp (u * Complex.I) ∂(gaussianReal 0 (‖L - t • x‖₊ ^ 2)) := by
    exact some_equality_in_Real' x L t
  _ = .exp (- ‖x‖ ^ 2 / 2 + μ[L] * Complex.I - ‖L - t • x‖ ^ 2 / 2) := by
    conv_lhs => rw [Complex.exp_add]
    conv_rhs => rw [add_sub_assoc, Complex.exp_add, sub_eq_add_neg, Complex.exp_add, ← mul_assoc]
    have h := charFun_gaussianReal (μ := 0) (v := ‖L - t • x‖₊ ^ 2) 1
    simp only [charFun, RCLike.inner_apply, conj_trivial, one_mul, Complex.ofReal_one,
      Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_pow, coe_nnnorm, Complex.ofReal_pow,
      one_pow, mul_one, zero_sub] at h
    rw [h]
  _ = .exp (t * L x.toInitialSpace - (1 + t ^ 2) / 2 * ‖x‖ ^ 2
        + μ[L] * Complex.I - Var[L; μ] / 2) := by
    have h_inner : (t : ℂ) * L x.toInitialSpace = ⟪.ofDual μ L, t • x⟫_ℝ := by
      simp [← CameronMartin.apply_toInitialSpace_eq_inner]
    rw [h_inner, real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    simp_rw [← pow_two]
    rw [CameronMartin.sq_norm_ofDual (μ := μ) L]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
    ring_nf

lemma some_equality_in_Complex (x : CameronMartin μ) (L : StrongDual ℝ E) (z : ℂ) :
    ∫ u, Complex.exp ((L u - z * (cmIsometryEquiv μ x : E → ℝ) u) * Complex.I
        - ‖x‖ ^ 2 / 2) ∂μ
      = .exp (z * L x.toInitialSpace - (1 + z ^ 2) / 2 * ‖x‖ ^ 2
        + μ[L] * Complex.I - Var[L; μ] / 2) := by
  revert z
  refine funext_iff.mp ?_
  rw [← Set.eqOn_univ]
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (𝕜 := ℂ) (E := ℂ) (z₀ := 0) ?_ ?_
    isPreconnected_univ (Set.mem_univ 0) ?_
  · simp_rw [sub_eq_add_neg, Complex.exp_add, integral_mul_const]
    refine AnalyticOnNhd.mul ?_ analyticOnNhd_const
    simp_rw [← sub_eq_add_neg]
    sorry
  · simp_rw [sub_eq_add_neg, Complex.exp_add]
    refine AnalyticOnNhd.mul ?_ analyticOnNhd_const
    refine AnalyticOnNhd.mul ?_ analyticOnNhd_const
    refine AnalyticOnNhd.mul ?_ ?_
    · exact (analyticOnNhd_id.mul analyticOnNhd_const).cexp
    · refine (AnalyticOnNhd.mul ?_ analyticOnNhd_const).neg.cexp
      exact (analyticOnNhd_const.add (analyticOnNhd_id.pow 2)).mul analyticOnNhd_const
  -- todo: extract lemma: frequently around a point in ℝ implies frequently around the point in ℂ.
  -- This is also used in ComplexMGF
  have h_real : ∃ᶠ (t : ℝ) in 𝓝[≠] 0,
      ∫ u, Complex.exp ((L u - t * (cmIsometryEquiv μ x : E → ℝ) u) * Complex.I
          - ‖x‖ ^ 2 / 2) ∂μ
        = .exp (t * L x.toInitialSpace - (1 + t ^ 2) / 2 * ‖x‖ ^ 2
          + μ[L] * Complex.I - Var[L; μ] / 2) :=
    .of_forall fun y ↦ some_equality_in_Real x L y
  rw [frequently_iff_seq_forall] at h_real ⊢
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
  refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · rw [← Complex.ofReal_zero, tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  · simp [hx_eq]

lemma cor_for_z_eq_I (x : CameronMartin μ) (L : StrongDual ℝ E) :
    ∫ u, Complex.exp (L u * Complex.I + (cmIsometryEquiv μ x : E → ℝ) u
        - ‖x‖ ^ 2 / 2) ∂μ
      = .exp ((μ[L] + L x.toInitialSpace) * Complex.I - Var[L; μ] / 2) := by
  have h := some_equality_in_Complex x L Complex.I
  simp only [Complex.I_sq, add_neg_cancel, zero_div, zero_mul, sub_zero] at h
  convert h using 3
  · congr
    rw [mul_comm Complex.I, sub_mul, mul_assoc]
    simp
  · ring

lemma charFunDual_withDensity_cameronMartin (x : CameronMartin μ) (L : StrongDual ℝ E) :
    charFunDual
        (μ.withDensity fun y ↦ .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) y - ‖x‖ ^ 2 / 2))) L
      = .exp ((μ[L] + L x.toInitialSpace) * Complex.I - Var[L; μ] / 2) := by
  calc charFunDual
        (μ.withDensity fun y ↦ .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) y - ‖x‖ ^ 2 / 2))) L
  _ = ∫ u, Complex.exp (L u * Complex.I + (cmIsometryEquiv μ x : E → ℝ) u
        - ‖x‖ ^ 2 / 2) ∂μ := by
    rw [charFunDual_apply, integral_withDensity_eq_integral_toReal_smul (by fun_prop)]
    swap; · exact ae_of_all _ (by finiteness)
    congr with u
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), add_sub_assoc, Complex.exp_add,
      mul_comm (Complex.exp _)]
    simp
  _ = .exp ((μ[L] + L x.toInitialSpace) * Complex.I - Var[L; μ] / 2) := cor_for_z_eq_I x L

theorem map_add_cameronMartin_eq_withDensity (x : CameronMartin μ) :
    μ.map (fun y ↦ y + x.toInitialSpace)
      = μ.withDensity (fun y ↦ .ofReal (.exp ((cmIsometryEquiv μ x : E → ℝ) y - ‖x‖ ^ 2 / 2))) := by
  have := isProbabilityMeasure_withDensity_cameronMartin x
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [charFunDual_map_add_const, IsGaussian.charFunDual_eq, ← Complex.exp_add,
    charFunDual_withDensity_cameronMartin x L]
  congr
  ring

theorem absolutelyContinuous_map_add_cameronMartin (x : CameronMartin μ) :
    μ.map (fun y ↦ y + x.toInitialSpace) ≪ μ := by
  rw [map_add_cameronMartin_eq_withDensity x]
  exact withDensity_absolutelyContinuous _ _

end ProbabilityTheory

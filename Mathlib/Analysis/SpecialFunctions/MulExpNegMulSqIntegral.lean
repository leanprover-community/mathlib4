/-
Copyright (c) 2025 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Properties of the integral of `mulExpNegMulSq`

The mapping `mulExpNegMulSq` can be used to transform a function `g : E → ℝ` into a bounded
function `mulExpNegMulSq ε ∘ g : E → ℝ = fun x => g x * Real.exp (-ε * g x * g x)`. This file
contains results on the integral of `mulExpNegMulSq g ε` with respect to a finite measure `P`.

## Lemmas

- `tendsto_integral_mulExpNegMulSq_comp`: By the dominated convergence theorem and
  `mulExpNegMulSq_abs_le_norm`, the integral of `mulExpNegMulSq ε ∘ g` with respect to a
  finite measure `P` converges to the integral of `g`, as `ε → 0`;
- `tendsto_integral_mul_one_add_inv_smul_sq_pow`: The integral of `mulExpNegMulSq ε ∘ g` with
  respect to a finite measure `P` can be approximated by the integral of the sequence approximating
  the exponential function, `fun x => (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x`. This allows to
  transfer properties of a subalgebra of functions containing `g` to the function
  `mulExpNegMulSq ε ∘ g`, see e.g. `integral_mulExpNegMulSq_comp_eq`.

## Main Result

`dist_integral_mulExpNegMulSq_comp_le`: For a subalgebra of functions `A`, if for any `g ∈ A` the
integral with respect to two finite measures `P, P'` coincide, then the difference of the integrals
of `mulExpNegMulSq ε ∘ g` with respect to `P, P'` is bounded by `6 * sqrt ε`.
This is a key ingredient in the proof of theorem `ext_of_forall_mem_subalgebra_integral_eq`, where
it is shown that a subalgebra of functions that separates points separates finite measures.
-/

open MeasureTheory Real NNReal ENNReal BoundedContinuousFunction Filter

open scoped Topology

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure E} [IsFiniteMeasure P] {ε : ℝ}

theorem integrable_mulExpNegMulSq_comp (f : C(E, ℝ)) (hε : 0 < ε) :
    Integrable (fun x => mulExpNegMulSq ε (f x)) P := by
  apply integrable P ⟨⟨fun x => mulExpNegMulSq ε (f x), by fun_prop⟩, ⟨2 * (sqrt ε)⁻¹, _⟩⟩
  exact fun x y => dist_mulExpNegMulSq_le_two_mul_sqrt hε (f x) (f y)

theorem integrable_mulExpNegMulSq_comp_restrict_of_isCompact {K : Set E} (hK : IsCompact K)
    (hKmeas : MeasurableSet K) (g : C(E, ℝ)) :
    Integrable (fun x => mulExpNegMulSq ε (g x)) (P.restrict K) :=
  g.continuous.mulExpNegMulSq.continuousOn.integrableOn_compact' hK hKmeas

/-- The integral of `mulExpNegMulSq ε ∘ g` with respect to a finite measure `P` converges to the
integral of `g`, as `ε → 0` from above. -/
theorem tendsto_integral_mulExpNegMulSq_comp (g : E →ᵇ ℝ) :
    Tendsto (fun ε => ∫ x, mulExpNegMulSq ε (g x) ∂P) (𝓝[>] 0) (𝓝 (∫ x, g x ∂P)) := by
  apply tendsto_of_seq_tendsto
  intro u hu
  obtain ⟨N, hupos⟩ := eventually_atTop.mp (tendsto_nhdsWithin_iff.mp hu).2
  apply tendsto_integral_filter_of_norm_le_const ?h_meas ?h_bound ?h_lim
  · exact Eventually.of_forall (fun n => g.continuous.mulExpNegMulSq.aestronglyMeasurable)
  · use norm g
    rw [eventually_atTop]
    use N
    intro n hn
    exact Eventually.of_forall
      (fun _ => abs_mulExpNegMulSq_comp_le_norm g (le_of_lt (Set.mem_Ioi.mp (hupos n hn))))
  · exact Eventually.of_forall (fun _ => (tendsto_nhdsWithin_of_tendsto_nhds
        tendsto_mulExpNegMulSq).comp hu)

/-- The integral of `mulExpNegMulSq ε ∘ g` with respect to a finite measure `P` can be
approximated by the integral of the sequence approximating the exponential function. -/
theorem tendsto_integral_mul_one_add_inv_smul_sq_pow (g : E →ᵇ ℝ) (hε : 0 < ε) :
    Tendsto (fun (n : ℕ) => ∫ x, (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂ P)
    atTop (𝓝 (∫ x, mulExpNegMulSq ε (g x) ∂P)) := by
  apply tendsto_integral_filter_of_norm_le_const ?h_meas ?h_bound ?h_lim
  · apply Eventually.of_forall
    exact fun n => StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable
        (Continuous.mul g.continuous ((1 + ((n : ℝ)⁻¹ • -(ε • g * g))) ^ n).continuous))
  · obtain ⟨N, hgN⟩ := exists_nat_gt (ε * (norm g * norm g))
    use norm g
    rw [eventually_atTop]
    use N
    intro n hn
    have hnpos : 0 < (n : ℝ) := by
      apply lt_of_lt_of_le (lt_of_le_of_lt _ hgN) (Nat.cast_le.mpr hn)
      exact (mul_nonneg (le_of_lt hε) (mul_self_nonneg (norm g)))
    apply Eventually.of_forall
    intro x
    simp only [smul_neg, BoundedContinuousFunction.coe_mul, Pi.mul_apply, pow_apply,
      BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_one, coe_neg,
      BoundedContinuousFunction.coe_smul, smul_eq_mul, Pi.add_apply, Pi.one_apply, Pi.neg_apply,
      norm_mul, norm_eq_abs, norm_pow]
    refine (mul_le_mul_of_nonneg_right (norm_coe_le_norm g x) (pow_nonneg (abs_nonneg _) n)).trans
      <| mul_le_of_le_one_right (norm_nonneg _) ?_
    apply pow_le_one₀ (abs_nonneg _)
    rw [mul_assoc, inv_mul_eq_div, abs_le]
    refine ⟨?_, (add_le_iff_nonpos_right 1).mpr (Left.neg_nonpos_iff.mpr
      (div_nonneg (mul_nonneg (le_of_lt hε) (mul_self_nonneg (g x))) (le_of_lt hnpos)))⟩
    apply le_trans (by linarith) (sub_nonneg_of_le ((div_le_one hnpos).mpr _))
    apply le_trans (le_trans _ (le_of_lt hgN)) (Nat.cast_le.mpr hn)
    apply mul_le_mul (Preorder.le_refl ε) _ (mul_self_nonneg (g x)) (le_of_lt hε)
    rw [← abs_le_iff_mul_self_le, abs_norm]
    exact norm_coe_le_norm g x
  · apply Eventually.of_forall
    intro x
    apply Tendsto.const_mul (g x)
    simp [mul_assoc, inv_mul_eq_div, ← neg_div]
    exact tendsto_one_add_div_pow_exp (-(ε * (g x * g x)))

theorem integral_mulExpNegMulSq_comp_eq {P' : Measure E} [IsFiniteMeasure P']
    {A : Subalgebra ℝ (E →ᵇ ℝ)} (hε : 0 < ε)
    (heq : ∀ g ∈ A, ∫ x, (g : E → ℝ) x ∂P = ∫ x, (g : E → ℝ) x ∂P') {g : E →ᵇ ℝ} (hgA : g ∈ A) :
    ∫ x, mulExpNegMulSq ε (g x) ∂P = ∫ x, mulExpNegMulSq ε (g x) ∂P' := by
  have one_add_inv_mul_mem (n : ℕ) : g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n ∈ A := by
    apply Subalgebra.mul_mem A hgA (Subalgebra.pow_mem A _ n)
    apply Subalgebra.add_mem A (Subalgebra.one_mem A) (Subalgebra.smul_mem A _ n⁻¹)
    exact Subalgebra.neg_mem A (Subalgebra.mul_mem A (Subalgebra.smul_mem A hgA ε) hgA)
  have limP : Tendsto (fun n : ℕ => ∫ x, (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂P) atTop
      (𝓝 (∫ x, mulExpNegMulSq ε (g x) ∂P')) := by
    rw [funext fun n => heq _ (one_add_inv_mul_mem n)]
    exact tendsto_integral_mul_one_add_inv_smul_sq_pow g hε
  exact tendsto_nhds_unique
    (tendsto_integral_mul_one_add_inv_smul_sq_pow g hε) limP

theorem abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt (f : C(E, ℝ))
    {K : Set E} (hK : MeasurableSet K) (hε : 0 < ε) (hKP : P Kᶜ < ε.toNNReal) :
    |∫ x, mulExpNegMulSq ε (f x) ∂P - ∫ x in K, mulExpNegMulSq ε (f x) ∂P| < sqrt ε := by
  apply lt_of_le_of_lt (norm_integral_sub_setIntegral_le
    (Eventually.of_forall (fun _ => abs_mulExpNegMulSq_le hε)) hK
    (integrable_mulExpNegMulSq_comp f hε))
  rw [mul_inv_lt_iff₀ (sqrt_pos_of_pos hε), mul_self_sqrt (le_of_lt hε)]
  exact toReal_lt_of_lt_ofReal hKP

theorem abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure {K : Set E} (hK : IsCompact K)
    (hKmeas : MeasurableSet K) (f g : C(E, ℝ)) {δ : ℝ} (hε : 0 < ε)
    (hfg : ∀ x ∈ K, |g x - f x| < δ) :
    |∫ x in K, mulExpNegMulSq ε (g x) ∂P - ∫ x in K, mulExpNegMulSq ε (f x) ∂P|
      ≤ δ * (P K).toReal := by
  rw [← (integral_sub (integrable_mulExpNegMulSq_comp_restrict_of_isCompact hK hKmeas g)
      (integrable_mulExpNegMulSq_comp_restrict_of_isCompact hK hKmeas f))]
  apply norm_setIntegral_le_of_norm_le_const hK.measure_lt_top
    (fun x hxK => le_trans (dist_mulExpNegMulSq_le_dist hε) (hfg x hxK).le)
    (StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable
    (Continuous.sub g.continuous.mulExpNegMulSq f.continuous.mulExpNegMulSq)))

variable {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
    {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure P']

/-- If for any `g ∈ A` the integrals with respect to two finite measures `P, P'` coincide, then the
difference of the integrals of `mulExpNegMulSq ε ∘ g` with respect to `P, P'` is bounded by
`6 * sqrt ε`. -/
theorem dist_integral_mulExpNegMulSq_comp_le (f : E →ᵇ ℝ)
    {A : Subalgebra ℝ (E →ᵇ ℝ)} (hA : (A.map (toContinuousMapₐ ℝ)).SeparatesPoints)
    (heq : ∀ g ∈ A, ∫ x, (g : E → ℝ) x ∂P = ∫ x, (g : E → ℝ) x ∂P') (hε : 0 < ε) :
    |∫ x, mulExpNegMulSq ε (f x) ∂P - ∫ x, mulExpNegMulSq ε (f x) ∂P'| ≤ 6 * sqrt ε := by
  -- if both measures are zero, the result is trivial
  by_cases hPP' : P = 0 ∧ P' = 0
  · simp only [hPP', integral_zero_measure, sub_self, abs_zero, gt_iff_lt, Nat.ofNat_pos,
    mul_nonneg_iff_of_pos_left, (le_of_lt (sqrt_pos_of_pos hε))]
  let const : ℝ := (max (P Set.univ).toReal (P' Set.univ).toReal)
  have pos_of_measure : 0 < const := by
    rw [not_and_or] at hPP'
    rcases hPP' with hP0 | hP'0
    · exact lt_max_of_lt_left
        (toReal_pos ((Measure.measure_univ_ne_zero).mpr hP0) (measure_ne_top P Set.univ))
    · exact lt_max_of_lt_right
        (toReal_pos ((Measure.measure_univ_ne_zero).mpr hP'0) (measure_ne_top P' Set.univ))
  -- obtain K, a compact and closed set, which covers E up to a small area of measure at most ε
  -- wrt to both P and P'
  obtain ⟨KP, _, hKPco, hKPcl, hKP⟩ := MeasurableSet.exists_isCompact_isClosed_diff_lt
    (MeasurableSet.univ) (measure_ne_top P Set.univ) (ne_of_gt (ofReal_pos.mpr hε))
  obtain ⟨KP', _, hKP'co, hKP'cl, hKP'⟩ := MeasurableSet.exists_isCompact_isClosed_diff_lt
    (MeasurableSet.univ) (measure_ne_top P' Set.univ) (ne_of_gt (ofReal_pos.mpr hε))
  let K := KP ∪ KP'
  have hKco := IsCompact.union hKPco hKP'co
  have hKcl := IsClosed.union hKPcl hKP'cl
  simp [← Set.compl_eq_univ_diff] at hKP hKP'
  have hKPbound : P (KP ∪ KP')ᶜ < ε.toNNReal := lt_of_le_of_lt
        (measure_mono (Set.compl_subset_compl_of_subset (Set.subset_union_left))) hKP
  have hKP'bound : P' (KP ∪ KP')ᶜ < ε.toNNReal := lt_of_le_of_lt
        (measure_mono (Set.compl_subset_compl_of_subset (Set.subset_union_right))) hKP'
  -- stone-weierstrass approximation of f on K
  obtain ⟨g', hg'A, hg'approx⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      hA f hKco (Left.mul_pos (sqrt_pos_of_pos hε) (inv_pos_of_pos pos_of_measure))
  simp only [Subalgebra.mem_map] at hg'A
  let g := hg'A.choose
  have hgA : g ∈ A := hg'A.choose_spec.1
  have hgapprox : ∀ x ∈ K, ‖g x - f x‖ < sqrt ε * const⁻¹ := by
    rw [← coe_toContinuousMapₐ ℝ g, hg'A.choose_spec.2]
    exact hg'approx
  -- collect the results needed in the decomposition at the end of the proof
  have line1 : |∫ x, mulExpNegMulSq ε (f x) ∂P
      - ∫ x in K, mulExpNegMulSq ε (f x) ∂P| < sqrt ε :=
    abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      f (IsClosed.measurableSet hKcl) hε hKPbound
  have line3 : |∫ x in K, mulExpNegMulSq ε (g x) ∂P
      - ∫ x, mulExpNegMulSq ε (g x) ∂P| < sqrt ε := by
    rw [abs_sub_comm]
    exact (abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      g (IsClosed.measurableSet hKcl) hε hKPbound)
  have line5 : |∫ x, mulExpNegMulSq ε (g x) ∂P'
      - ∫ x in K, mulExpNegMulSq ε (g x) ∂P'| < sqrt ε :=
    (abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      g (IsClosed.measurableSet hKcl) hε hKP'bound)
  have line7 : |∫ x in K, mulExpNegMulSq ε (f x) ∂P'
      - ∫ x, mulExpNegMulSq ε (f x) ∂P'| < sqrt ε := by
    rw [abs_sub_comm]
    exact (abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      f (IsClosed.measurableSet hKcl) hε hKP'bound)
  have line2 : |∫ x in K, mulExpNegMulSq ε (f x) ∂P
      - ∫ x in K, mulExpNegMulSq ε (g x) ∂P| ≤ sqrt ε := by
    rw [abs_sub_comm]
    apply le_trans (abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure hKco
      (IsClosed.measurableSet hKcl) f g hε hgapprox)
    rw [mul_assoc]
    apply mul_le_of_le_one_right (le_of_lt (sqrt_pos_of_pos hε))
    apply inv_mul_le_one_of_le₀ (le_max_of_le_left _) (le_of_lt pos_of_measure)
    exact (toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mpr
        (measure_mono (Set.subset_univ _))
  have line6 : |∫ x in K, mulExpNegMulSq ε (g x) ∂P'
      - ∫ x in K, mulExpNegMulSq ε (f x) ∂P'| ≤ sqrt ε := by
    apply le_trans (abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure hKco
      (IsClosed.measurableSet hKcl) f g hε hgapprox)
    rw [mul_assoc]
    apply mul_le_of_le_one_right (le_of_lt (sqrt_pos_of_pos hε))
    apply inv_mul_le_one_of_le₀ (le_max_of_le_right _) (le_of_lt pos_of_measure)
    exact (toReal_le_toReal (measure_ne_top P' _) (measure_ne_top P' _)).mpr
        (measure_mono (Set.subset_univ _))
  have line4 : |∫ x, mulExpNegMulSq ε (g x) ∂P
      - ∫ x, mulExpNegMulSq ε (g x) ∂P'| = 0 := by
    rw [abs_eq_zero, sub_eq_zero]
    exact integral_mulExpNegMulSq_comp_eq hε heq hgA
  calc
      |∫ x, mulExpNegMulSq ε (f x) ∂P - ∫ x, mulExpNegMulSq ε (f x) ∂P'|
    ≤ |∫ x, mulExpNegMulSq ε (f x) ∂P - ∫ x in K, mulExpNegMulSq ε (f x) ∂P|
      + |∫ x in K, mulExpNegMulSq ε (f x) ∂P - ∫ x in K, mulExpNegMulSq ε (g x) ∂P|
      + |∫ x in K, mulExpNegMulSq ε (g x) ∂P - ∫ x, mulExpNegMulSq ε (g x) ∂P|
      + |∫ x, mulExpNegMulSq ε (g x) ∂P - ∫ x, mulExpNegMulSq ε (g x) ∂P'|
      + |∫ x, mulExpNegMulSq ε (g x) ∂P' - ∫ x in K, mulExpNegMulSq ε (g x) ∂P'|
      + |∫ x in K, mulExpNegMulSq ε (g x) ∂P' - ∫ x in K, mulExpNegMulSq ε (f x) ∂P'|
      + |∫ x in K, mulExpNegMulSq ε (f x) ∂P' - ∫ x, mulExpNegMulSq ε (f x) ∂P'| :=
        @dist_triangle8 ℝ _ _ _ _ _ _ _ _ _
  _ ≤ 6 * sqrt ε := by linarith

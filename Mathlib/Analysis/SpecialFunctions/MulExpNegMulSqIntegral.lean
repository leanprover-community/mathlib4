/-
Copyright (c) 2025 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Properties of the integral of `mulExpNegMulSq`
The mapping `mulExpNegMulSq` can be used to transform a function `g : E → ℝ` into a bounded
function `(mulExpNegMulSq ε).comp g : E → ℝ = fun x => g x * Real.exp (-ε * g x * g x)`. This file
contains results on the integral of `mulExpNegMulSq g ε` with respect to a finite measure `P`.
## Lemmas
- `tendsto_integral_mulExpNegMulSq_comp`: By the dominated convergence theorem and
  `mulExpNegMulSq_abs_le_norm`, the integral of `(mulExpNegMulSq ε).comp g` with respect to a
  finite measure `P` converges to the integral of `g`, as `ε → 0`;
- `tendsto_integral_one_plus_inv_mul`: The integral of `(mulExpNegMulSq ε).comp g` with
  respect to a finite measure `P` can be approximated by the integral of the sequence approximating
  the exponential function, `fun x => (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x`. This allows to
  transfer properties of a subalgebra of functions containing `g` to the function
  `(mulExpNegMulSq ε).comp g`, see e.g. `integral_mulExpNegMulSq_comp_eq`.
## Main Result
`dist_integral_mulExpNegMulSq_comp_le`: For a subalgebra of functions `A`, if for any `g ∈ A` the
integral with respect to two finite measures `P, P'` coincide, then the difference of the integrals
of `(mulExpNegMulSq ε).comp g` with respect to `P, P'` is bounded by `6 * ε.sqrt`.
This is a key ingredient in the proof of theorem `ext_of_forall_mem_subalgebra_integral_eq`,
where it is shown that a subalgebra of functions that separates points separates finite measures.
-/

open MeasureTheory Real NNReal ENNReal BoundedContinuousFunction Filter

variable {E: Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) [IsFiniteMeasure P]

/--
the integral of `(mulExpNegMulSq ε).comp g` with respect to a finite measure `P` converges to the
integral of `g`, as `ε → 0` from above.
-/
theorem tendsto_integral_mulExpNegMulSq_comp (g : BoundedContinuousFunction E ℝ) :
    Tendsto (fun ε => ∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ (x : E), g x ∂P)) := by
  apply tendsto_of_seq_tendsto
  intro u hu
  obtain ⟨N, hupos⟩ := eventually_atTop.mp (tendsto_nhdsWithin_iff.mp hu).2
  have hbound : ∃ C, ∀ᶠ (n : ℕ) in Filter.atTop, ∀ᵐ (x : E) ∂P,
      |(mulExpNegMulSq (u n)).comp g x| ≤ C := by
    use norm g
    rw [eventually_atTop]
    use N; intro n hn
    exact Eventually.of_forall
      (fun _ => abs_mulExpNegMulSq_comp_le_norm g (le_of_lt (Set.mem_Ioi.mp (hupos n hn))))
  have hlim : ∀ᵐ (x : E) ∂P, Filter.Tendsto (fun (n : ℕ) => (mulExpNegMulSq (u n)).comp g x)
      Filter.atTop (nhds (g x)) := Eventually.of_forall
        (fun _ => (tendsto_nhdsWithin_of_tendsto_nhds
          tendsto_mulExpNegMulSq_comp).comp hu)
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => (mulExpNegMulSq (u n)).comp g x) P :=
    fun n => StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable
      (by simp [mulExpNegMulSq]; continuity))
  exact FiniteMeasure.tendstoIntegral_of_eventually_boundedPointwise
    (Eventually.of_forall hmeas) hbound hlim

/--
The integral of `(mulExpNegMulSq ε).comp g` with respect to a finite measure `P` can be
approximated by the integral of the sequence approximating the exponential function.
-/
theorem tendsto_integral_one_plus_inv_mul (g : BoundedContinuousFunction E ℝ)
    {ε : ℝ} (hε : ε > 0) :
    Filter.Tendsto (fun (n : ℕ) => ∫ (x : E), (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂ P)
    Filter.atTop (nhds (∫ (x : E), (mulExpNegMulSq ε).comp g x ∂ P)) := by
  apply FiniteMeasure.tendstoIntegral_of_eventually_boundedPointwise ?h_meas ?h_bound ?h_lim
  --measurability
  · apply Eventually.of_forall
    exact fun n => StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable
        (Continuous.mul g.continuous ((1 + ((n : ℝ)⁻¹ • -(ε • g * g))) ^ n).continuous))
  --boundedness
  · obtain ⟨N, hgN⟩ := exists_nat_gt (ε * (norm g * norm g))
    use norm g
    rw [eventually_atTop]
    use N; intro n hn
    have hnpos : 0 < (n : ℝ) := by
      apply lt_of_lt_of_le (lt_of_le_of_lt _ hgN) (Nat.cast_le.mpr hn)
      exact (mul_nonneg (le_of_lt hε) (mul_self_nonneg (norm g)))
    apply Eventually.of_forall
    intro x; simp
    refine mul_le_of_le_of_le_one' (BoundedContinuousFunction.norm_coe_le_norm g x) ?_
      (pow_nonneg (abs_nonneg _) n) (norm_nonneg _)
    apply pow_le_one₀ (abs_nonneg _)
    rw [mul_assoc, inv_mul_eq_div, abs_le]
    refine ⟨?_, (add_le_iff_nonpos_right 1).mpr (Left.neg_nonpos_iff.mpr
      (div_nonneg (mul_nonneg (le_of_lt hε) (mul_self_nonneg (g x))) (le_of_lt hnpos)))⟩
    apply le_trans (by linarith) (sub_nonneg_of_le ((div_le_one hnpos).mpr _))
    apply le_trans (le_trans _ (le_of_lt hgN)) (Nat.cast_le.mpr hn)
    apply mul_le_mul (Preorder.le_refl ε) _ (mul_self_nonneg (g x)) (le_of_lt hε)
    rw [← abs_le_iff_mul_self_le, abs_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm g x
  -- pointwise convergence
  · apply Eventually.of_forall
    intro x
    apply Filter.Tendsto.const_mul (g x)
    simp [mul_assoc, inv_mul_eq_div, ← neg_div]
    exact tendsto_one_plus_div_pow_exp (-(ε * (g x * g x)))

theorem integral_mulExpNegMulSq_comp_eq {P' : Measure E} [IsFiniteMeasure P']
    {A : Subalgebra ℝ C(E, ℝ)} {ε : ℝ} (hε : ε > 0)
    (hbound : ∀ g ∈ A, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C)
    (heq : ∀ g ∈ A, ∫ (x : E), (g : E → ℝ) x ∂P = ∫ (x : E), (g : E → ℝ) x ∂P') :
    ∀ (g : A), ∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P
        = ∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P' := by
  rintro ⟨g, hgA⟩
  obtain ⟨C, h⟩ := hbound g hgA
  have hmem (n : ℕ) : g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n ∈ A := by
    apply Subalgebra.mul_mem A hgA (Subalgebra.pow_mem A _ n)
    apply Subalgebra.add_mem A (Subalgebra.one_mem A) (Subalgebra.smul_mem A _ n⁻¹)
    exact Subalgebra.neg_mem A (Subalgebra.mul_mem A (Subalgebra.smul_mem A hgA ε) hgA)
  have limP : Tendsto (fun n : ℕ => ∫ (x : E), (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂P) atTop
      (nhds (∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P')) := by
    rw [funext (fun n => heq _ (hmem n))]
    exact tendsto_integral_one_plus_inv_mul P' (mkOfBound g C h) hε
  exact tendsto_nhds_unique (tendsto_integral_one_plus_inv_mul P (mkOfBound g C h) hε) limP

theorem abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt (f : C(E, ℝ))
    {K : Set E} (hK : MeasurableSet K) {ε : ℝ} (hε : ε > 0) (hKP : P Kᶜ < ε.toNNReal) :
    |∫ (x : E), (mulExpNegMulSq ε).comp f x ∂P
    - ∫ x in K, (mulExpNegMulSq ε).comp f x ∂P| < ε.sqrt := by
  have hbound : ∀ᵐ (x : E) ∂P, ‖(mulExpNegMulSq ε).comp f x‖ ≤ ε.sqrt⁻¹ :=
    Eventually.of_forall (fun _ => abs_mulExpNegMulSq_comp_le hε)
  have hint : Integrable ((mulExpNegMulSq ε).comp f) P := by
    apply BoundedContinuousFunction.integrable P
      ⟨⟨(mulExpNegMulSq ε).comp f, continuous_mulExpNegMulSq_comp f.continuous⟩, ⟨2 * ε.sqrt⁻¹, _⟩⟩
    exact dist_mulExpNegMulSq_comp_le_two_mul_sqrt hε
  apply lt_of_le_of_lt (norm_integral_sub_setIntegral_le hbound hK hint)
  rw [mul_inv_lt_iff₀ (Real.sqrt_pos_of_pos hε), mul_self_sqrt (le_of_lt hε)]
  exact (ENNReal.toReal_lt_of_lt_ofReal hKP)

theorem abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure {K : Set E} (hK : IsCompact K)
    (hKmeas : MeasurableSet K) (f g : C(E, ℝ)) {ε δ : ℝ} (hε : ε > 0)
    {P : Measure E} [hP : IsFiniteMeasure P] (hfg : ∀ x ∈ K, abs (g x - f x) < δ) :
    abs (∫ x in K, (mulExpNegMulSq ε).comp g x ∂P
      - ∫ x in K, (mulExpNegMulSq ε).comp f x ∂P) ≤ δ * (P K).toReal := by
  have integrable_mulExpNegMulSq (g : C(E, ℝ)) :
      Integrable (fun x ↦ (mulExpNegMulSq ε).comp g x) (P.restrict K) :=
    ContinuousOn.integrableOn_compact' hK hKmeas
      (Continuous.continuousOn (continuous_mulExpNegMulSq_comp g.continuous))
  rw [← (integral_sub (integrable_mulExpNegMulSq g) (integrable_mulExpNegMulSq f))]
  have h_norm_le (x : E) (hxK : x ∈ K) :
      norm ((mulExpNegMulSq ε).comp g x - (mulExpNegMulSq ε).comp f x) ≤ δ :=
    le_trans (dist_mulExpNegMulSq_comp_le_dist hε) (le_of_lt (hfg x hxK))
  apply norm_setIntegral_le_of_norm_le_const (IsCompact.measure_lt_top hK) h_norm_le
    (StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable _))
  simp [mulExpNegMulSq]
  continuity

section dist_integral

variable {E: Type*} [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
    {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure P']

/--
If for any `g ∈ A` the integrals with respect to two finite measures `P, P'` coincide, then the
difference of the integrals of `(mulExpNegMulSq ε).comp g` with respect to `P, P'` is bounded by
`6 * ε.sqrt`.
-/
theorem dist_integral_mulExpNegMulSq_comp_le (f : BoundedContinuousFunction E ℝ)
    {A : Subalgebra ℝ C(E, ℝ)} (hA : A.SeparatesPoints)
    (hbound : ∀ g ∈ A, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C)
    (heq : ∀ g ∈ A, ∫ (x : E), (g : E → ℝ) x ∂P = ∫ (x : E), (g : E → ℝ) x ∂P')
    {ε : ℝ} (hε : 0 < ε) :
    abs (∫ (x : E), (mulExpNegMulSq ε).comp f x ∂P
      - ∫ (x : E), (mulExpNegMulSq ε).comp f x ∂P') ≤ 6 * ε.sqrt := by
  -- if both measures are zero, the result is trivial
  by_cases hPP' : P = 0 ∧ P' = 0
  · simp only [hPP', integral_zero_measure, sub_self, abs_zero, gt_iff_lt, Nat.ofNat_pos,
    mul_nonneg_iff_of_pos_left, (le_of_lt (Real.sqrt_pos_of_pos hε))]
  let const : ℝ := (max (P Set.univ).toReal (P' Set.univ).toReal)
  have pos_of_measure : const > 0 := by
    rw [Mathlib.Tactic.PushNeg.not_and_or_eq] at hPP'
    cases' hPP' with hP0 hP'0
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
  obtain ⟨g, hgA, hgapprox⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_on_compact_of_separatesPoints
      hA f hKco (Left.mul_pos (Real.sqrt_pos_of_pos hε) (inv_pos_of_pos pos_of_measure))
  -- collect the results needed in the decomposition at the end of the proof
  have line1 : abs (∫ (x : E), (mulExpNegMulSq ε).comp f x ∂P
      - ∫ x in K, (mulExpNegMulSq ε).comp f x ∂P) < ε.sqrt :=
    abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      P f (IsClosed.measurableSet hKcl) hε hKPbound
  have line3 : abs (∫ x in K, (mulExpNegMulSq ε).comp g x ∂P
      - ∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P) < ε.sqrt := by
    rw [abs_sub_comm]
    apply (abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      P g (IsClosed.measurableSet hKcl) hε hKPbound)
  have line5 : abs (∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P'
      - ∫ x in K, (mulExpNegMulSq ε).comp g x ∂P') < ε.sqrt :=
    (abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      P' g (IsClosed.measurableSet hKcl) hε hKP'bound)
  have line7 : abs (∫ x in K, (mulExpNegMulSq ε).comp f x ∂P'
      - ∫ (x : E), (mulExpNegMulSq ε).comp f x ∂P') < ε.sqrt := by
    rw [abs_sub_comm]
    apply (abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      P' f (IsClosed.measurableSet hKcl) hε hKP'bound)
  have line2 : abs (∫ x in K, (mulExpNegMulSq ε).comp f x ∂P
      - ∫ x in K, (mulExpNegMulSq ε).comp g x ∂P) ≤ ε.sqrt := by
    rw [abs_sub_comm]
    apply le_trans (abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure hKco
      (IsClosed.measurableSet hKcl) f g hε hgapprox)
    rw [mul_assoc]
    apply mul_le_of_le_one_right (le_of_lt (Real.sqrt_pos_of_pos hε))
    apply inv_mul_le_one_of_le₀ (le_max_of_le_left _) (le_of_lt pos_of_measure)
    exact (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mpr
        (measure_mono (Set.subset_univ _))
  have line6 : abs (∫ x in K, (mulExpNegMulSq ε).comp g x ∂P'
      - ∫ x in K, (mulExpNegMulSq ε).comp f x ∂P') ≤ ε.sqrt := by
    apply le_trans (abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure hKco
      (IsClosed.measurableSet hKcl) f g hε hgapprox)
    rw [mul_assoc]
    apply mul_le_of_le_one_right (le_of_lt (Real.sqrt_pos_of_pos hε))
    apply inv_mul_le_one_of_le₀ (le_max_of_le_right _) (le_of_lt pos_of_measure)
    exact (ENNReal.toReal_le_toReal (measure_ne_top P' _) (measure_ne_top P' _)).mpr
        (measure_mono (Set.subset_univ _))
  have line4 : abs (∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P
      - ∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P') = 0 := by
    rw [abs_eq_zero, sub_eq_zero]
    apply integral_mulExpNegMulSq_comp_eq P hε hbound heq ⟨g, hgA⟩
  calc
    abs (∫ (x : E), (mulExpNegMulSq ε).comp f x ∂P
        - ∫ (x : E), (mulExpNegMulSq ε).comp f x ∂P')
      ≤ abs (∫ (x : E), (mulExpNegMulSq ε).comp f x ∂P
            - ∫ x in K, (mulExpNegMulSq ε).comp f x ∂P)
        + abs (∫ x in K, (mulExpNegMulSq ε).comp f x ∂P
            - ∫ x in K, (mulExpNegMulSq ε).comp g x ∂P)
        + abs (∫ x in K, (mulExpNegMulSq ε).comp g x ∂P
            - ∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P)
        + abs (∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P
            - ∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P')
        + abs (∫ (x : E), (mulExpNegMulSq ε).comp g x ∂P'
            - ∫ x in K, (mulExpNegMulSq ε).comp g x ∂P')
        + abs (∫ x in K, (mulExpNegMulSq ε).comp g x ∂P'
            - ∫ x in K, (mulExpNegMulSq ε).comp f x ∂P')
        + abs (∫ x in K, (mulExpNegMulSq ε).comp f x ∂P'
            - ∫ (x : E), (mulExpNegMulSq ε).comp f x ∂P') := @dist_triangle8 ℝ _ _ _ _ _ _ _ _ _
    _ ≤ 6 * ε.sqrt := by linarith

end dist_integral

/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.MulExpNegSq
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Properties of the integral of mulExpNegMulSq

The mapping mulExpNegMulSq transforms a continuous function `g` into another continuous function
`mulExpNegMulSq g ε : fun x => g x * Real.exp (-ε * g x * g x)`. This file contains results on
the integral of `mulExpNegMulSq g ε` with respect to a finite measure `P`.

## Lemmas

- `integral_mulExpNegMulSq_tendsto`: By the dominated convergence theorem and
  `mulExpNegMulSq_abs_le_norm`, the integral of `mulExpNegMulSq g ε` with respect to a finite
  measure `P` converges to the integral of `g`, as `ε → 0`;
- `tendsto_integral_expSeq_mulExpNegMulSq`: The integral of `mulExpNegMulSq g ε` with respect to
  a finite measure `P` can be approximated by the integral of the sequence approximating the
  exponential function, `fun x => (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x`. This allows to
  transfer properties of a subalgebra of functions containing `g` to the function
  `mulExpNegMulSq g ε`, see e.g. `integral_mulExpNegMulSq_eq`.

## Main Result

`dist_integral_mulExpNegMulSq_le`: For a subalgebra of functions `A`, if for any `g ∈ A` the
integral with respect to two finite measures `P, P'` coincide, then the difference of the integrals
of `mulExpNegMulSq g ε` with respect to `P, P'` is bounded by `6 * ε.sqrt`.
This is a key ingredient in the proof of theorem `ext_of_forall_mem_subalgebra_integral_eq`,
where it is shown that a subalgebra of functions that separates points separates finite measures.
-/

open MeasureTheory NNReal ENNReal BoundedContinuousFunction Filter

variable {E: Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) [IsFiniteMeasure P]

/--
the integral of `mulExpNegMulSq g ε` with respect to a finite measure `P` converges to the integral
of `g`, as `ε → 0` from above.
-/
theorem integral_mulExpNegMulSq_tendsto (g : BoundedContinuousFunction E ℝ) :
    Tendsto (fun ε => ∫ (x : E), (mulExpNegMulSq g.continuous ε x) ∂P)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ (x : E), g x ∂P)) := by
  apply tendsto_of_seq_tendsto
  intro u hu
  obtain ⟨N, hupos⟩ := eventually_atTop.mp (tendsto_nhdsWithin_iff.mp hu).2
  have hbound : ∃ C, ∀ᶠ (n : ℕ) in Filter.atTop, ∀ᵐ (x : E) ∂P,
      abs ((mulExpNegMulSq g.continuous (u n)) x) ≤ C := by
    use norm g
    rw [eventually_atTop]
    use N; intro n hn
    exact Eventually.of_forall
        (mulExpNegMulSq_abs_le_norm g (le_of_lt (Set.mem_Ioi.mp (hupos n hn))))
  have hlim : ∀ᵐ (x : E) ∂P, Filter.Tendsto (fun (n : ℕ) => (mulExpNegMulSq g.continuous (u n)) x)
      Filter.atTop (nhds (g x)) := Eventually.of_forall
        (fun x => (tendsto_nhdsWithin_of_tendsto_nhds
          (mulExpNegMulSq_tendsto g.continuous x)).comp hu)
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => mulExpNegMulSq g.continuous (u n) x) P := by
    intro n
    apply StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable _)
    continuity
  exact FiniteMeasure.tendstoIntegral_of_eventually_boundedPointwise
    (Eventually.of_forall hmeas) hbound hlim

theorem zero_le_one_sub_div {n : ℕ} {x : ℝ} (h : x ≤ n) : 0 ≤ 1 - x / n := by
  by_cases hn : n=0
  · simp only [hn, CharP.cast_eq_zero, _root_.div_zero, sub_zero, zero_le_one]
  · rwa [sub_nonneg, div_le_one ((Nat.cast_pos).mpr (Nat.zero_lt_of_ne_zero hn))]

theorem bounded_of_expSeq {x : ℝ} (n : ℕ) (hxnonneg : 0 ≤ x) (hxlen : x ≤ n) :
    abs ((1 + -((n : ℝ)⁻¹ * x)) ^ n) ≤ 1 := by
  rw [abs_pow]
  apply pow_le_one₀ (abs_nonneg _)
  rw [inv_mul_eq_div, abs_le]
  constructor
  · apply le_trans (Left.neg_nonpos_iff.2 zero_le_one) (zero_le_one_sub_div hxlen)
  · rw [add_le_iff_nonpos_right, Left.neg_nonpos_iff]
    apply div_nonneg hxnonneg (Nat.cast_nonneg n)

/--
The integral of `mulExpNegMulSq g ε` with respect to a finite measure `P` can be approximated by
the integral of the sequence approximating the exponential function.
-/
theorem tendsto_integral_expSeq_mulExpNegMulSq (g : BoundedContinuousFunction E ℝ)
    {ε : ℝ} (hε : ε > 0) (P : Measure E) [IsFiniteMeasure P] :
    Filter.Tendsto (fun (n : ℕ) => ∫ (x : E), (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂ P)
    Filter.atTop (nhds (∫ (x : E), mulExpNegMulSq g.continuous ε x ∂ P)) := by
  obtain ⟨N, hgN⟩ := exists_nat_ge (ε * (norm g * norm g))
  apply FiniteMeasure.tendstoIntegral_of_eventually_boundedPointwise
  -- measurability
  · apply Eventually.of_forall
    exact fun n => StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable
        (Continuous.mul g.continuous ((1 + ((n : ℝ)⁻¹ • -(ε • g * g))) ^ n).continuous))
  -- boundedness
  · use norm g
    rw [eventually_atTop]
    use N; intro n hn
    apply Eventually.of_forall
    intro x
    simp only [Algebra.smul_mul_assoc, smul_neg, BoundedContinuousFunction.coe_mul,
      BoundedContinuousFunction.coe_pow, BoundedContinuousFunction.coe_add,
      BoundedContinuousFunction.coe_one, coe_neg, BoundedContinuousFunction.coe_smul, Pi.mul_apply,
      smul_eq_mul, Pi.pow_apply, Pi.add_apply, Pi.one_apply, Pi.neg_apply, norm_mul,
      Real.norm_eq_abs]
    rw [← mul_one (norm g)]
    apply mul_le_mul (BoundedContinuousFunction.norm_coe_le_norm g x) _
        (abs_nonneg _) (norm_nonneg _)
    rw [mul_assoc]
    apply bounded_of_expSeq n (Left.mul_nonneg (le_of_lt hε) (mul_self_nonneg (g x)))
    apply le_trans (le_trans _ hgN) (Nat.cast_le.mpr hn)
    apply mul_le_mul (Preorder.le_refl ε) _ (mul_self_nonneg (g x)) (le_of_lt hε)
    rw [← abs_le_iff_mul_self_le, abs_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm g x
  -- pointwise convergence
  · apply Eventually.of_forall
    intro x
    apply Filter.Tendsto.const_mul (g x)
    simp only [Algebra.smul_mul_assoc, smul_neg, pow_apply, BoundedContinuousFunction.coe_add,
      BoundedContinuousFunction.coe_one, coe_neg, BoundedContinuousFunction.coe_smul,
      BoundedContinuousFunction.coe_mul, Pi.mul_apply, smul_eq_mul, Pi.add_apply, Pi.one_apply,
      Pi.neg_apply, mul_assoc, inv_mul_eq_div, ← neg_div]
    exact tendsto_one_plus_div_pow_exp (-(ε * (g x * g x)))

theorem integral_mulExpNegMulSq_eq {P' : Measure E} [IsFiniteMeasure P'] {A : Subalgebra ℝ C(E, ℝ)}
    {ε : ℝ} (hε : ε > 0) (hbound : ∀ g ∈ A, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C)
    (heq : ∀ g ∈ A, ∫ (x : E), (g : E → ℝ) x ∂P = ∫ (x : E), (g : E → ℝ) x ∂P') :
    ∀ (g : A), ∫ (x : E), (mulExpNegMulSq (g : C(E, ℝ)).continuous ε) x ∂P
        = ∫ (x : E), (mulExpNegMulSq (g : C(E, ℝ)).continuous ε) x ∂P' := by
  rintro ⟨g, hgA⟩
  obtain ⟨C, h⟩ := hbound g hgA
  --redefine g as a BoundedContinuousFunction
  let gb := mkOfBound g C h
  have : ∀ (n : ℕ), g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n ∈ A := by
    intro n
    apply Subalgebra.mul_mem A hgA (Subalgebra.pow_mem A _ n)
    apply Subalgebra.add_mem A (Subalgebra.one_mem A) (Subalgebra.smul_mem A _ n⁻¹)
    exact Subalgebra.neg_mem A (Subalgebra.mul_mem A (Subalgebra.smul_mem A hgA ε) hgA)
  have heqfun : (fun n : ℕ => ∫ (x : E), (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂P)
      = (fun n : ℕ => ∫ (x : E), (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂ P') := by
    apply funext (fun n => heq _ (this n))
  have limP : Tendsto (fun n : ℕ => ∫ (x : E), (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂P) atTop
      (nhds (∫ (x : E), (mulExpNegMulSq (g : C(E, ℝ)).continuous ε) x ∂P')) := by
    rw [heqfun]
    exact tendsto_integral_expSeq_mulExpNegMulSq gb hε P'
  apply tendsto_nhds_unique (tendsto_integral_expSeq_mulExpNegMulSq gb hε P) limP

theorem integral_mulExpNegMulSq_lt (f : C(E, ℝ)) {K : Set E} (hK : MeasurableSet K)
    {ε : ℝ} (hε : ε > 0) (hKP : P Kᶜ < ε.toNNReal) :
    abs (∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P
    - ∫ x in K, (mulExpNegMulSq f.continuous ε) x ∂P) < ε.sqrt := by
  have hbound : ∀ᵐ (x : E) ∂P, ‖(mulExpNegMulSq f.continuous ε) x‖ ≤ ε.sqrt⁻¹ :=
    Eventually.of_forall (mulExpNegMulSq_abs_le f.continuous hε)
  have hint : Integrable (mulExpNegMulSq f.continuous ε) P := by
    apply BoundedContinuousFunction.integrable P
      ⟨(mulExpNegMulSq f.continuous ε), ⟨2 * ε.sqrt⁻¹, _⟩⟩
    exact mulExpNegMulSq_bounded f.continuous hε
  apply lt_of_le_of_lt (norm_integral_sub_setIntegral_le hbound hK hint)
  have leps : ε * ε.sqrt⁻¹ = ε.sqrt := by
    nth_rw 1 [← (Real.mul_self_sqrt (le_of_lt hε)), mul_assoc,
        CommGroupWithZero.mul_inv_cancel ε.sqrt (ne_of_gt (Real.sqrt_pos_of_pos hε)), mul_one]
  nth_rw 2 [← leps]
  exact (_root_.mul_lt_mul_right (inv_pos.mpr (Real.sqrt_pos.mpr hε))).mpr
      (ENNReal.toReal_lt_of_lt_ofReal hKP)

theorem integral_mulExpNegMulSq_le_mul_measure {K : Set E} (hK : IsCompact K)
    (hKmeas : MeasurableSet K) (f g : C(E, ℝ)) {ε δ : ℝ} (hε : ε > 0)
    {P : Measure E} [hP : IsFiniteMeasure P] (hfg : ∀ x ∈ K, abs (g x - f x) < δ) :
    abs (∫ x in K, (mulExpNegMulSq g.continuous ε) x ∂P
      - ∫ x in K, (mulExpNegMulSq f.continuous ε) x ∂P) ≤ δ * (P K).toReal := by
  have : ∀ x ∈ K,
      norm ((mulExpNegMulSq g.continuous ε) x - (mulExpNegMulSq f.continuous ε) x) ≤ δ :=
    fun x hxK => le_trans
      (mulExpNegMulSq_lipschitz f.continuous g.continuous hε x) (le_of_lt (hfg x hxK))
  have integrable_mulExpNegMulSq :
      ∀ f : C(E, ℝ), Integrable (fun x ↦ (mulExpNegMulSq f.continuous ε) x) (P.restrict K) :=
    fun f => ContinuousOn.integrableOn_compact' hK hKmeas
        (Continuous.continuousOn (mulExpNegMulSq f.continuous ε).continuous)
  rw [← (integral_sub (integrable_mulExpNegMulSq g) (integrable_mulExpNegMulSq f))]
  · apply norm_setIntegral_le_of_norm_le_const (IsCompact.measure_lt_top hK) this
      (StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable _))
    continuity

-- special case of 'dist_le_range_sum_dist'
theorem dist_triangle8 {a b c d e f g h : ℝ} : abs (a - h) ≤ abs (a - b) + abs (b - c) + abs (c - d)
    + abs (d - e) + abs (e - f) + abs (f - g) + abs (g - h) := by
  apply le_trans (dist_triangle4 a f g h)
  apply add_le_add_right (add_le_add_right _ (dist f g)) (dist g h)
  apply le_trans (dist_triangle4 a d e f)
  apply add_le_add_right (add_le_add_right _ (dist d e)) (dist e f)
  exact dist_triangle4 a b c d


section dist_integral

variable {E: Type*} [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
    {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure P']

/--
If for any `g ∈ A` the integrals with respect to two finite measures `P, P'` coincide, then the
difference of the integrals of `mulExpNegMulSq g ε` with respect to `P, P'` is bounded by
`6 * ε.sqrt`.
-/
theorem dist_integral_mulExpNegMulSq_le (f : BoundedContinuousFunction E ℝ)
    {A : Subalgebra ℝ C(E, ℝ)} (hA : A.SeparatesPoints)
    (hbound : ∀ g ∈ A, ∃ C, ∀ x y : E, dist (g x) (g y) ≤ C)
    (heq : ∀ g ∈ A, ∫ (x : E), (g : E → ℝ) x ∂P = ∫ (x : E), (g : E → ℝ) x ∂P')
    {ε : ℝ} (hε : 0 < ε) :
    abs (∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P
      - ∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P') ≤ 6 * ε.sqrt := by
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
  have line1 : abs (∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P
      - ∫ x in K, (mulExpNegMulSq f.continuous ε) x ∂P) < ε.sqrt :=
    integral_mulExpNegMulSq_lt P f (IsClosed.measurableSet hKcl) hε hKPbound
  have line3 : abs (∫ x in K, (mulExpNegMulSq g.continuous ε) x ∂P
      - ∫ (x : E), (mulExpNegMulSq g.continuous ε) x ∂P) < ε.sqrt := by
    rw [abs_sub_comm]
    apply (integral_mulExpNegMulSq_lt P g (IsClosed.measurableSet hKcl) hε hKPbound)
  have line5 : abs (∫ (x : E), (mulExpNegMulSq g.continuous ε) x ∂P'
      - ∫ x in K, (mulExpNegMulSq g.continuous ε) x ∂P') < ε.sqrt :=
    (integral_mulExpNegMulSq_lt P' g (IsClosed.measurableSet hKcl) hε hKP'bound)
  have line7 : abs (∫ x in K, (mulExpNegMulSq f.continuous ε) x ∂P'
      - ∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P') < ε.sqrt := by
    rw [abs_sub_comm]
    apply (integral_mulExpNegMulSq_lt P' f (IsClosed.measurableSet hKcl) hε hKP'bound)
  have line2 : abs (∫ x in K, (mulExpNegMulSq f.continuous ε) x ∂P
      - ∫ x in K, (mulExpNegMulSq g.continuous ε) x ∂P) ≤ ε.sqrt := by
    rw [abs_sub_comm]
    apply le_trans (integral_mulExpNegMulSq_le_mul_measure hKco
      (IsClosed.measurableSet hKcl) f g hε hgapprox)
    rw [mul_assoc]
    apply mul_le_of_le_one_right (le_of_lt (Real.sqrt_pos_of_pos hε))
    apply inv_mul_le_one_of_le₀ (le_max_of_le_left _) (le_of_lt pos_of_measure)
    exact (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mpr
        (measure_mono (Set.subset_univ _))
  have line6 : abs (∫ x in K, (mulExpNegMulSq g.continuous ε) x ∂P'
      - ∫ x in K, (mulExpNegMulSq f.continuous ε) x ∂P') ≤ ε.sqrt := by
    apply le_trans (integral_mulExpNegMulSq_le_mul_measure hKco
      (IsClosed.measurableSet hKcl) f g hε hgapprox)
    rw [mul_assoc]
    apply mul_le_of_le_one_right (le_of_lt (Real.sqrt_pos_of_pos hε))
    apply inv_mul_le_one_of_le₀ (le_max_of_le_right _) (le_of_lt pos_of_measure)
    exact (ENNReal.toReal_le_toReal (measure_ne_top P' _) (measure_ne_top P' _)).mpr
        (measure_mono (Set.subset_univ _))
  have line4 : abs (∫ (x : E), (mulExpNegMulSq g.continuous ε) x ∂P
      - ∫ (x : E), (mulExpNegMulSq g.continuous ε) x ∂P') = 0 := by
    rw [abs_eq_zero, sub_eq_zero]
    apply integral_mulExpNegMulSq_eq P hε hbound heq ⟨g, hgA⟩
  calc
    abs (∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P
        - ∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P')
      ≤ abs (∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P
            - ∫ x in K, (mulExpNegMulSq f.continuous ε) x ∂P)
        + abs (∫ x in K, (mulExpNegMulSq f.continuous ε) x ∂P
            - ∫ x in K, (mulExpNegMulSq g.continuous ε) x ∂P)
        + abs (∫ x in K, (mulExpNegMulSq g.continuous ε) x ∂P
            - ∫ (x : E), (mulExpNegMulSq g.continuous ε) x ∂P)
        + abs (∫ (x : E), (mulExpNegMulSq g.continuous ε) x ∂P
            - ∫ (x : E), (mulExpNegMulSq g.continuous ε) x ∂P')
        + abs (∫ (x : E), (mulExpNegMulSq g.continuous ε) x ∂P'
            - ∫ x in K, (mulExpNegMulSq g.continuous ε) x ∂P')
        + abs (∫ x in K, (mulExpNegMulSq g.continuous ε) x ∂P'
            - ∫ x in K, (mulExpNegMulSq f.continuous ε) x ∂P')
        + abs (∫ x in K, (mulExpNegMulSq f.continuous ε) x ∂P'
            - ∫ (x : E), (mulExpNegMulSq f.continuous ε) x ∂P') := dist_triangle8
    _ ≤ 6 * ε.sqrt := by linarith

end dist_integral

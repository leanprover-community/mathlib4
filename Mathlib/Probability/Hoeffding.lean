/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Yuma Mizuno, Naoto Onda, Sho Sonoda
-/

import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Variance
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.Calculus.Taylor

/-!
# Hoeffding's lemma

This file states Hoeffding's lemma, which says that bounded random variables are subgaussian.

## Main results

* `ProbabilityTheory.hoeffding`: Hoeffding's Lemma states that for a random variable `X` with
  `E[X] = 0` (zero mean) and `a ≤ X ≤ b` almost surely, the inequality
  `mgf X μ t ≤ exp (t^2 * (b - a)^2 / 8)` holds almost surely for all `t ∈ ℝ`.

## References

We follow [martin2019] and [mehryar2018] for the proof of Hoeffding's lemma.
-/

open MeasureTheory ProbabilityTheory Real

namespace ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω := by volume_tac)

lemma integrable_exp_of_ae_le_const [IsFiniteMeasure μ] {X : Ω → ℝ} (b : ℝ)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ≤ b) :
    ∀ t, 0 ≤ t → t ∈ integrableExpSet X μ := by
  intro t ht
  refine .of_mem_Icc 0 (rexp (t * b)) (measurable_exp.comp_aemeasurable (hX.const_mul t)) ?_
  filter_upwards [hb] with ω hb using ⟨by positivity, by gcongr⟩

lemma integrable_exp_of_ae_const_le [IsFiniteMeasure μ] {X : Ω → ℝ} (a : ℝ)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, a ≤ X ω) :
    ∀ t, t ≤ 0 → t ∈ integrableExpSet X μ := by
  intro t ht
  dsimp [integrableExpSet]
  rw [(by funext ω; simp only [mul_neg, neg_mul, neg_neg]:
    (fun ω ↦ rexp (t * X ω)) = (fun ω ↦ rexp (-t * -X ω)))]
  apply integrable_exp_of_ae_le_const
  · exact AEMeasurable.neg hX
  · filter_upwards [hb] with ω hb using neg_le_neg_iff.mpr hb
  · exact neg_nonneg.mpr ht

lemma integrableExpSet_of_ae_mem_Icc [IsFiniteMeasure μ] {X : Ω → ℝ} (a b : ℝ)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    integrableExpSet X μ = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro t
  by_cases sign_t : 0 ≤ t
  case pos =>
    apply integrable_exp_of_ae_le_const _ _ hX
      (by filter_upwards [hb] with ω hb using hb.2) _ sign_t
  case neg =>
    apply integrable_exp_of_ae_const_le _ _  hX
      (by filter_upwards [hb] with ω hb using hb.1) _ (le_of_not_ge sign_t)

theorem mem_interior_integrableExpSet_of_ae_mem_Icc  [IsFiniteMeasure μ] {X : Ω → ℝ} (t a b : ℝ)
    (hX : AEMeasurable X μ)
    (h : ∀ᵐ (ω : Ω) ∂μ, X ω ∈ Set.Icc a b) : t ∈ interior (integrableExpSet X μ) := by
  rw [integrableExpSet_of_ae_mem_Icc μ a b hX h]
  apply mem_interior_iff_mem_nhds.mpr Filter.univ_mem

theorem cgf_deriv_eq_tilted_measure_expectation {X : Ω → ℝ} (t : ℝ)
    (h0 : t ∈ interior (integrableExpSet X μ)) :
    deriv (cgf X μ) t = (μ.tilted fun ω ↦ t * X ω)[X] := by
  rw [deriv_cgf]
  · rw [MeasureTheory.integral_tilted, ← integral_div]
    simp only [smul_eq_mul, mgf]; congr with ω; ring
  · exact h0

theorem cgf_iterated_deriv_two_eq_tilted_measure_variance [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (t a b : ℝ) (hX : AEMeasurable X μ) (h : ∀ᵐ (ω : Ω) ∂μ, X ω ∈ Set.Icc a b):
    iteratedDeriv 2 (cgf X μ) t = Var[X ; μ.tilted fun ω ↦ t * X ω] := by
  rw [iteratedDeriv_two_cgf]
  · have p : (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ (X ω) ^ 2] =
      (μ[fun ω ↦ (X ω) ^ 2 * rexp (t * X ω)]) / mgf X μ t := by
      rw [MeasureTheory.integral_tilted, ← integral_div]
      simp only [smul_eq_mul, mgf]; congr with ω; ring
    rw [<- p, cgf_deriv_eq_tilted_measure_expectation _ t
      (mem_interior_integrableExpSet_of_ae_mem_Icc μ t a b hX h)]
    dsimp only
    have p : Var[X ; μ.tilted fun ω ↦ t * X ω] =
        (μ.tilted fun ω ↦ t * X ω)[X ^ 2] - ((μ.tilted fun ω ↦ t * X ω)[X]) ^ 2 := by
      have _ : IsProbabilityMeasure (μ.tilted fun ω ↦ t * X ω) :=
        isProbabilityMeasure_tilted
        (by rw [integrableExpSet_of_ae_mem_Icc μ a b hX h]; exact trivial :
          t ∈ integrableExpSet X μ)
      have hμ := tilted_absolutelyContinuous μ fun ω ↦ t * X ω
      apply variance_def' <|
        memLp_of_bounded (hμ h) (AEMeasurable.aestronglyMeasurable (hX.mono_ac hμ)) 2
    rw [p]; exact rfl
  · exact mem_interior_integrableExpSet_of_ae_mem_Icc μ t a b hX h

theorem cgf_le_bound_of_ae_mem_Icc_and_mean_zero [IsProbabilityMeasure μ]
    (t a b : ℝ) {X : Ω → ℝ} (ht : 0 < t)
    (hX : AEMeasurable X μ)
    (h : ∀ᵐ (ω : Ω) ∂μ, X ω ∈ Set.Icc a b) (h0 : ∫ (x : Ω), X x ∂μ = 0):
  cgf X μ t ≤ t ^ 2 * (b - a) ^ 2 / 8 := by
  let f := cgf X μ
  let f' := deriv (cgf X μ)
  let f'' := iteratedDeriv 2 (cgf X μ)
  have hf : f 0 = 0 := cgf_zero
  have hf' : f' 0 = 0 := by
    dsimp [f']
    rw [deriv_cgf_zero]
    · simp only [measure_univ, ENNReal.one_toReal, div_one, f']
      exact h0
    · exact mem_interior_integrableExpSet_of_ae_mem_Icc μ 0 a b hX h
  have q : ∃ c ∈ (Set.Ioo 0 t), f t = f 0 + f' 0 * t + f'' c * t ^ 2 / 2 := by
    have q' : ∃ c ∈ (Set.Ioo 0 t), f t - taylorWithinEval f 1 (Set.Icc 0 t) 0 t =
      iteratedDerivWithin (1 + 1) f (Set.Icc 0 t) c * (t - 0) ^ (1 + 1) / ↑(1 + 1).factorial := by
      apply @taylor_mean_remainder_lagrange f t 0 1 ht _ _
      · simp only [Nat.cast_one]
        apply AnalyticOn.contDiffOn_of_completeSpace
        have : AnalyticOn ℝ (cgf X μ) (interior (integrableExpSet X μ)) := analyticOn_cgf
        rw [integrableExpSet_of_ae_mem_Icc μ a b hX h] at this
        rw [interior_univ] at this
        exact AnalyticOn.mono this (fun ⦃a⦄ a ↦ trivial)
      · apply DifferentiableOn.mono
        apply ContDiffOn.differentiableOn_iteratedDerivWithin
        exact AnalyticOn.contDiffOn (n := 2) (AnalyticOn.mono analyticOn_cgf
          (fun s hs ↦ mem_interior_integrableExpSet_of_ae_mem_Icc μ s a b hX h))
          (uniqueDiffOn_Icc ht)
        norm_cast
        exact uniqueDiffOn_Icc ht
        exact Set.Ioo_subset_Icc_self
    obtain ⟨c, ⟨q0, qc'⟩⟩ := q'
    use c
    constructor
    · exact q0
    · simp only [taylorWithinEval_succ, taylor_within_zero_eval, CharP.cast_eq_zero, zero_add,
      Nat.factorial_zero, Nat.cast_one, mul_one, inv_one, sub_zero, pow_one, one_mul,
      iteratedDerivWithin_one, smul_eq_mul, Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat] at qc'
      have q1 : derivWithin f (Set.Icc 0 t) 0 = f' 0 := by
        rw [DifferentiableAt.derivWithin]
        · exact differentiableAt_cgf (mem_interior_integrableExpSet_of_ae_mem_Icc μ 0 a b hX h)
        · apply uniqueDiffWithinAt_convex (convex_Icc 0 t)
          simp only [interior_Icc, Set.nonempty_Ioo]
          exact ht
          simp only [closure_Icc, Set.mem_Icc, le_refl, true_and]
          exact le_of_lt ht
      have q2 : iteratedDerivWithin 2 f (Set.Icc 0 t) c = f'' c := by
        rw [<- (by rw [iteratedDerivWithin_univ] : iteratedDerivWithin 2 f Set.univ c = f'' c)]
        rw [iteratedDerivWithin_eq_iteratedFDerivWithin]
        rw [iteratedDerivWithin_eq_iteratedFDerivWithin]
        apply congr
        rw [<- (Set.univ_inter (Set.Icc 0 t))]
        symm
        rw [iteratedFDerivWithin_inter]
        exact Icc_mem_nhds_iff.mpr q0
        exact rfl
      rw [q1, q2] at qc'
      linarith
  rw [hf, hf'] at q
  simp only [zero_mul, add_zero, zero_add, forall_const] at q
  obtain ⟨c, ⟨_, cq'⟩⟩ := q
  have s : f t ≤ t^2 * (b - a)^2 / 8 := by
    rw [cq']
    calc
    _ ≤ ((b - a) / 2) ^ 2 * t ^ 2 / 2 := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        dsimp [f'']
        rw [cgf_iterated_deriv_two_eq_tilted_measure_variance _ c a b hX h]
        · have _ : IsProbabilityMeasure (μ.tilted fun ω ↦ c * X ω) := isProbabilityMeasure_tilted
            (by rw [integrableExpSet_of_ae_mem_Icc μ a b hX h]; exact trivial :
              c ∈ integrableExpSet X μ)
          exact variance_le_sq_of_bounded
            ((tilted_absolutelyContinuous μ fun ω ↦ c * X ω) h)
            (hX.mono_ac (tilted_absolutelyContinuous μ fun ω ↦ c * X ω))
        · exact sq_nonneg t
      · linarith
    _ = t ^ 2 * (b - a) ^ 2 / 8 := by ring
  exact s

/-! ### Hoeffding's lemma restricted to t ≥ 0 -/

private theorem hoeffding_nonneg [IsProbabilityMeasure μ]
    (t a b : ℝ) {X : Ω → ℝ} (ht : 0 ≤ t) (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (h0 : μ[X] = 0) :
    mgf X μ t ≤ exp (t^2 * (b - a)^2 / 8) := by
  dsimp [mgf]
  by_cases w : t = 0;
    · rw [w]; simp only [zero_mul, exp_zero, integral_const, measure_univ,
    ENNReal.one_toReal, smul_eq_mul, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, le_refl]
  set f : ℝ → ℝ := fun t ↦ cgf X μ t
  suffices f t ≤ t^2 * (b - a)^2 / 8 from by
    rw [<- log_le_iff_le_exp]
    exact this
    apply mgf_pos' (Ne.symm (NeZero.ne' μ))
      (by rw [integrableExpSet_of_ae_mem_Icc μ a b hX h]; exact trivial :
      (t ∈ integrableExpSet X μ))
  exact cgf_le_bound_of_ae_mem_Icc_and_mean_zero μ t a b
    (lt_of_le_of_ne ht fun a ↦ w (id (Eq.symm a))) hX h h0

/-! ### Hoeffding's lemma -/

/-- Hoeffding's Lemma states that for a random variable `X` with `E[X] = 0` (zero mean) and
 `a ≤ X ≤ b` almost surely, the inequality
 `μ[exp (t * (X ω))] ≤ exp (t^2 * (b - a)^2 / 8)` holds almost surely for all `t ∈ ℝ`. -/
theorem hoeffding [IsProbabilityMeasure μ] (t a b : ℝ) {X : Ω → ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (h0 : μ[X] = 0) :
    mgf X μ t ≤ exp (t^2 * (b - a)^2 / 8) := by
  by_cases h' : 0 ≤ t
  case pos =>
    exact hoeffding_nonneg μ t a b h' hX h h0
  case neg =>
    simp only [not_le] at h'
    suffices ∫ ω, rexp (- t * - X ω) ∂μ ≤
      rexp ((- t) ^ 2 * ((- a) - (- b)) ^ 2 / 8) from by
      simp only [mul_neg, neg_mul, neg_neg, even_two, Even.neg_pow, sub_neg_eq_add] at this
      rw [<- (by ring : (-a + b) = b - a)]
      exact this
    apply hoeffding_nonneg _ _ _ _ (by linarith : 0 ≤ - t) hX.neg
    · simp only [Set.mem_Icc, neg_le_neg_iff, Filter.eventually_and]
      exact ⟨h.mono fun ω h ↦ h.2, h.mono fun ω h ↦ h.1⟩
    · rw [integral_neg]
      simp only [neg_eq_zero]
      exact h0

end ProbabilityTheory

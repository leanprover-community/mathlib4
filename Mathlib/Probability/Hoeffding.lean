/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
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

This file states Hoeffding's lemma.

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
    ∀ (t : ℝ), 0 ≤ t → t ∈ integrableExpSet X μ := by
  intro t ht
  refine .of_mem_Icc 0 (rexp (t * b)) (measurable_exp.comp_aemeasurable (hX.const_mul t)) ?_
  filter_upwards [hb] with ω hb using ⟨by positivity, by gcongr⟩

lemma integrable_exp_of_ae_const_le [IsFiniteMeasure μ] {X : Ω → ℝ} (a : ℝ)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, a ≤ X ω) :
    ∀ (t : ℝ), t ≤ 0 → t ∈ integrableExpSet X μ := by
  intro t ht
  dsimp [integrableExpSet]
  rw [(by funext ω; simp only [mul_neg, neg_mul, neg_neg]:
    (fun ω ↦ rexp (t * X ω)) = (fun ω ↦ rexp (-t * -X ω)))]
  apply integrable_exp_of_ae_le_const
  · exact AEMeasurable.neg hX
  · filter_upwards [hb] with ω hb using neg_le_neg_iff.mpr hb
  · exact neg_nonneg.mpr ht

lemma integrable_exp_of_ae_mem_Icc [IsFiniteMeasure μ] {X : Ω → ℝ} (a b : ℝ)
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

theorem integrable_exp_set_interior_of_ae_mem_Icc  [IsFiniteMeasure μ] {X : Ω → ℝ} (t a b : ℝ)
    (hX : AEMeasurable X μ)
    (h : ∀ᵐ (ω : Ω) ∂μ, X ω ∈ Set.Icc a b) : t ∈ interior (integrableExpSet X μ) := by
  rw [integrable_exp_of_ae_mem_Icc μ a b hX h]
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
    iteratedDeriv 2 (cgf X μ) t = Var[X; μ.tilted fun ω ↦ t * X ω] := by
  rw [iteratedDeriv_two_cgf]
  · have p : (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ (X ω) ^ 2] =
      (μ[fun ω ↦ (X ω) ^ 2 * rexp (t * X ω)]) / mgf X μ t := by
      rw [MeasureTheory.integral_tilted, ← integral_div]
      simp only [smul_eq_mul, mgf]; congr with ω; ring
    rw [<- p, cgf_deriv_eq_tilted_measure_expectation _ t
      (integrable_exp_set_interior_of_ae_mem_Icc μ t a b hX h)]
    dsimp only
    have p : Var[X; μ.tilted fun ω ↦ t * X ω] =
        (μ.tilted fun ω ↦ t * X ω)[X ^ 2] - ((μ.tilted fun ω ↦ t * X ω)[X]) ^ 2 := by
      have _ : IsProbabilityMeasure (μ.tilted fun ω ↦ t * X ω) :=
        isProbabilityMeasure_tilted
        (by rw [integrable_exp_of_ae_mem_Icc μ a b hX h]; exact trivial : t ∈ integrableExpSet X μ)
      have hμ := tilted_absolutelyContinuous μ fun ω ↦ t * X ω
      apply variance_def' <|
        memLp_of_bounded (hμ h) (AEMeasurable.aestronglyMeasurable (hX.mono_ac hμ)) 2
    rw [p]; exact rfl
  · exact integrable_exp_set_interior_of_ae_mem_Icc μ t a b hX h

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
    · exact integrable_exp_set_interior_of_ae_mem_Icc μ 0 a b hX h
  have q : ∃ c ∈ (Set.Ioo 0 t), f t = f 0 + f' 0 * t + f'' c * t ^ 2 / 2 := by
    have q' : ∃ c ∈ (Set.Ioo 0 t), f t - taylorWithinEval f 1 (Set.Icc 0 t) 0 t =
      iteratedDerivWithin (1 + 1) f (Set.Icc 0 t) c * (t - 0) ^ (1 + 1) / ↑(1 + 1).factorial := by
      apply @taylor_mean_remainder_lagrange f t 0 1 ht _ _
      simp only [Nat.cast_one]
      refine AnalyticOn.contDiffOn_of_completeSpace ?_
      dsimp [f]
      have r : AnalyticOn ℝ (cgf X μ) (interior (integrableExpSet X μ)) := analyticOn_cgf
      rw [integrable_exp_of_ae_mem_Icc μ a b hX h] at r
      simp only [interior_univ] at r
      apply AnalyticOn.mono r (fun ⦃a⦄ a ↦ trivial)
      apply DifferentiableOn.mono
      rw [differentiableOn_univ]
      · apply?
      · sorry



    sorry
    /-
    let A := (f t - f 0 - f' 0 * t) * 2 / t ^ 2
    have q0 : f t = f 0 + f' 0 * t + A * t ^ 2 / 2 := by
      have q0' : A * t ^ 2 = (f t - f 0 - f' 0 * t) * 2 := by
        calc
        _ = (f t - f 0 - f' 0 * t) * 2 * t ^ 2 / t ^ 2 :=
          Eq.symm (mul_div_right_comm ((f t - f 0 - f' 0 * t) * 2) (t ^ 2) (t ^ 2))
        _ = (f t - f 0 - f' 0 * t) * 2 * (t ^ 2 / t ^ 2) := by ring
        _ = (f t - f 0 - f' 0 * t) * 2 := by field_simp only
      rw [q0']; ring
    set g : ℝ → ℝ := fun x ↦ f t - f x - f' x * (t - x) - A * (t - x) ^ 2 / 2
    have q1 : g 0 = 0 := by
      dsimp only [g, A]
      calc
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 * t ^ 2 / t ^ 2 := by field_simp
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 * (t ^ 2 / t ^ 2) := by ring
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 := by field_simp
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) := by ring
      _ = 0 := by ring
    have q2 : g t = 0 := by
      dsimp only [g]
      simp only [sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_div]
    set g' : ℝ → ℝ := fun x ↦ - f'' x * (t - x) + A * (t - x)
    have q3 : ∀ x : ℝ, (x ∈ interior (integrableExpSet X μ)) → HasDerivAt g (g' x) x := by
      intro x hs
      apply HasDerivAt.add
      · rw [← (by ring : 0 - f' x + (f' x - f'' x * (t - x)) = - f'' x * (t - x))]
        refine HasDerivAt.add ?_ ?_
        · refine HasDerivAt.sub ?_ ?_
          exact hasDerivAt_const x (f t)
          refine DifferentiableAt.hasDerivAt ?_
          apply AnalyticAt.differentiableAt (analyticAt_cgf hs)
        · dsimp [f', f'']
          suffices HasDerivAt (fun x ↦ (deriv (cgf X μ) x * (x - t)))
            (iteratedDeriv 2 (cgf X μ) x * (x - t) + deriv (cgf X μ) x * 1) x from by
            rw [(by funext x; ring : (fun x ↦ -(deriv (cgf X μ) x * (t - x)))
              = fun x ↦ (deriv (cgf X μ) x * (x - t)))]
            rw [(by ring : (deriv (cgf X μ) x - iteratedDeriv 2 (cgf X μ) x * (t - x))
              = (iteratedDeriv 2 (cgf X μ) x * (x - t) + deriv (cgf X μ) x * 1))]
            exact this
          apply HasDerivAt.mul
          · rw [iteratedDeriv_succ]
            simp only [iteratedDeriv_one, hasDerivAt_deriv_iff]
            have r := differentiableAt_iteratedDeriv_cgf hs 1
            simp only [iteratedDeriv_one] at r
            exact r
          · exact HasDerivAt.add_const (-t) (hasDerivAt_id' x)
      · rw [(by ext x; ring : (fun x ↦ -(A * (t - x) ^ 2 / 2)) =
          (fun x ↦ -A * ((x - t) ^ 2 / 2))),
            (by ring : (A * (t - x)) = -A * (x - t))]
        apply HasDerivAt.const_mul
        rw [(by ext x; ring : (fun y ↦ (y - t) ^ 2 / 2) = (fun y ↦ (1 / 2) * (y - t) ^ 2)),
            (by ring : x - t = (1 / 2) * (2 * (x - t)))]
        apply HasDerivAt.const_mul
        rw [(by ext x; ring : (fun y ↦ (y - t) ^ 2) = (fun y ↦ y ^ 2 - 2 * t * y + t ^ 2)),
            (by ring : (2 * (x - t)) = 2 * (x ^ (2 - 1)) - 2 * t + 0)]
        apply HasDerivAt.add
        · apply HasDerivAt.add
          · apply hasDerivAt_pow
          · rw [(by ext x; ring : (fun x ↦ -(2 * t * x)) = (fun x ↦ (x * -(2 * t))))]
            apply hasDerivAt_mul_const
        · apply hasDerivAt_const
    have q4 : ∃ c ∈ (Set.Ioo 0 t), g' c = 0 :=
      exists_hasDerivAt_eq_zero ht
        (HasDerivAt.continuousOn
          (fun x _ => q3 _ (integrable_exp_set_interior_of_ae_mem_Icc μ x a b hX h)))
        (by rw [q1, q2] : g 0 = g t)
        (fun x _ => q3 _ (integrable_exp_set_interior_of_ae_mem_Icc μ x a b hX h))
    obtain ⟨c, ⟨cq, cq'⟩⟩ := q4
    use c; constructor
    · exact cq
    · dsimp only [g'] at cq';
      have cq'' : (A - f'' c) * (t - c) = 0 := by linarith
      have cq''' : A = f'' c := by
        have cr : (A - f'' c) = 0 := by
          simp only [mul_eq_zero] at cq''
          exact cq''.elim id (by intro; obtain ⟨_, _⟩ := cq; linarith)
        linarith
      rw [← cq''']
      exact q0
  -/
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
            (by rw [integrable_exp_of_ae_mem_Icc μ a b hX h]; exact trivial :
              c ∈ integrableExpSet X μ)
          exact variance_le_sq_of_bounded
            ((tilted_absolutelyContinuous μ fun ω ↦ c * X ω) h)
            (hX.mono_ac (tilted_absolutelyContinuous μ fun ω ↦ c * X ω))
        · exact sq_nonneg t
      · linarith
    _ = t ^ 2 * (b - a) ^ 2 / 8 := by ring
  exact s

/-! ### Hoeffding's lemma restricted to t ≥ 0 -/

theorem hoeffding_nonneg [IsProbabilityMeasure μ]
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
      (by rw [integrable_exp_of_ae_mem_Icc μ a b hX h]; exact trivial : (t ∈ integrableExpSet X μ))
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

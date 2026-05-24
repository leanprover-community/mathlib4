/-
Copyright (c) 2026 Zixiao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zixiao Wang, Rajarshi Mukherjee
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# The Neyman–Pearson lemma (sum-of-errors form)

For two finite measures `P` and `Q` on a measurable space `Ω`, the Neyman–Pearson lemma
characterizes the randomized tests `T : Ω → ℝ` with values in `[0, 1]` that minimize
the sum of error masses
`∫ T dP + t · ∫ (1 - T) dQ`
where `t > 0` is a fixed cost weight on Type II errors (equivalently, the test compares
the likelihood ratio against the threshold `t⁻¹`).

## Main definitions

* `ProbabilityTheory.NeymanPearson.npLikelihoodRatio P Q` — the likelihood ratio
  `(dQ/d(P+Q)) / (dP/d(P+Q))` of `Q` against `P`.
* `ProbabilityTheory.NeymanPearson.npTest P Q t η` — the Neyman–Pearson test:
`1` if the likelihood ratio is `> t⁻¹`, `η` if it equals `t⁻¹`, and `0` otherwise;
  forced to `1` on `{dP/d(P+Q) = 0}`.
* `ProbabilityTheory.NeymanPearson.npSumError P Q t T` — the sum-of-errors cost
  `∫ T dP + t · ∫ (1 - T) dQ`.

## Main result

* `ProbabilityTheory.NeymanPearson.neyman_pearson` — `npTest P Q t η` minimizes
  `npSumError P Q t` over the set of measurable `[0, 1]`-valued tests, for any
  `t > 0` and `0 ≤ η ≤ 1`.

## References

* Ingster, Y. and Suslina, I.A., 2012. Nonparametric goodness-of-fit testing under Gaussian models (Vol. 169). Springer Science & Business Media.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.NeymanPearson

variable {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)

/-- The likelihood ratio of `Q` against `P` with respect to the dominating measure
`P + Q`, i.e. `(dQ/d(P+Q)) / (dP/d(P+Q))`. On the `P`-null set where `dP/d(P+Q)`
vanishes, this evaluates to `0` by Lean's `a / 0 = 0` convention; the value there
is immaterial to the optimality statement `neyman_pearson` because `npTest` is
hard-coded to `1` on that set. -/
noncomputable def npLikelihoodRatio : Ω → ℝ := fun ω ↦
  (Q.rnDeriv (P + Q) ω).toReal / (P.rnDeriv (P + Q) ω).toReal

/-- The Neyman–Pearson randomized test against the threshold `t⁻¹`: returns `1` if the
likelihood ratio is `> t⁻¹`, `η` at the boundary `= t⁻¹`, and `0` otherwise; returns `1`
on the `P`-null set where the ratio is undefined. The test is optimal for
`npSumError P Q t` when `t > 0`. Boundedness in `[0, 1]` requires `0 ≤ η ≤ 1`
(see `npTest_nonneg` and `npTest_le_one`). -/
noncomputable def npTest (t η : ℝ) : Ω → ℝ := fun ω ↦
  if (P.rnDeriv (P + Q) ω).toReal = 0 then 1
  else if npLikelihoodRatio P Q ω > t⁻¹ then 1
  else if npLikelihoodRatio P Q ω = t⁻¹ then η
  else 0

/-- The sum-of-errors cost functional `∫ T dP + t · ∫ (1 - T) dQ`. -/
noncomputable def npSumError (t : ℝ) (T : Ω → ℝ) : ℝ :=
  ∫ ω, T ω ∂P + t * ∫ ω, (1 - T ω) ∂Q

/-- The likelihood ratio is measurable. -/
@[fun_prop]
lemma measurable_npLikelihoodRatio : Measurable (npLikelihoodRatio P Q) :=
  (Measure.measurable_rnDeriv Q (P + Q)).ennreal_toReal.div
    (Measure.measurable_rnDeriv P (P + Q)).ennreal_toReal

/-- The Neyman–Pearson test is measurable. -/
@[fun_prop]
lemma measurable_npTest (t η : ℝ) : Measurable (npTest P Q t η) := by
  have hh := measurable_npLikelihoodRatio P Q
  have hp : Measurable (fun ω ↦ (P.rnDeriv (P + Q) ω).toReal) := by fun_prop
  exact Measurable.ite (measurableSet_eq_fun hp measurable_const) measurable_const <|
    Measurable.ite (measurableSet_lt measurable_const hh) measurable_const <|
      Measurable.ite (measurableSet_eq_fun hh measurable_const) measurable_const measurable_const

/-- The Neyman–Pearson test is non-negative when `0 ≤ η`. -/
lemma npTest_nonneg {t η : ℝ} (hη0 : 0 ≤ η) (ω : Ω) : 0 ≤ npTest P Q t η ω := by
  simp only [npTest]
  split_ifs <;> linarith

/-- The Neyman–Pearson test is bounded by `1` when `η ≤ 1`. -/
lemma npTest_le_one {t η : ℝ} (hη1 : η ≤ 1) (ω : Ω) : npTest P Q t η ω ≤ 1 := by
  simp only [npTest]
  split_ifs <;> linarith

/-- **Neyman–Pearson lemma (sum-of-errors form).** For finite measures `P` and `Q` on
a measurable space `Ω`, the randomized test `npTest P Q t η` minimizes
`npSumError P Q t T = ∫ T dP + t · ∫ (1 - T) dQ` over all measurable `[0, 1]`-valued
tests `T`, for any threshold `t > 0` and any `0 ≤ η ≤ 1`. -/
theorem neyman_pearson
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (t η : ℝ) (ht : 0 < t) (hη : η ∈ Set.Icc (0 : ℝ) 1) :
    IsMinOn (npSumError P Q t)
      { T : Ω → ℝ | Measurable T ∧ (∀ ω, 0 ≤ T ω) ∧ (∀ ω, T ω ≤ 1) }
      (npTest P Q t η) := by
  intro T hT
  obtain ⟨hTm, hT0, hT1⟩ := hT
  obtain ⟨hη0, hη1⟩ := hη
  set τ := npTest P Q t η
  change npSumError P Q t τ ≤ npSumError P Q t T
  have hPμ : P ≪ P + Q := Measure.AbsolutelyContinuous.add_right .rfl Q
  have hQμ : Q ≪ P + Q := Measure.AbsolutelyContinuous.add_right' .rfl P
  have hτm : Measurable τ := measurable_npTest P Q t η
  have hτ0 : ∀ ω, 0 ≤ τ ω := npTest_nonneg P Q hη0
  have hτ1 : ∀ ω, τ ω ≤ 1 := npTest_le_one P Q hη1
  have h_int_μ : ∀ F : Ω → ℝ, Measurable F → (∀ ω, 0 ≤ F ω) → (∀ ω, F ω ≤ 1)
      → Integrable (fun ω ↦ (P.rnDeriv (P + Q) ω).toReal * F ω) (P + Q) ∧
        Integrable (fun ω ↦ (Q.rnDeriv (P + Q) ω).toReal * (1 - F ω)) (P + Q) := by
    intro F hFm hF0 hF1
    have hF_P : Integrable F P := .of_mem_Icc 0 1 hFm.aemeasurable
      (ae_of_all _ fun ω ↦ Set.mem_Icc.mpr ⟨hF0 ω, hF1 ω⟩)
    have h1F_m : Measurable (fun ω ↦ 1 - F ω) := by fun_prop
    have h1F_Q : Integrable (fun ω ↦ 1 - F ω) Q := .of_mem_Icc 0 1 h1F_m.aemeasurable
      (ae_of_all _ fun ω ↦ Set.mem_Icc.mpr ⟨by linarith [hF1 ω], by linarith [hF0 ω]⟩)
    exact ⟨(integrable_toReal_rnDeriv_mul_iff hPμ).mpr hF_P,
           (integrable_toReal_rnDeriv_mul_iff hQμ).mpr h1F_Q⟩
  obtain ⟨hpτ, hq1τ⟩ := h_int_μ τ hτm hτ0 hτ1
  obtain ⟨hpT, hq1T⟩ := h_int_μ T hTm hT0 hT1
  have h_change : ∀ F : Ω → ℝ,
      Integrable (fun ω ↦ (P.rnDeriv (P + Q) ω).toReal * F ω) (P + Q) →
      Integrable (fun ω ↦ (Q.rnDeriv (P + Q) ω).toReal * (1 - F ω)) (P + Q) →
      npSumError P Q t F =
        ∫ ω, (P.rnDeriv (P + Q) ω).toReal * F ω +
          t * ((Q.rnDeriv (P + Q) ω).toReal * (1 - F ω)) ∂(P + Q) := fun F hpF hq1F ↦ by
    change ∫ ω, F ω ∂P + t * ∫ ω, (1 - F ω) ∂Q = _
    rw [← integral_toReal_rnDeriv_mul hPμ, ← integral_toReal_rnDeriv_mul hQμ,
        ← integral_const_mul, ← integral_add hpF (hq1F.const_mul t)]
  rw [h_change τ hpτ hq1τ, h_change T hpT hq1T]
  refine integral_mono (hpτ.add (hq1τ.const_mul t)) (hpT.add (hq1T.const_mul t)) ?_
  intro ω
  dsimp only
  by_cases hp_zero : (P.rnDeriv (P + Q) ω).toReal = 0
  · have hτ_one : τ ω = 1 := by
      change npTest P Q t η ω = 1
      simp only [npTest, if_pos hp_zero]
    rw [hp_zero, hτ_one]
    nlinarith [mul_nonneg ht.le (mul_nonneg
      (ENNReal.toReal_nonneg : (0:ℝ) ≤ (Q.rnDeriv (P + Q) ω).toReal)
      (sub_nonneg.mpr (hT1 ω)))]
  · have hp_pos : 0 < (P.rnDeriv (P + Q) ω).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hp_zero)
    have h_ratio : npLikelihoodRatio P Q ω =
        (Q.rnDeriv (P + Q) ω).toReal / (P.rnDeriv (P + Q) ω).toReal := rfl
    rcases lt_trichotomy (npLikelihoodRatio P Q ω) t⁻¹ with h_lt | h_eq | h_gt
    · have hτ_zero : τ ω = 0 := by
        change npTest P Q t η ω = 0
        simp only [npTest, if_neg hp_zero, if_neg (not_lt.mpr h_lt.le), if_neg (ne_of_lt h_lt)]
      rw [h_ratio, div_lt_iff₀ hp_pos] at h_lt
      have htq_lt_p : t * (Q.rnDeriv (P + Q) ω).toReal < (P.rnDeriv (P + Q) ω).toReal := by
        have := mul_lt_mul_of_pos_left h_lt ht
        rwa [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at this
      rw [hτ_zero]; nlinarith [hT0 ω, hT1 ω, htq_lt_p]
    · rw [h_ratio, div_eq_iff hp_zero] at h_eq
      have hp_eq : (P.rnDeriv (P + Q) ω).toReal = t * (Q.rnDeriv (P + Q) ω).toReal := by
        rw [h_eq, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
      rw [hp_eq]; ring_nf; exact le_rfl
    · have hτ_one : τ ω = 1 := by
        change npTest P Q t η ω = 1
        simp only [npTest, if_neg hp_zero, if_pos h_gt]
      rw [h_ratio, lt_div_iff₀ hp_pos] at h_gt
      have hp_lt_tq : (P.rnDeriv (P + Q) ω).toReal < t * (Q.rnDeriv (P + Q) ω).toReal := by
        have := mul_lt_mul_of_pos_left h_gt ht
        rwa [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at this
      rw [hτ_one]; nlinarith [hT0 ω, hT1 ω, hp_lt_tq]

end ProbabilityTheory.NeymanPearson

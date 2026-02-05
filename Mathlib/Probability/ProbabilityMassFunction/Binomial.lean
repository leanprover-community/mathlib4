/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Tactic.FinCases

/-!
# The binomial distribution

This file defines the probability mass function of the binomial distribution.

## Main results

* `binomial_one_eq_bernoulli`: For `n = 1`, it is equal to `PMF.bernoulli`.
-/

@[expose] public section

namespace PMF

open ENNReal NNReal
/-- The binomial `PMF`: the probability of observing exactly `i` “heads” in a sequence of `n`
independent coin tosses, each having probability `p` of coming up “heads”. -/
def binomial (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : PMF (Fin (n + 1)) :=
  .ofFintype (fun i =>
      ↑(p ^ (i : ℕ) * (1 - p) ^ ((Fin.last n - i) : ℕ) * (n.choose i : ℕ))) (by
    dsimp only
    norm_cast
    convert (add_pow p (1 - p) n).symm
    · rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_pos hi]
    · rw [add_tsub_cancel_of_le (mod_cast h), one_pow])

theorem binomial_apply (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) (i : Fin (n + 1)) :
    binomial p h n i = p ^ (i : ℕ) * (1 - p) ^ ((Fin.last n - i) : ℕ) * (n.choose i : ℕ) := by
  simp [binomial]

@[simp]
theorem binomial_apply_zero (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) :
    binomial p h n 0 = (1 - p) ^ n := by
  simp [binomial_apply]

@[simp]
theorem binomial_apply_last (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) :
    binomial p h n (.last n) = p ^ n := by
  simp [binomial_apply]

theorem binomial_apply_self (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) :
    binomial p h n (.last n) = p ^ n := by simp

/-- The binomial distribution on one coin is the Bernoulli distribution. -/
theorem binomial_one_eq_bernoulli (p : ℝ≥0) (h : p ≤ 1) :
    binomial p h 1 = (bernoulli p h).map (cond · 1 0) := by
  ext i; fin_cases i <;> simp [binomial_apply]

end PMF

section CharacteristicFunction

open scoped NNReal Real

open Complex MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {p : ℝ≥0} {h : p ≤ 1}
  {n : ℕ}

/-- A binomial distribution on `Fin (n + 1)` with success probability `p`
and `n` independent trials. -/
noncomputable
def binomialMeasure (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : Measure (Fin (n + 1)) :=
  (PMF.binomial p h n).toMeasure

/-- A binomial distribution on `ℝ` with success probability `p` and `n` independent trials. -/
noncomputable
def binomialReal (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : Measure ℝ :=
  (binomialMeasure p h n).map (fun k : Fin (n + 1) => (k : ℝ))

instance isProbabilityMeasure_binomialReal :
    IsProbabilityMeasure (binomialReal p h n) := by
  unfold binomialReal binomialMeasure
  exact Measure.isProbabilityMeasure_map
    (by fun_prop : Measurable (_ : Fin (n + 1) → ℝ)).aemeasurable

/-- The complex moment-generating function of a binomial distribution with success probability `p`
and `n` independent trials is given by `z ↦ (1 - p + p * exp z) ^ n`. -/
theorem complexMGF_id_binomialReal (z : ℂ) :
    complexMGF id (binomialReal p h n) z = (1 - p + p * cexp z) ^ n := by
  calc complexMGF id (binomialReal p h n) z
    _ = ∫ k, cexp (z * k) ∂(PMF.binomial p h n).toMeasure := by
      simp only [complexMGF, id_eq, binomialReal, binomialMeasure]
      exact integral_map (by fun_prop : Measurable (_ : Fin (n + 1) → ℝ)).aemeasurable
        (by fun_prop)
    _ = ∑ k, (PMF.binomial p h n k).toReal • cexp (z * k) :=
      PMF.integral_eq_sum ..
    _ = ∑ m ∈ Finset.range (n + 1), (p * cexp z) ^ m * (1 - p) ^ (n - m) * n.choose m := by
      simp only [PMF.binomial, PMF.ofFintype_apply, Fin.val_last,
        ENNReal.coe_toReal, Complex.real_smul]
      push_cast [NNReal.coe_sub h]
      rw [Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi; simp only [dif_pos hi]
      rw [mul_comm z _, Complex.exp_nat_mul]
      push_cast [Nat.cast_choose ℂ (Nat.lt_succ_iff.mp hi)]; ring
    _ = (1 - p + p * cexp z) ^ n := by
      rw [add_comm (1 - _), add_pow]

/-- The complex moment-generating function of a random variable with binomial distribution
with success probability `p` and `n` independent trials is given by
`z ↦ (1 - p + p * exp z) ^ n`. -/
theorem complexMGF_binomialReal (hX : μ.map X = binomialReal p h n) (z : ℂ) :
    complexMGF X μ z = (1 - p + p * cexp z) ^ n := by
  have hX_meas : AEMeasurable X μ :=
    aemeasurable_of_map_neZero (by rw [hX]; exact isProbabilityMeasure_binomialReal.neZero)
  rw [← complexMGF_id_map hX_meas, hX, complexMGF_id_binomialReal]

/-- The characteristic function of a binomial distribution with success probability `p` and `n`
independent trials is given by `t ↦ (1 - p + p * (exp (t * I))) ^ n`. -/
theorem charFun_binomialReal (t : ℝ) :
    charFun (binomialReal p h n) t = (1 - p + p * (cexp (t * I))) ^ n := by
  rw [← complexMGF_id_mul_I, complexMGF_id_binomialReal (t * I)]

/-- The moment-generating function of a random variable with binomial distribution with success
probability `p` and `n` independent trials is given by `t ↦ (1 - p + p * exp t) ^ n`. -/
theorem mgf_binomialReal (hX : μ.map X = binomialReal p h n) (t : ℝ) :
    mgf X μ t = (1 - p + p * rexp t) ^ n := by
  suffices (mgf X μ t : ℂ) = (1 - p + p * rexp t) ^ n from mod_cast this
  have hX_meas : AEMeasurable X μ :=
    aemeasurable_of_map_neZero (by rw [hX]; exact isProbabilityMeasure_binomialReal.neZero)
  rw [← mgf_id_map hX_meas, ← complexMGF_ofReal, hX, complexMGF_id_binomialReal]
  norm_cast

theorem mgf_fun_id_binomialReal :
    mgf (fun x ↦ x) (binomialReal p h n) = fun t ↦ (1 - p + p * rexp t) ^ n := by
  ext t
  exact mgf_binomialReal (h := h) (by simp) t

theorem mgf_id_binomialReal :
    mgf id (binomialReal p h n) = fun t ↦ (1 - p + p * rexp t) ^ n :=
  mgf_fun_id_binomialReal

/-- The cumulant-generating function of a random variable with binomial distribution with success
probability `p` and `n` independent trials is given by `t ↦??`. -/
theorem cgf_binomialReal (hX : μ.map X = binomialReal p h n) (t : ℝ) :
    cgf X μ t = n * Real.log (1 - p + p * rexp t) := by
  rw [cgf, mgf_binomialReal hX t, Real.log_pow]

lemma integrable_exp_mul_binomialReal (t : ℝ) :
    Integrable (fun x ↦ rexp (t * x)) (binomialReal p h n) := by
  rw [← mgf_pos_iff, mgf_fun_id_binomialReal]
  exact pow_pos (by
    rcases eq_or_lt_of_le p.coe_nonneg with hp | hp
    · simp [← hp]
    · linarith [sub_nonneg.mpr (show (p : ℝ) ≤ 1 from mod_cast h),
        mul_pos hp (Real.exp_pos t)]) _

@[simp]
lemma integrableExpSet_id_binomialReal :
    integrableExpSet id (binomialReal p h n) = Set.univ := by
  ext
  simpa [integrableExpSet] using integrable_exp_mul_binomialReal _

@[simp]
lemma integrableExpSet_fun_id_binomialReal :
    integrableExpSet (fun x ↦ x) (binomialReal p h n) = Set.univ :=
  integrableExpSet_id_binomialReal

end CharacteristicFunction

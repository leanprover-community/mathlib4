/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Distributions.SetBernoulli
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.HasLaw

import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Probability.Distributions.TwoValued
import Mathlib.Probability.Notation

/-!
# Binomial random variables

This file defines the binomial distribution and binomial random variables,
and computes their expectation and variance.

## Main definitions

* `ProbabilityTheory.binomial`:
  Binomial distribution on an arbitrary semiring with parameters `n` and `p`.

## Notation

`Bin(n, p)` is the binomial distribution with parameters `n` and `p` in `ℕ`.
`Bin(R, n, p)` is the binomial distribution with parameters `n` and `p` in `R`.
-/

public section

open MeasureTheory Set
open scoped NNReal ProbabilityTheory unitInterval ENNReal

namespace ProbabilityTheory
variable {R Ω : Type*} [MeasurableSpace R] [AddMonoidWithOne R] {m : MeasurableSpace Ω}
  {P : Measure Ω} {X : Ω → R} {n : ℕ} {p : I}

/-- The binomial probability distribution with parameter `p`. -/
@[expose]
noncomputable def binomial (n : ℕ) (p : I) : Measure ℕ := setBer(Iio n, p).map ncard

/-- The binomial probability distribution with parameter `p`. -/
scoped notation3 "Bin(" n ", " p ")" => binomial n p

/-- The binomial probability distribution with parameter `p` valued in the semiring `R`. -/
scoped notation3 "Bin(" R ", " n ", " p ")" => (binomial n p).map (Nat.cast : ℕ → R)

@[simp]
lemma binomial_nat : Bin(ℕ, n, p) = Bin(n, p) := Measure.map_id

lemma binomial_nat_zero : Bin(0, p) = Measure.dirac 0 := by simp [binomial]

@[simp]
lemma binomial_zero : Bin(R, 0, p) = Measure.dirac 0 := by
  simp [binomial, Measure.map_dirac' .of_discrete]

instance isProbabilityMeasure_binomial : IsProbabilityMeasure Bin(n, p) :=
  Measure.isProbabilityMeasure_map <| by fun_prop

lemma ae_le_of_hasLaw_binomial {X : Ω → ℕ} (hX : HasLaw X Bin(n, p) P) : ∀ᵐ ω ∂P, X ω ≤ n := by
  rw [hX.ae_iff (p := (· ≤ n)) <| by fun_prop, binomial,
    ae_map_iff (by fun_prop) (finite_Iic _).measurableSet]
  filter_upwards [setBernoulli_ae_subset] with s hs
  simpa using ncard_le_ncard hs

lemma binomial_nat_apply (s : Set ℕ) :
    Bin(n, p) s = setBer(Iio n, p) {t | t.ncard ∈ s ∧ t ⊆ Iio n} := by
  rw [binomial, Measure.map_apply (by fun_prop) (by measurability),
    setBernoulli_apply_eq_apply_subsets]
  simp

lemma binomial_apply [MeasurableSingletonClass R] [CharZero R] (s : Set ℕ) :
    Bin(R, n, p) (Nat.cast '' s) = setBer(Iio n, p) {t | t.ncard ∈ s ∧ t ⊆ Iio n} := by
  rw [Measure.map_apply (by fun_prop) ((Countable.to_set inferInstance).image _).measurableSet,
    binomial_nat_apply]
  simp

lemma binomial_real_nat_apply (s : Set ℕ) :
    Bin(n, p).real s = setBer(Iio n, p).real {t | t.ncard ∈ s ∧ t ⊆ Iio n} := by
  rw [measureReal_def, binomial_nat_apply, measureReal_def]

lemma binomial_real_apply [MeasurableSingletonClass R] [CharZero R] (s : Set ℕ) :
    Bin(R, n, p).real (Nat.cast '' s) =
      setBer(Iio n, p).real {t | t.ncard ∈ s ∧ t ⊆ Iio n} := by
  rw [measureReal_def, binomial_apply, measureReal_def]

lemma binomial_real_nat_singleton (n k : ℕ) (p : I) :
    Bin(n, p).real {k} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  classical
  have : {s | s.ncard ∈ ({k} : Set ℕ) ∧ s ⊆ Iio n}.Finite :=
    (finite_Iio n).finite_subsets.subset (by grind)
  rw [binomial_real_nat_apply, ← biUnion_of_singleton (setOf _)]
  simp_rw [← this.mem_toFinset]
  rw [measureReal_biUnion_finset (by simp) (by simp)]
  have h1 s (hs : s ∈ this.toFinset) :
      setBer(Iio n, p).real {s} = p ^ k * (1 - p) ^ (n - k) := by
    simp only [mem_singleton_iff, Finite.mem_toFinset, mem_setOf_eq] at hs
    rw [setBernoulli_real_singleton _ hs.2 (finite_Iio n),
      ncard_diff' hs.2 (finite_Iio n), ncard_Iio_nat, hs.1]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_assoc,
    ← ncard_eq_toFinset_card _ _]
  simp [ncard_powerset_ncard]

lemma binomial_real_singleton [MeasurableSingletonClass R] [CharZero R] (n k : ℕ) (p : I) :
    Bin(R, n, p).real {(k : R)} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  rw [map_measureReal_apply (by fun_prop) (by measurability)]
  convert binomial_real_nat_singleton n k p
  ext; simp

lemma binomial_singleton [MeasurableSingletonClass R] [CharZero R] (n k : ℕ) (p : I) :
    Bin(R, n, p) {(k : R)} = ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(R, n, p) _) (by simp), ← measureReal_def,
    binomial_real_singleton]

lemma binomial_singleton_nat (n k : ℕ) (p : I) :
    Bin(n, p) {k} = ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(n, p) _) (by simp), ← measureReal_def,
    binomial_real_nat_singleton]

lemma binomial_nat_eq (n : ℕ) (p : I) :
    Bin(n, p) =
      ∑ k ∈ Finset.Iic n, ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) •
        .dirac k := by
  apply Measure.ext_of_singleton
  intro k
  rw [binomial_singleton_nat, Measure.finset_sum_apply, Finset.sum_eq_single k]
  · simp
  · simp_all
  · simp_all [Nat.choose_eq_zero_of_lt]

lemma map_sum {ι α β : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace β} {m : ι → Measure α}
    {f : α → β} {s : Finset ι} (hf : AEMeasurable f (∑ i ∈ s, m i)) :
    Measure.map f (∑ i ∈ s, m i) = ∑ i ∈ s, (m i).map f := by
  rw [← Measure.sum_coe_finset, ← Measure.sum_coe_finset, Measure.map_sum]
  rwa [Measure.sum_coe_finset]

lemma binomial_eq [MeasurableSingletonClass R] (n : ℕ) (p : I) :
    Bin(R, n, p) =
      ∑ k ∈ Finset.Iic n, ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) •
        .dirac (k : R) := by
  rw [binomial_nat_eq, map_sum]
  · refine Finset.sum_congr rfl fun x hx ↦ ?_
    · rw [Measure.map_smul, Measure.map_dirac]
  · exact Measurable.aemeasurable (by fun_prop)

lemma integrable_binomial_nat {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) :
    Integrable f Bin(n, p) := by
  rw [binomial_nat_eq, integrable_finset_sum_measure]
  intro i hi
  apply Integrable.smul_measure
  · exact integrable_dirac (by simp)
  · simp

lemma integrable_binomial [MeasurableSingletonClass R] {E : Type*} [NormedAddCommGroup E]
    (f : R → E) :
    Integrable f Bin(R, n, p) := by
  rw [binomial_eq, integrable_finset_sum_measure]
  intro i hi
  apply Integrable.smul_measure
  · exact integrable_dirac (by simp)
  · simp

lemma integral_binomial_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℕ → E) :
    ∫ x, f x ∂Bin(n, p) =
      ∑ k ∈ Finset.Iic n, (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [binomial_nat_eq, integral_finset_sum_measure]
  · congr with
    simp only [integral_smul_measure, integral_dirac]
    rw [ENNReal.toReal_ofReal]
    have : 0 ≤ (1 - p : ℝ) := by grind
    have : 0 ≤ (p : ℝ) := by grind
    positivity
  exact fun _ _ ↦ (integrable_dirac (by simp)).smul_measure (by simp)

lemma integral_binomial [MeasurableSingletonClass R]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : R → E) :
    ∫ x, f x ∂Bin(R, n, p) =
      ∑ k ∈ Finset.Iic n, (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [integral_map .of_discrete (integrable_binomial f).aestronglyMeasurable, integral_binomial_nat]

lemma test' : ∫ x, x ∂Bin(ℝ, n, p) = p * n := by
  cases n with
  | zero => simp
  | succ n =>
  rw [integral_binomial]
  calc
  _ = ∑ k ∈ Finset.Iic (n + 1), (k * ((n + 1).choose k) *
      ((p : ℝ) ^ k * (1 - p) ^ (n + 1 - k))) := by
    congr with; rw [smul_eq_mul]; ring
  _ = ∑ k ∈ Finset.Iic n, (k + 1) * (n + 1).choose (k + 1) * ((p : ℝ) ^ (k + 1) *
      (1 - p) ^ (n - k)) := by
    rw [← Nat.range_succ_eq_Iic, Finset.sum_range_succ', Nat.range_succ_eq_Iic]
    simp
  _ = p * ∑ k ∈ Finset.Iic n, (n + 1) * (n.choose k) * ((p : ℝ) ^ k * (1 - p) ^ (n - k)) := by
    rw [Finset.mul_sum]
    congr with k
    rw [← n.cast_add_one, ← Nat.cast_mul, Nat.add_one_mul_choose_eq, pow_add]
    push_cast
    ring
  _ = p * (n + 1) * ∑ k ∈ Finset.range (n + 1), (p : ℝ) ^ k * (1 - p) ^ (n - k) * n.choose k := by
    rw [← Nat.range_succ_eq_Iic, Finset.mul_sum, Finset.mul_sum]
    congr with k
    ring
  _ = p * (n + 1 : ℕ) := by
    rw [← add_pow]
    simp

/-! ### Binomial random variables -/

variable {X : Ω → ℝ}

/-- **Expectation of a binomial random variable**.

The expectation of a binomial random variable with parameters `n` and `p` is `pn`. -/
lemma integral_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) : P[X] = p.val * n := by
  rw [hX.integral_eq, test']

/-- **Variance of a binomial random variable**.

The variance of a binomial random variable with parameters `n` and `p` is `p(1 - p)n`. -/
proof_wanted variance_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) :
    Var[X; P] = p * (1 - p) * n

/-- **Conditional variance of a binomial random variable**.

The conditional variance of a binomial random variable is the product of the conditional
probabilities that it's equal to `0` and that it's equal to `1`. -/
proof_wanted condVar_of_hasLaw_binomial {m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {P : Measure[m₀] Ω}
    (hX : HasLaw X Bin(ℝ, n, p) P) :
    Var[X; P | m] =ᵐ[P] P[X | m] * P[1 - X | m]

end ProbabilityTheory

/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Etienne Marion
-/
module

public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.SetBernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.HasLaw

import Mathlib.Data.Set.Notation
import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Probability.Distributions.TwoValued
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Notation

/-!
# Binomial random variables

This file defines the binomial distribution and binomial random variables,
and computes their expectation and variance. For `n : ℕ` and `p : I`,
the binomial distribution `Bin(n, p)` is defined as the cardinal of a random subset `U`
of `Set.Iic n` such that each `k ∈ Set.Iic n` belongs to `U` independently with probability `p`.

## Main definition

* `ProbabilityTheory.binomial`:
  Binomial distribution on an arbitrary semiring with parameters `n` and `p`.

## Implementation details

We provide the definition `binomial` with notation `Bin(n, P)` as the corresponding measure
over `ℕ`. We also introduce a notation `Bin(R, n p)` for the same measure but over a general
`AddMonoidWithOne R`, that stands for `Bin(n, p).map (Nat.cast : ℕ → R)`. This is in particular
useful if one is interested in the binomial distribution as a measure over `ℝ` or `ℤ`.
Results should be proven for both `Bin(n, p)` and `Bin(R, n, p)` when possible, using the first
one to prove the second. Note that results concerning `Bin(R, n, p)` may require
`[MeasurableSingletonClass R]` and/or `[CharZero R]`.

When refering to `Bin(n, p)` in names, use `binomial`. When refering to `Bin(R, n, p)`,
use `map_cast_binomial`.

## Notation

`Bin(n, p)` is the binomial distribution with parameters `n` and `p` in `ℕ`.
`Bin(R, n, p)` is the binomial distribution with parameters `n` and `p` in `R`.
-/

public section

open MeasureTheory Set Measure
open scoped NNReal ProbabilityTheory unitInterval ENNReal Set.Notation

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
lemma binomial_nat : Bin(ℕ, n, p) = Bin(n, p) := map_id

lemma binomial_zero : Bin(0, p) = dirac 0 := by simp [binomial]

@[simp]
lemma map_cast_binomial_zero : Bin(R, 0, p) = dirac 0 := by
  simp [binomial, map_dirac' .of_discrete]

instance isProbabilityMeasure_binomial : IsProbabilityMeasure Bin(n, p) :=
  isProbabilityMeasure_map <| by fun_prop

instance isProbabilityMeasure_map_cast_binomial : IsProbabilityMeasure Bin(R, n, p) :=
  isProbabilityMeasure_map .of_discrete

lemma ae_le_of_hasLaw_binomial {X : Ω → ℕ} (hX : HasLaw X Bin(n, p) P) : ∀ᵐ ω ∂P, X ω ≤ n := by
  rw [hX.ae_iff (p := (· ≤ n)) <| by fun_prop, binomial,
    ae_map_iff (by fun_prop) (finite_Iic _).measurableSet]
  filter_upwards [setBernoulli_ae_subset] with s hs
  simpa using ncard_le_ncard hs

lemma binomial_apply (s : Set ℕ) :
    Bin(n, p) s = setBer(Iio n, p) {t | t.ncard ∈ s ∧ t ⊆ Iio n} := by
  rw [binomial, map_ncard_setBernoulli_apply]

lemma map_cast_binomial_apply [MeasurableSingletonClass R] [CharZero R] (s : Set ℕ) :
    Bin(R, n, p) (Nat.cast '' s) = setBer(Iio n, p) {t | t.ncard ∈ s ∧ t ⊆ Iio n} := by
  rw [map_apply (by fun_prop) ((Countable.to_set inferInstance).image _).measurableSet,
    binomial_apply]
  simp

lemma binomial_real_apply (s : Set ℕ) :
    Bin(n, p).real s = setBer(Iio n, p).real {t | t.ncard ∈ s ∧ t ⊆ Iio n} := by
  rw [measureReal_def, binomial_apply, measureReal_def]

lemma map_cast_binomial_real_apply [MeasurableSingletonClass R] [CharZero R] (s : Set ℕ) :
    Bin(R, n, p).real (Nat.cast '' s) =
      setBer(Iio n, p).real {t | t.ncard ∈ s ∧ t ⊆ Iio n} := by
  rw [measureReal_def, map_cast_binomial_apply, measureReal_def]

lemma binomial_real_singleton (n k : ℕ) (p : I) :
    Bin(n, p).real {k} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  rw [binomial, map_ncard_setBernoulli_real_singleton (finite_Iio n), ncard_Iio_nat]

lemma map_cast_binomial_real_singleton [MeasurableSingletonClass R] [CharZero R] (n k : ℕ) (p : I) :
    Bin(R, n, p).real {(k : R)} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  rw [map_measureReal_apply (by fun_prop) (by measurability)]
  convert binomial_real_singleton n k p
  ext; simp

lemma binomial_singleton (n k : ℕ) (p : I) :
    Bin(n, p) {k} = ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(n, p) _) (by simp), ← measureReal_def,
    binomial_real_singleton]

lemma binomial_real_zero (n : ℕ) (p : I) :
    Bin(n, p).real {0} = (1 - p) ^ n := by simp [binomial_real_singleton]

lemma map_cast_binomial_real_zero [MeasurableSingletonClass R] [CharZero R] (n : ℕ) (p : I) :
    Bin(R, n, p).real {0} = (1 - p) ^ n := by
  rw [← Nat.cast_zero, map_cast_binomial_real_singleton]
  simp

lemma binomial_real_self (n : ℕ) (p : I) :
    Bin(n, p).real {n} = p ^ n := by simp [binomial_real_singleton]

lemma map_cast_binomial_real_self [MeasurableSingletonClass R] [CharZero R] (n : ℕ) (p : I) :
    Bin(R, n, p).real {(n : R)} = p ^ n := by simp [map_cast_binomial_real_singleton]

@[simp]
lemma binomial_nonneg {k : ℕ} : (0 : ℝ) ≤ (n.choose k) * p ^ k * (1 - p) ^ (n - k) :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by grind) _)) (pow_nonneg (by grind) _)

lemma map_cast_binomial_singleton [MeasurableSingletonClass R] [CharZero R] (n k : ℕ) (p : I) :
    Bin(R, n, p) {(k : R)} = ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(R, n, p) _) (by simp), ← measureReal_def,
    map_cast_binomial_real_singleton]

lemma binomial_eq_sum_dirac (n : ℕ) (p : I) :
    Bin(n, p) =
      ∑ k ∈ Finset.Iic n, ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) • dirac k := by
  refine ext_of_singleton fun k ↦ ?_
  rw [binomial_singleton, finset_sum_apply, Finset.sum_eq_single k]
  · simp
  · simp_all
  · simp_all [Nat.choose_eq_zero_of_lt]

lemma map_cast_binomial_eq_sum_dirac [MeasurableSingletonClass R] (n : ℕ) (p : I) :
    Bin(R, n, p) =
      ∑ k ∈ Finset.Iic n, ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) •
        dirac (k : R) := by
  rw [binomial_eq_sum_dirac, Measure.map_finset_sum .of_discrete]
  exact Finset.sum_congr rfl fun _ _ ↦ by rw [Measure.map_smul, map_dirac]

section Integral

variable {E : Type*} [NormedAddCommGroup E]

lemma integrable_map_cast_binomial [MeasurableSingletonClass R] (f : R → E) :
    Integrable f Bin(R, n, p) := by
  simp [map_cast_binomial_eq_sum_dirac, integrable_finset_sum_measure, integrable_dirac,
    Integrable.smul_measure]

lemma integrable_binomial (f : ℕ → E) :
    Integrable f Bin(n, p) := (integrable_map_cast_binomial f).comp_measurable .of_discrete

variable [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_binomial (f : ℕ → E) :
    ∫ x, f x ∂Bin(n, p) =
      ∑ k ∈ Finset.Iic n, (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [binomial_eq_sum_dirac, integral_finset_sum_measure]
  · simp
  exact fun _ _ ↦ (integrable_dirac (by simp)).smul_measure (by simp)

lemma integral_map_cast_binomial [MeasurableSingletonClass R]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : R → E) :
    ∫ x, f x ∂Bin(R, n, p) =
      ∑ k ∈ Finset.Iic n, (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [integral_map .of_discrete (integrable_map_cast_binomial f).aestronglyMeasurable,
    integral_binomial]

lemma l1 {ι : Type*} (u : Set ι) {S : Ω → Set ι} (hS : HasLaw S setBer(u, p) P) :
    iIndepFun (fun i ω ↦ i ∈ S ω) P := by
  have := hS.isProbabilityMeasure
  rw [iIndepFun_iff_finset]
  intro s
  rw [iIndepFun_iff_map_fun_eq_pi_map]
  · have : (fun ω i ↦ s.restrict (fun i ω ↦ i ∈ S ω) i ω) = (fun t (i : s) ↦ i.1 ∈ t) ∘ S := by
      ext; simp
    have h1 : (fun t (i : s) ↦ i.1 ∈ t) ∘ (fun (p : ι → Prop) ↦ {i | p i}) = s.restrict := by
      ext; simp
    rw [this, ← AEMeasurable.map_map_of_aemeasurable, hS.map_eq, setBernoulli_eq_map, map_map,
      h1, infinitePi_map_restrict]
    · congr
      ext i : 1
      have : s.restrict (fun i ω ↦ i ∈ S ω) i = (fun t ↦ i.1 ∈ t) ∘ S := by ext; simp
      have h1 : (fun t ↦ i.1 ∈ t) ∘ (fun (p : ι → Prop) ↦ {i | p i}) = Function.eval i.1 := by
        ext; simp
      rw [this, ← AEMeasurable.map_map_of_aemeasurable, hS.map_eq, setBernoulli_eq_map, map_map, h1,
        infinitePi_map_eval]
      all_goals fun_prop
    any_goals fun_prop
  intro
  exact ((Finset.measurable_restrict s).comp_aemeasurable hS.aemeasurable).eval _

lemma measurePreserving_ncard_setBernoulli_binomial_ncard {ι : Type*} [Countable ι] {u : Set ι}
    (hu : u.Finite) :
    MeasurePreserving ncard setBer(u, p) Bin(u.ncard, p) where
  measurable := by fun_prop
  map_eq := by
    refine ext_of_singleton fun k ↦ ?_
    rw [binomial_singleton, map_ncard_setBernoulli_singleton hu]

/-- A sum of `n` independent Bernoulli random variables is a binomial random variable. -/
lemma iIndepFun.hasLaw_finset_sum_binomial {ι : Type*} {s : Finset ι} {X : ι → Ω → ℕ}
    (hX : iIndepFun (s.restrict X) P)
    (lawX : ∀ i ∈ s, HasLaw (X i) Ber(1, 0, p) P) :
    HasLaw (∑ i ∈ s, X i) Bin(s.card, p) P := by
  classical
  obtain ⟨Ω', mΩ', P', S, -, hS⟩ := setBer((Finset.univ (α := s) : Set s), p).exists_hasLaw
  convert hS.hasLaw_indicator_pi_of_setBernoulli.comp_of_hasLaw_comp
    (f := fun x ↦ ∑ i, x i) (Y := fun ω i ↦ X i.1 ω) (by fun_prop) ?_ ?_
  · simp only [Finset.sum_apply]
    rw [← Finset.sum_coe_sort, ← Finset.sum_coe_sort]
  · exact iIndepFun.hasLaw_pi (fun i ↦ lawX i i.1.2) (hX.precomp (fun _ _ _ ↦ by grind))
  have : HasLaw (fun ω ↦ (S ω).ncard) Bin(s.card, p) P' := by
    convert (measurePreserving_ncard_setBernoulli_binomial_ncard (by simp)).comp_hasLaw hS
    simp
  convert this with ω
  rw [Set.ncard_eq_toFinset_card _ (toFinite (S ω)), Finset.card_eq_sum_ite (Finset.subset_univ _),
    ← Finset.univ.sum_coe_sort]
  congr with i
  simp [Set.indicator]

end Integral

/-! ### Binomial random variables -/

variable {X : Ω → ℝ}

/-- **Expectation of a binomial random variable**.

The expectation of a binomial random variable with parameters `n` and `p` is `pn`. -/
proof_wanted integral_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) : P[X] = p.val * n

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

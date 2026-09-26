/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.SetBernoulli

import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Probability.HasLawExists

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

We provide the definition `binomial` with notation `Bin(n, p)` as the corresponding measure
over `ℕ`. We also introduce a notation `Bin(R, n, p)` for the same measure but over a general
`AddMonoidWithOne R`, that stands for `Bin(n, p).map (Nat.cast : ℕ → R)`. This is in particular
useful if one is interested in the binomial distribution as a measure over `ℝ` or `ℤ`.
Results should be proven for both `Bin(n, p)` and `Bin(R, n, p)` when possible, using the first
one to prove the second. Note that results concerning `Bin(R, n, p)` may require
`[MeasurableSingletonClass R]` and/or `[CharZero R]`.

When referring to `Bin(n, p)` in names, use `binomial`. When referring to `Bin(R, n, p)`,
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

instance isProbabilityMeasure_binomial : IsProbabilityMeasure Bin(n, p) := by
  rw [binomial]
  infer_instance

lemma ae_le_of_hasLaw_binomial {X : Ω → ℕ} (hX : HasLaw X Bin(n, p) P) : ∀ᵐ ω ∂P, X ω ≤ n := by
  rw [hX.ae_iff (p := (· ≤ n)) <| by fun_prop, binomial,
    ae_map_iff (by fun_prop) (finite_Iic _).measurableSet]
  filter_upwards [setBernoulli_ae_subset] with s hs
  simpa using ncard_le_ncard hs

lemma binomial_real_singleton (n k : ℕ) (p : I) :
    Bin(n, p).real {k} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  rw [binomial, map_ncard_setBernoulli_real_singleton (finite_Iio n), ncard_Iio_nat]

lemma binomial_singleton (n k : ℕ) (p : I) :
    Bin(n, p) {k} = ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(n, p) _) (by simp), ← measureReal_def,
    binomial_real_singleton]

lemma map_cast_binomial_real_singleton [MeasurableSingletonClass R] [CharZero R] (n k : ℕ) (p : I) :
    Bin(R, n, p).real {(k : R)} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  rw [map_measureReal_apply (by fun_prop) (by measurability)]
  convert binomial_real_singleton n k p
  ext; simp

@[simp]
lemma binomial_nonneg {k : ℕ} : (0 : ℝ) ≤ (n.choose k) * p ^ k * (1 - p) ^ (n - k) :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by grind) _)) (pow_nonneg (by grind) _)

lemma map_cast_binomial_singleton [MeasurableSingletonClass R] [CharZero R] (n k : ℕ) (p : I) :
    Bin(R, n, p) {(k : R)} = ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(R, n, p) _) (by simp), ← measureReal_def,
    map_cast_binomial_real_singleton]

@[simp]
lemma binomial_real_zero (n : ℕ) (p : I) :
    Bin(n, p).real {0} = (1 - p) ^ n := by simp [binomial_real_singleton]

@[simp]
lemma map_cast_binomial_real_zero [MeasurableSingletonClass R] [CharZero R] (n : ℕ) (p : I) :
    Bin(R, n, p).real {0} = (1 - p) ^ n := by
  rw [← Nat.cast_zero, map_cast_binomial_real_singleton]
  simp

@[simp]
lemma binomial_real_self (n : ℕ) (p : I) :
    Bin(n, p).real {n} = p ^ n := by simp [binomial_real_singleton]

@[simp]
lemma map_cast_binomial_real_self [MeasurableSingletonClass R] [CharZero R] (n : ℕ) (p : I) :
    Bin(R, n, p).real {(n : R)} = p ^ n := by simp [map_cast_binomial_real_singleton]

lemma binomial_one_eq_bernoulliMeasure (p : I) :
    Bin(1, p) = Ber(1, 0, p) := by
  refine ext_of_measureReal_singleton fun k ↦ ?_
  match k with
  | 0 | 1 => simp
  | k + 2 => simp [binomial_real_singleton, Nat.choose_eq_zero_of_lt]

lemma map_cast_binomial_one_eq_bernoulliMeasure (p : I) :
    Bin(R, 1, p) = Ber(1, 0, p) := by
  rw [binomial_one_eq_bernoulliMeasure, map_bernoulliMeasure']
  · simp
  · fun_prop

lemma binomial_eq_sum_dirac (n : ℕ) (p : I) :
    Bin(n, p) =
      ∑ k ∈ Finset.Iic n, ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) • dirac k := by
  refine ext_of_singleton fun k ↦ ?_
  rw [binomial_singleton, finsetSum_apply, Finset.sum_eq_single k]
  · simp
  · simp_all
  · simp_all [Nat.choose_eq_zero_of_lt]

lemma map_cast_binomial_eq_sum_dirac [MeasurableSingletonClass R] (n : ℕ) (p : I) :
    Bin(R, n, p) =
      ∑ k ∈ Finset.Iic n, ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) •
        dirac (k : R) := by
  rw [binomial_eq_sum_dirac, Measure.map_finset_sum .of_discrete]
  exact Finset.sum_congr rfl fun _ _ ↦ by rw [Measure.map_smul _ (by fun_prop), map_dirac]

section Integral

variable {E : Type*} [NormedAddCommGroup E]

lemma integrable_map_cast_binomial [MeasurableSingletonClass R] (f : R → E) :
    Integrable f Bin(R, n, p) := by
  simp [map_cast_binomial_eq_sum_dirac, integrable_finsetSum_measure, integrable_dirac,
    Integrable.smul_measure]

lemma integrable_binomial (f : ℕ → E) :
    Integrable f Bin(n, p) := (integrable_map_cast_binomial f).comp_measurable .of_discrete

variable [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_binomial (f : ℕ → E) :
    ∫ x, f x ∂Bin(n, p) =
      ∑ k ∈ Finset.Iic n, (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [binomial_eq_sum_dirac, integral_finsetSum_measure]
  · simp
  exact fun _ _ ↦ (integrable_dirac (by simp)).smul_measure (by simp)

lemma integral_map_cast_binomial [MeasurableSingletonClass R] (f : R → E) :
    ∫ x, f x ∂Bin(R, n, p) =
      ∑ k ∈ Finset.Iic n, (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [integral_map .of_discrete (integrable_map_cast_binomial f).aestronglyMeasurable,
    integral_binomial]

lemma measurePreserving_ncard_setBernoulli_binomial_ncard {ι : Type*} [Countable ι] {u : Set ι}
    (hu : u.Finite) :
    MeasurePreserving ncard setBer(u, p) Bin(u.ncard, p) where
  measurable := by fun_prop
  map_eq := by
    refine ext_of_singleton fun k ↦ ?_
    rw [binomial_singleton, map_ncard_setBernoulli_singleton hu]

/-- The sum of two independent binomial random variables is a binomial random variable. -/
lemma IndepFun.hasLaw_add_map_cast_binomial [MeasurableAdd₂ R] {X Y : Ω → R} {n1 n2 : ℕ} (p : I)
    (hXY : X ⟂ᵢ[P] Y) (hX : HasLaw X (Bin(R, n1, p)) P) (hY : HasLaw Y (Bin(R, n2, p)) P) :
    HasLaw (X + Y) Bin(R, n1 + n2, p) P := by
  obtain ⟨Ω', mΩ', P', S, -, hS⟩ := (setBer(Iio (n1 + n2), p)).exists_hasLaw
  have := hS.isProbabilityMeasure
  have := hX.isProbabilityMeasure
  have : HasLaw (fun ω ↦ (((S ω ∩ (Iio n1)).ncard : R), ((S ω ∩ (Ico n1 (n1 + n2))).ncard : R)))
      (Bin(R, n1, p).prod Bin(R, n2, p)) P' := by
    refine IndepFun.hasLaw_prod ?_ ?_ ?_
    · have := hS.inter (u := Iio n1)
      simp only [Iio_inter_Iio, le_add_iff_nonneg_right, zero_le, inf_of_le_right] at this
      convert hasLaw_map .of_discrete |>.comp <|
        (measurePreserving_ncard_setBernoulli_binomial_ncard (finite_Iio n1)).comp_hasLaw this
      all_goals simp
    · have := hS.inter (u := Ico n1 (n1 + n2))
      rw [show Iio (n1 + n2) ∩ Ico n1 (n1 + n2) = Ico n1 (n1 + n2) by grind] at this
      convert hasLaw_map .of_discrete |>.comp <|
        (measurePreserving_ncard_setBernoulli_binomial_ncard (finite_Ico n1 _)).comp_hasLaw this
      all_goals simp
    refine (indepFun_inter (t := Iio n1) (u := Ico n1 (n1 + n2)) hS ?_).comp
      (φ := (Nat.cast (R := R)) ∘ ncard) (ψ := (Nat.cast (R := R)) ∘ ncard) ?_ ?_
    · grind
    all_goals fun_prop
  convert this.comp_of_hasLaw_comp
    (f := fun x ↦ x.1 + x.2) (Y := (fun ω ↦ (X ω, Y ω))) (by fun_prop) ?_ ?_
  · simp
  · exact hXY.hasLaw_prod hX hY
  simp only
  convert ((hasLaw_map .of_discrete).comp <|
    (measurePreserving_ncard_setBernoulli_binomial_ncard (finite_Iio _)).comp_hasLaw hS).congr
    ?_
  · simp
  filter_upwards [IsSetBernoulli.ae_subset hS] with ω hω
  rw [← Nat.cast_add, ← ncard_union_eq, ← inter_union_distrib_left, Iio_union_Ico]
  · simp [inter_eq_left.2 hω]
  · grind
  · grind

/-- The sum of two independent binomial random variables is a binomial random variable. -/
lemma IndepFun.hasLaw_add_binomial {X Y : Ω → ℕ}
    {n1 n2 : ℕ} (p : I)
    (hXY : X ⟂ᵢ[P] Y) (hX : HasLaw X (Bin(n1, p)) P) (hY : HasLaw Y (Bin(n2, p)) P) :
    HasLaw (X + Y) Bin(n1 + n2, p) P := by
  convert hXY.hasLaw_add_map_cast_binomial p (binomial_nat ▸ hX) (binomial_nat ▸ hY)
  simp

/-- The sum of independent binomial random variables is a binomial random variable. -/
private lemma iIndepFun.hasLaw_finsetSum_map_cast_binomial {R ι : Type*}
    [MeasurableSpace R] [AddCommMonoidWithOne R] [MeasurableAdd₂ R]
    {X : ι → Ω → R} {s : Finset ι} {n : ι → ℕ} (p : I)
    (hX : iIndepFun X P) (lX : ∀ i, HasLaw (X i) Bin(R, n i, p) P) :
    HasLaw (∑ i ∈ s, X i) Bin(R, ∑ i ∈ s, n i, p) P := by
  classical
  have := hX.isProbabilityMeasure
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, map_cast_binomial_zero]
    exact hasLaw_dirac_of_ae_eq .rfl
  | insert i s hi h =>
    simp_rw [Finset.sum_insert hi]
    refine IndepFun.hasLaw_add_map_cast_binomial p ?_ (lX i) h
    · refine hX.indepFun_finsetSum_of_notMem₀ ?_ hi |>.symm
      fun_prop

/-- The sum of independent binomial random variables is a binomial random variable. -/
lemma iIndepFun.hasLaw_fintypeSum_map_cast_binomial {R ι : Type*} [Fintype ι]
    [MeasurableSpace R] [AddCommMonoidWithOne R] [MeasurableAdd₂ R]
    {X : ι → Ω → R} {n : ι → ℕ} (p : I)
    (hX : iIndepFun X P) (lX : ∀ i, HasLaw (X i) Bin(R, n i, p) P) :
    HasLaw (∑ i, X i) Bin(R, ∑ i, n i, p) P :=
  hX.hasLaw_finsetSum_map_cast_binomial p lX

/-- The sum of independent binomial random variables is a binomial random variable. -/
lemma iIndepFun.hasLaw_finsetSum_map_cast_binomial' {R ι : Type*}
    [MeasurableSpace R] [AddCommMonoidWithOne R] [MeasurableAdd₂ R]
    {X : ι → Ω → R} {s : Finset ι} {n : ι → ℕ} (p : I)
    (hX : iIndepFun (s.restrict X) P) (lX : ∀ i ∈ s, HasLaw (X i) Bin(R, n i, p) P) :
    HasLaw (∑ i ∈ s, X i) Bin(R, ∑ i ∈ s, n i, p) P := by
  convert hX.hasLaw_fintypeSum_map_cast_binomial p (n := s.restrict n) fun i ↦ lX i.1 i.2
  · simp [Finset.sum_attach]
  · simp [Finset.sum_attach]

/-- The sum of independent binomial random variables is a binomial random variable. -/
lemma iIndepFun.hasLaw_fintypeSum_binomial {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℕ} {n : ι → ℕ} (p : I)
    (hX : iIndepFun X P) (lX : ∀ i, HasLaw (X i) Bin(n i, p) P) :
    HasLaw (∑ i, X i) Bin(∑ i, n i, p) P := by
  rw [← binomial_nat]
  exact hX.hasLaw_fintypeSum_map_cast_binomial p (by simpa using lX)

/-- The sum of independent binomial random variables is a binomial random variable. -/
lemma iIndepFun.hasLaw_finsetSum_binomial {ι : Type*}
    {X : ι → Ω → ℕ} {s : Finset ι} {n : ι → ℕ} (p : I)
    (hX : iIndepFun (s.restrict X) P) (lX : ∀ i ∈ s, HasLaw (X i) Bin(n i, p) P) :
    HasLaw (∑ i ∈ s, X i) Bin(∑ i ∈ s, n i, p) P := by
  rw [← binomial_nat]
  exact hX.hasLaw_finsetSum_map_cast_binomial' p (by simpa using lX)

/-- A sum of independent Bernoulli random variables is a binomial random variable. -/
lemma iIndepFun.hasLaw_finsetSum_bernoulli_map_cast_binomial {ι R : Type*} {s : Finset ι}
    {X : ι → Ω → R}
    [MeasurableSpace R] [AddCommMonoidWithOne R] [MeasurableAdd₂ R]
    (hX : iIndepFun (s.restrict X) P) (lawX : ∀ i ∈ s, HasLaw (X i) Ber(1, 0, p) P) :
    HasLaw (∑ i ∈ s, X i) Bin(R, s.card, p) P := by
  simp_rw [← map_cast_binomial_one_eq_bernoulliMeasure] at lawX
  convert hX.hasLaw_finsetSum_map_cast_binomial' p lawX
  simp

/-- A sum of independent Bernoulli random variables is a binomial random variable. -/
lemma iIndepFun.hasLaw_finsetSum_bernoulli_binomial {ι : Type*} {s : Finset ι} {X : ι → Ω → ℕ}
    (hX : iIndepFun (s.restrict X) P) (lawX : ∀ i ∈ s, HasLaw (X i) Ber(1, 0, p) P) :
    HasLaw (∑ i ∈ s, X i) Bin(s.card, p) P := by
  convert hX.hasLaw_finsetSum_bernoulli_map_cast_binomial lawX
  simp

/-- A sum of independent Bernoulli random variables is a binomial random variable. -/
lemma iIndepFun.hasLaw_sum_map_cast_binomial {ι : Type*} (R : Type*) [Fintype ι] {X : ι → Ω → R}
    [MeasurableSpace R] [AddCommMonoidWithOne R] [MeasurableAdd₂ R]
    (hX : iIndepFun X P) (lawX : ∀ i, HasLaw (X i) Ber(1, 0, p) P) :
    HasLaw (∑ i, X i) Bin(R, Fintype.card ι, p) P := by
  convert (hX.restrict _).hasLaw_finsetSum_bernoulli_map_cast_binomial ?_
  · simp
  · simpa

/-- A sum of independent Bernoulli random variables is a binomial random variable. -/
lemma iIndepFun.hasLaw_sum_binomial {ι : Type*} [Fintype ι] {X : ι → Ω → ℕ}
    (hX : iIndepFun X P) (lawX : ∀ i, HasLaw (X i) Ber(1, 0, p) P) :
    HasLaw (∑ i, X i) Bin(Fintype.card ι, p) P := by
  convert hX.hasLaw_sum_map_cast_binomial ℕ lawX
  simp

end Integral

/-! ### Binomial random variables -/

variable {X : Ω → ℝ}

/-- **Expectation of a binomial random variable**.

The expectation of a binomial random variable with parameters `n` and `p` is `pn`. -/
theorem integral_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) : P[X] = p.val * n := by
  rw [hX.integral_eq, integral_map_cast_binomial, ← n.range_succ_eq_Iic, Finset.sum_range_succ']
  cases n with norm_num | succ n
  calc
    _ = p * ∑ x ∈ Finset.range (n + 1), (n + 1).choose (x + 1) * (x + 1) *
        p.val ^ x * (1 - p) ^ (n - x) := by grind [Finset.mul_sum]
    _ = p * ∑ x ∈ Finset.range (n + 1), n.choose x * (n + 1) * p.val ^ x * (1 - p) ^ (n - x) := by
      congrm p * ∑ x ∈ Finset.range (n + 1), ?_ * p.val ^ x * (1 - p) ^ (n - x)
      norm_cast
      rw [← Nat.add_one_mul_choose_eq n x, mul_comm]
    _ = p * (n + 1) * ∑ x ∈ Finset.range (n + 1), n.choose x * p.val ^ x * (1 - p) ^ (n - x) := by
      rw [mul_assoc, Finset.mul_sum (a := (n : ℝ) + 1)]
      group
    _ = p * (n + 1) := by grind [add_pow p.val (1 - p) n, one_pow]

end ProbabilityTheory

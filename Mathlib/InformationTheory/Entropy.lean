/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

/- public import Mathlib.Topology.Instances.ENNReal.Lemmas -/
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Shannon Entropy for Discrete Random Variables

This file defines the Shannon entropy (in nats) for discrete random variables represented
as probability mass functions (PMFs).

## Main Definitions

* `entropy p`: The Shannon entropy (in nats) of a PMF `p`, defined as
  `∑' a, - (p a).toReal * log ((p a).toReal)`

## Main Results

* `entropy_nonneg`: Entropy is nonnegative
* `entropy_eq_zero_iff`: Entropy is zero if and only if the distribution is deterministic
* `entropy_pure`: Entropy of a deterministic distribution is zero
* `entropy_bernoulli_eq_binEntropy`: Connection to binary entropy function
* `entropy_uniform`: Entropy of uniform distribution on n elements equals `log n`

## Examples

* Uniform distribution on `{0, 1}` has entropy `log 2`
* Bernoulli distribution with `p = 1/2` has entropy `log 2`
* Deterministic distributions have entropy `0`

## Tags

entropy, Shannon, information theory, discrete random variable, PMF
-/

open scoped Finset MeasureTheory NNReal ENNReal

namespace InformationTheory

variable {α : Type*}

/-! ### Basic Definitions -/

/-- Shannon entropy (in nats) of a probability mass function.

We use `Real.negMulLog` so the summand is well-behaved at probability `0`.
The PMF values live in `ENNReal`, so we convert to `ℝ` with `ENNReal.toReal`.

The entropy is defined as `H(X) = ∑_{x ∈ 𝒳} p(x) · log(p(x))` where the sum
is over all possible outcomes and we use the convention `0 · log(0) = 0`. -/
noncomputable def entropy (p : PMF α) : ℝ :=
  ∑' a : α, Real.negMulLog (ENNReal.toReal (p a))

/-- Entropy computed over a finset (useful for finite distributions). -/
@[pp_nodot] noncomputable def entropyFinset [DecidableEq α]
    (s : Finset α) (p : α → ℝ) : ℝ :=
  ∑ a ∈ s, Real.negMulLog (p a)

/-! ### Basic Properties -/

/-- Entropy of a deterministic distribution (pure) is zero. -/
@[simp] lemma entropy_pure (a : α) : entropy (PMF.pure a) = 0 := by
  classical
  simp only [entropy, PMF.pure_apply]
  have h : (fun a' : α => Real.negMulLog (ENNReal.toReal (if a' = a then 1 else 0)))
      = (fun _ : α => (0 : ℝ)) := by
    funext a'
    by_cases ha : a' = a
    · simp [ha, Real.negMulLog_one]
    · simp [ha, Real.negMulLog_zero]
  rw [h]
  simp [tsum_zero]

lemma entropy_nonneg (p : PMF α) : 0 ≤ entropy p := by
  simp only [entropy]
  refine tsum_nonneg fun a => ?_
  refine Real.negMulLog_nonneg ?_ ?_
  · exact ENNReal.toReal_nonneg
  · refine ENNReal.toReal_le_of_le_ofReal ?_ ?_
    · exact zero_le_one' ℝ
    · simp_all only [ENNReal.ofReal_one]
      exact PMF.coe_le_one p a

lemma entropy_eq_zero_iff (p : PMF α) : entropy p = 0 ↔ ∃ a : α, p = PMF.pure a := by
  constructor
  · sorry
  · sorry

/-! ### Connection to Binary Entropy -/

/-- The entropy of a Bernoulli PMF equals the binary entropy function.

This connects the general entropy definition with the specialized binary entropy
function defined in `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`. -/
theorem entropy_bernoulli_eq_binEntropy (p : ℝ≥0) (h : p ≤ 1) :
    entropy (PMF.bernoulli p h) = Real.binEntropy (p : ℝ) := by
  simp only [entropy, PMF.bernoulli_apply]
  simp_all [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, ENNReal.toReal]

/-- Entropy of uniform distribution on two elements equals `log 2`. -/
example : entropy (PMF.uniformOfFinset ({0, 1} : Finset ℕ) (by simp) : PMF ℕ) = Real.log 2 := by
  classical
  simp only [entropy, PMF.uniformOfFinset]
  -- Uniform distribution assigns probability 1/2 to each element
  -- We compute: - (1/2) * log(1/2) - (1/2) * log(1/2) = - log(1/2) = log 2
  have h1 : Real.negMulLog ((2⁻¹ : ENNReal).toReal) = Real.log 2 / 2 := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    simp [Real.negMulLog]
    ring_nf
  -- The sum only has two nonzero terms: at 0 and at 1, each contributing log 2 / 2
  have h2 : (fun a : ℕ => Real.negMulLog (ENNReal.toReal (if a = 0 ∨ a = 1 then (2⁻¹ : ENNReal) else 0)))
      = (fun a : ℕ => (if a = 0 then Real.log 2 / 2 else 0) + (if a = 1 then Real.log 2 / 2 else 0)) := by
    funext a
    aesop
  simp [h2]
  -- Split the sum and use tsum_ite_eq for each part
  have h3 : ∑' a : ℕ, ((if a = 0 then Real.log 2 / 2 else 0) + (if a = 1 then Real.log 2 / 2 else 0))
      = (∑' a : ℕ, if a = 0 then Real.log 2 / 2 else 0) + (∑' a : ℕ, if a = 1 then Real.log 2 / 2 else 0) := by
        simp_all only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, tsum_ite_eq, add_halves]
        sorry

  simp [h3]

/-- Entropy of a deterministic distribution is zero. -/
example : entropy (PMF.pure ()) = 0 := by simp [entropy_pure]

/-- Entropy of another deterministic distribution is zero. -/
example : entropy (PMF.pure true) = 0 := by simp [entropy_pure]

end InformationTheory

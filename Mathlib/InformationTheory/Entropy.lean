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

public section

open scoped Finset MeasureTheory NNReal ENNReal

namespace InformationTheory

variable {α β : Type*}

/-! ### Basic Definitions -/

/-- Shannon entropy (in nats) of a probability mass function.

We use `Real.negMulLog` so the summand is well-behaved at probability `0`.
The PMF values live in `ENNReal`, so we convert to `ℝ` with `ENNReal.toReal`.

The entropy is defined as `H(X) = ∑_{x ∈ 𝒳} p(x) · log(p(x))` where the sum
is over all possible outcomes and we use the convention `0 · log(0) = 0`. -/
noncomputable def entropy (p : PMF α) : ℝ :=
  ∑' a : α, Real.negMulLog (ENNReal.toReal (p a))

@[simp] lemma entropy_def (p : PMF α) :
    entropy p = ∑' a : α, Real.negMulLog (ENNReal.toReal (p a)) := by simp only [entropy]

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

/-- Entropy of a deterministic distribution is zero. -/
example : entropy (PMF.pure ()) = 0 := by simp only [entropy_pure]
/-- Entropy of another deterministic distribution is zero. -/
example : entropy (PMF.pure true) = 0 := by simp only [entropy_pure]

/-- Entropy of a PMF is non negative. -/
@[simp] lemma entropy_nonneg (p : PMF α) : 0 ≤ entropy p := by
  simp only [entropy]
  refine tsum_nonneg fun a => ?_
  refine Real.negMulLog_nonneg ?_ ?_
  · exact ENNReal.toReal_nonneg
  · refine ENNReal.toReal_le_of_le_ofReal ?_ ?_
    · exact zero_le_one' ℝ
    · simp_all only [ENNReal.ofReal_one]
      exact PMF.coe_le_one p a

lemma entropy_eq_zero_iff (p : PMF α) [Finite α] :
  entropy p = 0 ↔ ∃ a : α, p = PMF.pure a := by
  classical
  constructor
  · intro hE
    by_contra h
    -- When p is not pure, the support has at least two elements
    obtain ⟨a0, ha0⟩ := p.support_nonempty
    have h_supp : Set.Nontrivial p.support := by
      rw [Set.nontrivial_iff_ne_singleton ha0]
      intro heq
      have h1 : p a0 = 1 := (p.apply_eq_one_iff a0).2 heq
      have : p = pure a0 := PMF.ext fun x => by
        /- by_cases hx : x = a0 <;> simp [pure] -/
        by_cases hx : x = a0 <;> simp only [pure, PMF.pure_apply]
        · simp_all only [not_exists, Set.mem_singleton_iff, ↓reduceIte]
        · simp_all only [entropy_def, not_exists, Set.mem_singleton_iff, ↓reduceIte]
          refine (PMF.apply_eq_zero_iff p x).mpr ?_
          simp_all only [Set.mem_singleton_iff, not_false_eq_true]
        /- exact (p.apply_eq_zero_iff x).2 (fun h' => hx (Set.mem_singleton_iff.1 (heq.symm h'))) -/
      exact h ⟨a0, this⟩
    obtain ⟨a, ha, a', ha', haa'⟩ := h_supp
    have ha_pos : 0 < (p a).toReal :=
      ENNReal.toReal_pos ((p.mem_support_iff a).1 ha) (p.apply_ne_top a)
    have ha'_pos : 0 < (p a').toReal :=
      ENNReal.toReal_pos ((p.mem_support_iff a').1 ha') (p.apply_ne_top a')
    have ha_lt_one : (p a).toReal < 1 := by
      by_contra h_not
      push_neg at h_not
      /- have h1 : (p a).toReal = 1 := le_antisymm ?_ h_not -/
      have h1 : (p a).toReal = 1 := le_antisymm
        (by
          have hpa : p a ≤ (1 : ENNReal) := PMF.coe_le_one p a
          refine ENNReal.toReal_le_of_le_ofReal (by simp) (by simpa using hpa)
        ) 
        h_not
      /- have h1 : (p a).toReal = 1 := le_antisymm (by aesop?) h_not -/
      /- have h2 : p a = 1 := by simp [(ENNReal.toReal_eq_one_iff (p a))] -/
      have h2 : p a = 1 := by 
        simp_all only [entropy_def, not_exists, PMF.mem_support_iff, ne_eq, zero_lt_one, le_refl]
        exact (ENNReal.toReal_eq_one_iff (p a)).1 h1
        
      have : p.support = {a} := (p.apply_eq_one_iff a).1 h2
      have : p = pure a := PMF.ext fun x => by
        by_cases hx : x = a <;> simp_all only [not_exists, Set.mem_singleton_iff, 
                                               ne_eq, not_true_eq_false]
      exact h ⟨a, this⟩
    have ha'_lt_one : (p a').toReal < 1 := by
      by_contra h_not
      push_neg at h_not
      /- have h1 : (p a).toReal = 1 := le_antisymm ?_ h_not -/
      have h1 : (p a').toReal = 1 := le_antisymm
        (by
          have hpa : p a' ≤ (1 : ENNReal) := PMF.coe_le_one p a'
          refine ENNReal.toReal_le_of_le_ofReal (by simp) (by simpa using hpa)
        ) 
        h_not
      /- have h1 : (p a).toReal = 1 := le_antisymm (by aesop?) h_not -/
      /- have h2 : p a = 1 := by simp [(ENNReal.toReal_eq_one_iff (p a))] -/
      have h2 : p a' = 1 := by 
        simp_all only [entropy_def, not_exists, PMF.mem_support_iff, ne_eq, zero_lt_one, le_refl]
        exact (ENNReal.toReal_eq_one_iff (p a')).1 h1
        
      have : p.support = {a'} := (p.apply_eq_one_iff a').1 h2
      have : p = pure a := PMF.ext fun x => by
        by_cases hx : x = a' <;> simp_all only [not_exists, Set.mem_singleton_iff]
      exact h ⟨a, this⟩
    
    have h_neg_pos : ∀ x : ℝ, 0 < x → x < 1 → 0 < Real.negMulLog x := by
      intro x hx0 hx1
      rw [Real.negMulLog_eq_neg, neg_pos]
      exact mul_neg_of_pos_of_neg hx0 (Real.log_neg hx0 hx1)
    have h1 : 0 < Real.negMulLog ((p a).toReal) := h_neg_pos _ ha_pos ha_lt_one
    have h2 : 0 < Real.negMulLog ((p a').toReal) := h_neg_pos _ ha'_pos ha'_lt_one
    have h_summable : Summable (fun b : α => Real.negMulLog (ENNReal.toReal (p b))) :=
      Summable.of_finite
    have h_rest_summable : Summable (fun b => 
      if b = a then 0 else Real.negMulLog (ENNReal.toReal (p b))) := Summable.of_finite
    have h_sum :
        Real.negMulLog ((p a').toReal)
          ≤ ∑' b : α, if b = a then 0 else Real.negMulLog ((p b).toReal) := by
      have ha'ne : a' ≠ a := ne_comm.1 haa'
      -- pointwise nonneg of the "rest" function
      have h_nonneg :
          ∀ b : α, 0 ≤ (if b = a then 0 else Real.negMulLog ((p b).toReal)) := by
        intro b
        by_cases hb : b = a
        · simp [hb]
        · -- `negMulLog` is nonnegative on `[0,1]`
          have hb0 : 0 ≤ (p b).toReal := ENNReal.toReal_nonneg
          have hb1 : (p b).toReal ≤ 1 := by
            have hpb : p b ≤ (1 : ENNReal) := PMF.coe_le_one p b
            -- convert toReal ≤ 1
            exact ENNReal.toReal_le_of_le_ofReal (by simp) (by simpa using hpb)
          have : 0 ≤ Real.negMulLog ((p b).toReal) := Real.negMulLog_nonneg hb0 hb1
          simpa [hb] using this
      -- apply `le_tsum` to pick out the `a'` term
      have h_nonneg' :
          ∀ j : α, j ≠ a' →
            0 ≤ (if j = a then 0 else Real.negMulLog ((p j).toReal)) := by
        intro j hj
        exact h_nonneg j
      
      have hle :
          (if a' = a then 0 else Real.negMulLog ((p a').toReal))
            ≤ ∑' b : α, if b = a then 0 else Real.negMulLog ((p b).toReal) :=
        (Summable.le_tsum h_rest_summable a') h_nonneg'
      -- simplify the picked term using `a' ≠ a`
      simpa [ha'ne] using hle
    rw [entropy, (h_summable.tsum_eq_add_tsum_ite a)] at hE
    linarith [h1, h2, h_sum]
    
  · rintro ⟨a, rfl⟩
    simp only [entropy_pure]

lemma entropy_pos_of_not_pure (p : PMF α) [Finite α]
    (hp : ¬ ∃ a : α, p = PMF.pure a) :
    0 < entropy p := by
  have hnonneg : 0 ≤ entropy p := entropy_nonneg (α := α) p
  have hne : entropy p ≠ 0 := by
    intro h0
    exact hp ((entropy_eq_zero_iff p).1 h0)
  -- nonneg + ≠0 gives strict positivity in ℝ
  exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)


/-     (hp : ∀ a : α, p ≠ PMF.pure a) : -/
/-     0 < entropy p := by -/
/-   apply entropy_pos_of_not_pure (α := α) p -/
/-   intro h -/
/-   rcases h with ⟨a, rfl⟩ -/
/-   exact hp a rfl -/

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
  -- We compute: - (1/2) * log(1/2) - (1/2) * log(1/2) = - log(1/2) = log 2
  have h1 : Real.negMulLog ((2⁻¹ : ENNReal).toReal) = Real.log 2 / 2 := by
    simp only [Real.negMulLog, ENNReal.toReal_inv, ENNReal.toReal_ofNat, 
               Real.log_inv, mul_neg, neg_mul, neg_neg]
    ring_nf
  have h2 : (fun a : ℕ => 
      Real.negMulLog (ENNReal.toReal (if a = 0 ∨ a = 1 then (2⁻¹ : ENNReal) else 0)))
      = (fun a : ℕ => (if a = 0 then Real.log 2 / 2 else 0) + 
                      (if a = 1 then Real.log 2 / 2 else 0)) := by
    funext a
    aesop
  simp [h2]
  have hsumm1 : HasSum (fun (n : ℕ) => (if n = 0 then Real.log 2 / 2 else 0)) (Real.log 2 / 2) := by
    apply hasSum_ite_eq 0
  have hsumm2 : HasSum (fun (n : ℕ) => (if n = 1 then Real.log 2 / 2 else 0)) (Real.log 2 / 2) := by
    apply hasSum_ite_eq 1
  simp only [Summable.tsum_add (HasSum.summable hsumm1) (HasSum.summable hsumm2), 
             tsum_ite_eq, add_halves]

end InformationTheory

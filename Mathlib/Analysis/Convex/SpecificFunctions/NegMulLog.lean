import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Entropy function

The purpose of this file is to record basic analytic properties of the function
$$h(x) = - x * \log x$$ on the unit interval, for use in the theory of Shannon entropy.

## Main results

* `sum_negMulLog_le`: a Jensen inequality for `negMulLog`
* `sum_negMulLog_eq`: the equality case of this inequality

-/

open scoped ENNReal NNReal Topology BigOperators

namespace Real
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {p : ι → ℝ}

/-- Jensen's inequality for the entropy function. -/
lemma sum_negMulLog_le (h₀ : ∀ i ∈ s, 0 ≤ w i) (h₁ : ∑ i in s, w i = 1) (hmem : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i in s, w i * negMulLog (p i) ≤ negMulLog (∑ i in s, w i * p i) :=
  concaveOn_negMulLog.le_map_sum h₀ h₁ hmem

/-- The strict Jensen inequality for the entropy function. -/
lemma sum_negMulLog_lt (h₀ : ∀ i ∈ s, 0 < w i) (h₁ : ∑ i in s, w i = 1) (hmem : ∀ i ∈ s, 0 ≤ p i)
    (hp : ∃ j ∈ s, ∃ k ∈ s, p j ≠ p k) :
    ∑ i in s, w i * negMulLog (p i) < negMulLog (∑ i in s, w i * p i) :=
  strictConcaveOn_negMulLog.lt_map_sum h₀ h₁ hmem hp

/-- The equality case of Jensen's inequality for the entropy function. -/
lemma sum_negMulLog_eq_iff (h₀ : ∀ i ∈ s, 0 < w i) (h₁ : ∑ i in s, w i = 1)
    (hmem : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i in s, w i * negMulLog (p i) = negMulLog (∑ i in s, w i * p i) ↔
      ∀ j ∈ s, p j = ∑ i in s, w i * p i :=
  eq_comm.trans $ strictConcaveOn_negMulLog.map_sum_eq_iff h₀ h₁ hmem

/-- The equality case of Jensen's inequality for the entropy function. -/
lemma sum_negMulLog_eq_iff' (h₀ : ∀ i ∈ s, 0 ≤ w i) (h₁ : ∑ i in s, w i = 1)
    (hmem : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i in s, w i * negMulLog (p i) = negMulLog (∑ i in s, w i * p i) ↔
      ∀ j ∈ s, w j ≠ 0 → p j = ∑ i in s, w i * p i :=
  eq_comm.trans $ strictConcaveOn_negMulLog.map_sum_eq_iff' h₀ h₁ hmem

end Real

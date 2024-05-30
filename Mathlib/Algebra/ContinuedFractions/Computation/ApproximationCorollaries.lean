/-
Copyright (c) 2021 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.EvalEquiv
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Order.LeftRightNhds

#align_import algebra.continued_fractions.computation.approximation_corollaries from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Corollaries From Approximation Lemmas (`Algebra.ContinuedFractions.Computation.Approximations`)

## Summary

We show that the generalized_continued_fraction given by `GeneralizedContinuedFraction.of` in fact
is a (regular) continued fraction. Using the equivalence of the convergents computations
(`GeneralizedContinuedFraction.convergents` and `GeneralizedContinuedFraction.convergents'`) for
continued fractions (see `Algebra.ContinuedFractions.ConvergentsEquiv`), it follows that the
convergents computations for `GeneralizedContinuedFraction.of` are equivalent.

Moreover, we show the convergence of the continued fractions computations, that is
`(GeneralizedContinuedFraction.of v).convergents` indeed computes `v` in the limit.

## Main Theorems

- `GeneralizedContinuedFraction.of_convergents_eq_convergents'` shows that the convergents
  computations for `GeneralizedContinuedFraction.of` are equivalent.
- `GeneralizedContinuedFraction.of_convergence` shows that
  `(GeneralizedContinuedFraction.of v).convergents` converges to `v`.

## Tags

convergence, fractions
-/


variable {K : Type*} (v : K) [LinearOrderedField K] [FloorRing K]

open CF (of)

namespace CF

#noalign generalized_continued_fraction.of_convergents_eq_convergents'

#noalign generalized_continued_fraction.convergents_succ

section Convergence

/-!
### Convergence

We next show that `(GeneralizedContinuedFraction.of v).convergents v` converges to `v`.
-/


variable [Archimedean K]

open Nat

theorem of_convergence_epsilon :
    ∀ ε > (0 : K), ∃ N : ℕ, ∀ n ≥ N, |v - (of v).convergents n| < ε := by
  intro ε ε_pos
  -- use the archimedean property to obtian a suitable N
  rcases (exists_nat_gt ε⁻¹ : ∃ N' : ℕ, ε⁻¹ < N') with ⟨N', inv_ε_lt_N'⟩
  let N := max N' 5
  -- set minimum to 5 to have N ≤ fib N work
  exists N
  intro n n_ge_N
  cases' Decidable.em ((of v).s.TerminatedAt n) with terminatedAt_n not_terminatedAt_n
  · rw [of_terminatedAt_iff_fractParts_terminatedAt] at terminatedAt_n
    simp [← fractParts_representation_of_eq_none terminatedAt_n, ε_pos]
  · refine lt_of_le_of_lt (abs_sub_convergents_le not_terminatedAt_n) ?_
    rw [inv_lt _ ε_pos]
    · refine lt_of_lt_of_le inv_ε_lt_N' ?_
      norm_cast; rw [PNat.mul_coe]
      refine le_trans (le_max_left N' 5) (le_trans n_ge_N ?_)
      refine le_trans (le_fib_self (le_trans (le_max_right N' 5) n_ge_N)) ?_
      refine le_trans fib_le_fib_succ (le_trans (fib (n + 1)).le_mul_self
        (le_trans (Nat.mul_le_mul_left (fib (n + 1)) fib_le_fib_succ) ?_))
      apply Nat.mul_le_mul
      · convert ((of v).take n).succ_length_fib_le_denom; symm
        suffices hv : ∀ m, ((of v).s.take n).get? m = none ↔ n ≤ m by
          simp [- Seq'.get?_take] at hv
          apply eq_of_forall_ge_iff hv
        simp [Seq'.get?_take]
        conv =>
          enter [m, 1, hm]
          tactic =>
            apply eq_false
            refine mt (Seq'.le_stable _ ?_) not_terminatedAt_n
            nlinarith
        simp [imp_false]
      · convert ((of v).take (n + 1)).succ_length_fib_le_denom; symm
        suffices hv : ∀ m, ((of v).s.take (n + 1)).get? m = none ↔ n + 1 ≤ m by
          simp [- Seq'.get?_take] at hv
          apply eq_of_forall_ge_iff hv
        simp [Seq'.get?_take]
        conv =>
          enter [m, 1, hm]
          tactic =>
            apply eq_false
            refine mt (Seq'.le_stable _ ?_) not_terminatedAt_n
            nlinarith
        simp [imp_false]
    · simp
#align generalized_continued_fraction.of_convergence_epsilon CF.of_convergence_epsilon

theorem of_convergence [TopologicalSpace K] [OrderTopology K] :
    Filter.Tendsto (of v).convergents Filter.atTop <| nhds v := by
  simpa [LinearOrderedAddCommGroup.tendsto_nhds, abs_sub_comm] using of_convergence_epsilon v
#align generalized_continued_fraction.of_convergence CF.of_convergence

end Convergence

end CF

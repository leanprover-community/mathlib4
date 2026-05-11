/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Prime.Basic

import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.SylvesterSchur.Bridge
import Mathlib.NumberTheory.SylvesterSchur.ErdosKey

/-!
# Sylvester-Schur theorem

This file exposes the `Nat.ascFactorial` form of the Sylvester-Schur theorem, proved
through a private consecutive-block induction.

## Main statements

* `Nat.exists_prime_gt_and_dvd_ascFactorial`: among `k` consecutive natural numbers
  starting at `n`, where `0 < k < n`, one term has a prime divisor greater than `k`.

## Implementation notes

The private induction uses Bertrand's postulate for the base block and the Erdős
binomial-coefficient argument in `Mathlib.NumberTheory.SylvesterSchur.ErdosKey` for the
induction step.

## References

The proof follows Erdős's proof of the Sylvester-Schur theorem.

## Tags

Sylvester-Schur theorem, prime divisors, binomial coefficients, ascending factorials
-/

namespace Nat

open SylvesterSchur

/-! ### Final induction -/

/- Internal induction proving the consecutive-integer form.

The base block starts at `n + 1` and is Bertrand's postulate.  The induction step shifts
the witness from the previous block unless it belongs to the lost left endpoint; in that
case the Erdős binomial-coefficient lemma supplies a new large prime in the current block. -/
private lemma sylvester_schur_core {n k : ℕ} (hn : 1 ≤ n) (hk : n < k) :
    ∃ i < n, ∃ p, p.Prime ∧ n < p ∧ p ∣ k + i := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hkn : k = n + 1
    · subst hkn
      obtain ⟨p, hp_prime, hp_gt, hp_le⟩ :=
        Nat.exists_prime_lt_and_le_two_mul n (by omega)
      refine ⟨p - (n + 1), by omega, p, hp_prime, hp_gt, ?_⟩
      rw [show n + 1 + (p - (n + 1)) = p by omega]
    have hkm1_gt : n < k - 1 := by omega
    have hkm1_lt : k - 1 < k := Nat.sub_lt (by omega) Nat.one_pos
    obtain ⟨j, hj_lt, q, hq_prime, hq_gt, hq_dvd⟩ := ih (k - 1) hkm1_lt hkm1_gt
    by_cases hj0 : j = 0
    · -- The induction witness is on the lost left endpoint, so use the binomial lemma.
      obtain ⟨p, hp_prime, hp_gt, hp_dvd⟩ :=
        SylvesterSchur.Internal.erdos_choose_prime_factor_gt n hn k hk
      obtain ⟨i, hi_lt, hi_dvd⟩ :=
        exists_dvd_consecutive_of_prime_dvd_choose n k p hp_prime hp_gt hp_dvd
      exact ⟨i, hi_lt, p, hp_prime, hp_gt, hi_dvd⟩
    · refine ⟨j - 1, by omega, q, hq_prime, hq_gt, ?_⟩
      have heq : k - 1 + j = k + (j - 1) := by omega
      rwa [heq] at hq_dvd

end Nat

@[expose] public section

namespace Nat

/-- Sylvester-Schur theorem in Mathlib's `Nat.ascFactorial` API form. -/
theorem exists_prime_gt_and_dvd_ascFactorial {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.ascFactorial k := by
  obtain ⟨i, hi_lt, p, hp_prime, hp_gt, hp_dvd⟩ :=
    sylvester_schur_core (n := k) (k := n) hk hkn
  refine ⟨p, hp_prime, hp_gt, ?_⟩
  rw [Nat.ascFactorial_eq_prod_range]
  exact hp_dvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi_lt))

end Nat

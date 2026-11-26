/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.PadicValNat

/-!
# Perfect powers detected by valuations

A natural number whose `p`-adic valuation at every prime is divisible by `k`
is a perfect `k`-th power: the root is assembled prime by prime from the
factorization of `n`, dividing each exponent by `k`.
-/

public section

namespace Nat

/-- If the `p`-adic valuation of `n` is divisible by `k` at every prime `p`,
then `n` is a perfect `k`-th power. -/
theorem exists_pow_of_dvd_padicValNat {n k : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Nat.Prime p → k ∣ padicValNat p n) :
    ∃ m, n = m ^ k := by
  let m := n.factorization.prod fun p e => p ^ (e / k)
  refine ⟨m, ?_⟩
  have hself : n.factorization.prod (· ^ ·) = n :=
    Nat.prod_factorization_pow_eq_self hn
  apply Eq.symm
  calc
    m ^ k
        = (n.factorization.support.prod fun p =>
            p ^ (n.factorization p / k)) ^ k := by
          simp only [m, Finsupp.prod]
    _ = n.factorization.support.prod fun p =>
            (p ^ (n.factorization p / k)) ^ k := by
          rw [Finset.prod_pow]
    _ = n.factorization.support.prod fun p =>
            p ^ n.factorization p := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          have hpP : p.Prime :=
            Nat.prime_of_mem_primeFactors (by
              simpa [Nat.support_factorization] using hp)
          have hk : k ∣ n.factorization p := by
            rw [Nat.factorization_def n hpP, ← Nat.padicValNat_def]
            exact h p hpP
          rw [← pow_mul, Nat.mul_comm, Nat.mul_div_cancel' hk]
    _ = n := by
          simpa [Finsupp.prod] using hself

end Nat

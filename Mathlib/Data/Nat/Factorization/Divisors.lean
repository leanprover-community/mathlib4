/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.Divisors

/-!
# Results about divisors and factorizations
-/

@[expose] public section

open Finsupp

namespace Nat

theorem divisors_eq_prod_pow_le_factorization {n : ℕ} (hn : n ≠ 0) :
    n.divisors = { f.prod (· ^ ·) | f ≤ n.factorization } := by
  refine Set.ext fun k ↦ ⟨fun h ↦ ?_, fun ⟨f, hle, h⟩ ↦ mem_divisors.mpr ⟨?_, hn⟩⟩
  · have hdvd := dvd_of_mem_divisors h
    have hk := ne_zero_of_dvd_ne_zero hn hdvd
    exact ⟨_, factorization_le_iff_dvd hk hn |>.mpr hdvd, factorization_prod_pow_eq_self hk⟩
  · rw [← h, ← factorization_prod_pow_eq_self hn]
    exact prod_dvd_prod_of_subset_of_dvd (support_mono hle) fun p _ ↦ Nat.pow_dvd_pow p <| hle p

theorem properDivisors_eq_prod_pow_lt_factorization {n : ℕ} :
    n.properDivisors = { f.prod (· ^ ·) | f < n.factorization } := by
  by_cases hn : n = 0
  · simp [hn]
  refine Set.ext fun k ↦ ⟨fun h ↦ ?_, fun ⟨f, hlt, h⟩ ↦ ?_⟩
  · have ⟨hdvd, hlt⟩ := mem_properDivisors.mp h
    have hk := ne_zero_of_dvd_ne_zero hn hdvd
    refine ⟨_, ?_, factorization_prod_pow_eq_self hk⟩
    apply lt_of_le_of_ne <| factorization_le_iff_dvd hk hn |>.mpr hdvd
    exact mt (Nat.eq_of_factorization_eq' hk hn) hlt.ne
  · have : k ∣ n := by
      rw [← h, ← factorization_prod_pow_eq_self hn]
      apply prod_dvd_prod_of_subset_of_dvd <| support_mono hlt.le
      exact fun p _ ↦ Nat.pow_dvd_pow p <| hlt.le p
    refine mem_properDivisors.mpr ⟨this, lt_of_le_of_ne (le_of_dvd (Nat.pos_of_ne_zero hn) this) ?_⟩
    suffices k.factorization = f from (this ▸ hlt.ne <| congrArg _ ·)
    refine h ▸ prod_pow_factorization_eq_self fun _ hp ↦ ?_
    exact prime_of_mem_primeFactors <| support_mono hlt.le hp

end Nat

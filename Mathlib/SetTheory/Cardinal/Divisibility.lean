/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Tactic.WLOG

/-!
# Cardinal Divisibility

We show basic results about divisibility in the cardinal numbers. This relation can be characterised
in the following simple way: if `a` and `b` are both less than `ℵ₀`, then `a ∣ b` iff they are
divisible as natural numbers. If `b` is greater than `ℵ₀`, then `a ∣ b` iff `a ≤ b`. This
furthermore shows that all infinite cardinals are prime; recall that `a * b = max a b` if
`ℵ₀ ≤ a * b`; therefore `a ∣ b * c = a ∣ max b c` and therefore clearly either `a ∣ b` or `a ∣ c`.
Note furthermore that no infinite cardinal is irreducible
(`Cardinal.not_irreducible_of_aleph0_le`), showing that the cardinal numbers do not form a
cancellative `CommMonoidWithZero`.

## Main results

* `Cardinal.prime_of_aleph0_le`: a `Cardinal` is prime if it is infinite.
* `Cardinal.is_prime_iff`: a `Cardinal` is prime iff it is infinite or a prime natural number.
* `Cardinal.isPrimePow_iff`: a `Cardinal` is a prime power iff it is infinite or a natural number
  which is itself a prime power.
-/

public section

namespace Cardinal

universe u

variable {a b : Cardinal.{u}} {n m : ℕ}

instance : Unique Cardinal.{u}ˣ where
  default := 1
  uniq := by
    intro ⟨a, b, h, _⟩
    rw [← Units.val_eq_one]
    apply ((mul_eq_one_iff_of_one_le _ _).1 h).1 <;>
      grind [Cardinal.one_le_iff_ne_zero]

@[deprecated (since := "2026-09-20")] alias isUnit_iff := isUnit_iff_eq_one

@[simp]
theorem prime_of_aleph0_le (ha : ℵ₀ ≤ a) : Prime a := by
  refine ⟨(aleph0_pos.trans_le ha).ne', ?_, fun b c hbc => ?_⟩
  · rw [isUnit_iff_eq_one]
    exact (one_lt_aleph0.trans_le ha).ne'
  rcases eq_or_ne (b * c) 0 with hz | hz
  · rcases mul_eq_zero.mp hz with (rfl | rfl) <;> simp
  rw [mul_eq_max' (ha.trans (le_of_dvd hz hbc)), max_def] at hbc
  split_ifs at hbc <;> tauto

theorem not_irreducible_of_aleph0_le (ha : ℵ₀ ≤ a) : ¬Irreducible a := by
  rw [irreducible_iff, not_and_or]
  refine .inr fun h => ?_
  simpa [mul_aleph0_eq ha, (one_lt_aleph0.trans_le ha).ne'] using @h a ℵ₀

@[simp, norm_cast]
theorem prime_natCast_iff : Prime (n : Cardinal) ↔ n.Prime := by
  simp only [Prime, Nat.prime_iff]
  refine and_congr (by simp) (and_congr ?_ ⟨fun h b c hbc => ?_, fun h b c hbc => ?_⟩)
  · simp
  · exact_mod_cast h b c (mod_cast hbc)
  rcases lt_or_ge (b * c) ℵ₀ with h' | h'
  · rcases mul_lt_aleph0_iff.mp h' with (rfl | rfl | ⟨hb, hc⟩)
    · simp
    · simp
    lift b to ℕ using hb
    lift c to ℕ using hc
    exact mod_cast h b c (mod_cast hbc)
  rcases aleph0_le_mul_iff.mp h' with ⟨hb, hc, hℵ₀⟩
  have hn : (n : Cardinal) ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff, mul_eq_zero] at hbc
    cases hbc <;> contradiction
  wlog hℵ₀b : ℵ₀ ≤ b
  apply (this h c b _ _ hc hb hℵ₀.symm hn (hℵ₀.resolve_left hℵ₀b)).symm <;> try assumption
  · rwa [mul_comm] at hbc
  · rwa [mul_comm] at h'
  · exact Or.inl (dvd_of_le_of_aleph0_le hn (natCast_lt_aleph0.le.trans hℵ₀b) hℵ₀b)

@[deprecated (since := "2026-09-20")] alias nat_is_prime_iff := prime_natCast_iff

theorem prime_iff {a : Cardinal} : Prime a ↔ ℵ₀ ≤ a ∨ ∃ p : ℕ, a = p ∧ p.Prime := by
  rcases le_or_gt ℵ₀ a with h | h
  · simp [h]
  lift a to ℕ using id h
  simp [not_le.mpr h]

@[deprecated (since := "2026-09-20")] alias is_prime_iff := prime_iff

theorem isPrimePow_iff {a : Cardinal} : IsPrimePow a ↔ ℵ₀ ≤ a ∨ ∃ n : ℕ, a = n ∧ IsPrimePow n := by
  by_cases h : ℵ₀ ≤ a
  · simp [h, (prime_of_aleph0_le h).isPrimePow]
  simp only [h, false_or, isPrimePow_nat_iff]
  lift a to ℕ using not_le.mp h
  rw [isPrimePow_def]
  refine
    ⟨?_, fun ⟨n, han, p, k, hp, hk, h⟩ =>
          ⟨p, k, prime_natCast_iff.2 hp, hk, by rw [han]; exact mod_cast h⟩⟩
  rintro ⟨p, k, hp, hk, hpk⟩
  have key : p ^ (1 : Cardinal) ≤ ↑a := by
    rw [← hpk]; apply power_le_power_left hp.ne_zero; exact mod_cast hk
  rw [power_one] at key
  lift p to ℕ using key.trans_lt natCast_lt_aleph0
  exact ⟨a, rfl, p, k, prime_natCast_iff.mp hp, hk, mod_cast hpk⟩

end Cardinal

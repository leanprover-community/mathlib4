/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Init
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

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

@[expose] public section


namespace Cardinal

universe u

variable {a b : Cardinal.{u}} {n m : ℕ}

/-- Alias of `isUnit_iff_eq_one` for discoverability. -/
theorem isUnit_iff : IsUnit a ↔ a = 1 := by
  refine
    ⟨fun h => ?_, by
      rintro rfl
      exact isUnit_one⟩
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact (not_isUnit_zero h).elim
  rw [isUnit_iff_forall_dvd] at h
  obtain ⟨t, ht⟩ := h 1
  rw [eq_comm, mul_eq_one_iff_of_one_le] at ht
  · exact ht.1
  · exact Cardinal.one_le_iff_ne_zero.mpr ha
  · apply Cardinal.one_le_iff_ne_zero.mpr
    intro h
    rw [h, mul_zero] at ht
    exact zero_ne_one ht

instance : Unique Cardinal.{u}ˣ where
  default := 1
  uniq a := Units.val_eq_one.mp <| isUnit_iff.mp a.isUnit

theorem le_of_dvd {a b : Cardinal} (hb : b ≠ 0) (hdiv : a ∣ b) : a ≤ b := by
  obtain ⟨b, rfl⟩ := hdiv
  apply le_mul_right
  simp_all

theorem dvd_of_le_of_aleph0_le (ha : a ≠ 0) (h : a ≤ b) (hb : ℵ₀ ≤ b) : a ∣ b :=
  ⟨b, (mul_eq_right hb h ha).symm⟩

@[simp]
theorem prime_of_aleph0_le (ha : ℵ₀ ≤ a) : Prime a := by
  refine ⟨(aleph0_pos.trans_le ha).ne', ?_, fun b c hbc => ?_⟩
  · rw [isUnit_iff]
    exact (one_lt_aleph0.trans_le ha).ne'
  rcases eq_or_ne (b * c) 0 with hz | hz
  · rcases mul_eq_zero.mp hz with (rfl | rfl) <;> simp
  wlog h : c ≤ b
  · cases le_total c b <;> [solve_by_elim; rw [or_comm]]
    apply_assumption
    assumption'
    all_goals rwa [mul_comm]
  left
  have habc := le_of_dvd hz hbc
  rwa [mul_eq_max' <| ha.trans <| habc, max_def', if_pos h] at hbc

theorem not_irreducible_of_aleph0_le (ha : ℵ₀ ≤ a) : ¬Irreducible a := by
  rw [irreducible_iff, not_and_or]
  refine Or.inr fun h => ?_
  simpa [mul_aleph0_eq ha, isUnit_iff, (one_lt_aleph0.trans_le ha).ne', one_lt_aleph0.ne'] using
    @h a ℵ₀

@[simp, norm_cast]
theorem nat_coe_dvd_iff : (n : Cardinal) ∣ m ↔ n ∣ m := by
  refine ⟨?_, fun ⟨h, ht⟩ => ⟨h, mod_cast ht⟩⟩
  rintro ⟨k, hk⟩
  have : ↑m < ℵ₀ := natCast_lt_aleph0
  rw [hk, mul_lt_aleph0_iff] at this
  rcases this with (h | h | ⟨-, hk'⟩)
  iterate 2 simp only [h, mul_zero, zero_mul, Nat.cast_eq_zero] at hk; simp [hk]
  lift k to ℕ using hk'
  exact ⟨k, mod_cast hk⟩

@[simp]
theorem nat_is_prime_iff : Prime (n : Cardinal) ↔ n.Prime := by
  simp only [Prime, Nat.prime_iff]
  refine and_congr (by simp) (and_congr ?_ ⟨fun h b c hbc => ?_, fun h b c hbc => ?_⟩)
  · simp only [isUnit_iff, Nat.isUnit_iff]
    exact mod_cast Iff.rfl
  · exact mod_cast h b c (mod_cast hbc)
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

theorem is_prime_iff {a : Cardinal} : Prime a ↔ ℵ₀ ≤ a ∨ ∃ p : ℕ, a = p ∧ p.Prime := by
  rcases le_or_gt ℵ₀ a with h | h
  · simp [h]
  lift a to ℕ using id h
  simp [not_le.mpr h]

theorem isPrimePow_iff {a : Cardinal} : IsPrimePow a ↔ ℵ₀ ≤ a ∨ ∃ n : ℕ, a = n ∧ IsPrimePow n := by
  by_cases h : ℵ₀ ≤ a
  · simp [h, (prime_of_aleph0_le h).isPrimePow]
  simp only [h, false_or, isPrimePow_nat_iff]
  lift a to ℕ using not_le.mp h
  rw [isPrimePow_def]
  refine
    ⟨?_, fun ⟨n, han, p, k, hp, hk, h⟩ =>
          ⟨p, k, nat_is_prime_iff.2 hp, hk, by rw [han]; exact mod_cast h⟩⟩
  rintro ⟨p, k, hp, hk, hpk⟩
  have key : p ^ (1 : Cardinal) ≤ ↑a := by
    rw [← hpk]; apply power_le_power_left hp.ne_zero; exact mod_cast hk
  rw [power_one] at key
  lift p to ℕ using key.trans_lt natCast_lt_aleph0
  exact ⟨a, rfl, p, k, nat_is_prime_iff.mp hp, hk, mod_cast hpk⟩

end Cardinal

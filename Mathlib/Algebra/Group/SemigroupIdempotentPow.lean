/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.PNatPowAssoc
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Logic.Denumerable
public import Mathlib.Tactic.PNatToNat
public import Mathlib.Tactic.Ring.RingNF

/-!
# Idempotent Elements in Finite Semigroups

This file defines properties related to idempotent elements in finite semigroups and monoids.

## Main theorems

* `Semigroup.exists_idempotent_ppow` - In finite semigroups,
  `∀ x, ∃ (m : ℕ+), IsIdempotentElem (x ^ m)`
* `Monoid.exists_idempotent_pow` - `∃ (n : ℕ), IsIdempotentElem (x ^ n) ∧ n ≠ 0` in finite monoids.
* `Monoid.exists_pow_sandwich_eq_self` - In finite monoids, if `a = x * a * y`, then there exists
 positive powers `n₁` and `n₂` such that `x ^ n₁ * a = a` and `a * y ^ n₂ = a`.
-/

public section

namespace Semigroup

variable {S : Type*} [Semigroup S] [Pow S ℕ+] [PNatPowAssoc S]

/-- Idempotent elements are stable under positive powers. -/
lemma ppow_succ_eq {x : S} (n : ℕ+) (h_idem : IsIdempotentElem x) : x ^ n = x := by
  induction n with
  | one => rw [ppow_one]
  | succ n' ih => rw [ppow_succ, ih, h_idem]

/-- In a finite semigroup, powers of any element eventually repeat. -/
lemma exists_repeating_ppow [Finite S] (x : S) : ∃ (m n : ℕ+), x ^ m * x ^ n = x ^ m := by
  obtain ⟨o, p, hop, heq⟩ : ∃ o p : ℕ+, o ≠ p ∧ x ^ o = x ^ p := by
    apply Finite.exists_ne_map_eq_of_infinite
  simp_all only [ne_eq, ← ppow_add]
  rcases (lt_or_gt_of_ne hop) with (o_lt_p | p_lt_o)
  · use o, p - o
    rw [heq]
    congr
    pnat_to_nat; omega
  · use p, o - p
    rw [← heq]
    congr
    pnat_to_nat; omega

/-- If two powers of an element are both idempotent, then they are equal. -/
theorem ppow_idempotent_unique {x : S} {m n : ℕ+}
    (hm : IsIdempotentElem (x ^ m)) (hn : IsIdempotentElem (x ^ n)) : x ^ m = x ^ n := by
  rw [← ppow_succ_eq m hn, ← ppow_succ_eq n hm, ← ppow_mul, ← ppow_mul']

/-- In a finite semigroup, every element has an idempotent power. -/
theorem exists_idempotent_ppow [Finite S] (x : S) : ∃ (m : ℕ+), IsIdempotentElem (x ^ m) := by
  -- `n` is the length of the pre-period/tail, and `loop_size` is the length of the cycle.
  obtain ⟨n, loop_size, loop_eq⟩ := exists_repeating_ppow x
  -- Once powers of `x` enter the cycle,
  -- adding further multiples of `loop_size` to the exponent doesn't change the result.
  have loop : ∀ (loop_count start : ℕ+),
      n < start → x ^ (start + loop_count * loop_size) = x ^ start := by
    intro loop_count
    induction loop_count with
    | one =>
      intro start n_lt_start
      have exists_eq_sum : start = n + (start - n) := by
         pnat_to_nat; omega
      rw [exists_eq_sum]
      simp only [one_mul, ppow_add]
      rw [ppow_mul_comm, mul_assoc, loop_eq]
    | succ loop_count' ih =>
      intro start n_lt_start
      have exists_eq_sum : start = n + (start - n) := by
         pnat_to_nat; omega
      rw [exists_eq_sum] at n_lt_start ⊢
      specialize ih (start - n + n)
      rw [add_comm] at n_lt_start
      apply ih at n_lt_start
      rw [add_one_mul, add_comm n, ← add_assoc, ppow_add, n_lt_start,ppow_add, mul_assoc, loop_eq]
  -- We choose `2 * n * loop_size` as the exponent because it is
  -- beyond the pre-period `n` and is a multiple of `loop_size`.
  use 2 * n * loop_size
  unfold IsIdempotentElem
  specialize loop (2 * n) (2 * n * loop_size)
  simp_all only [ppow_add]
  apply loop
  have n_lt_2nm (n m : ℕ+) : n < 2 * n * m := by
    induction m with
    | one => pnat_to_nat; omega
    | succ m ih => pnat_to_nat; ring_nf; omega
  apply n_lt_2nm

end Semigroup

namespace Monoid

variable {M : Type*} [Monoid M]

/-- Idempotent elements are stable under positive powers in monoids. -/
lemma pow_succ_eq {x : M} {n : ℕ} (h_idem : IsIdempotentElem x) :
    x ^ (n + 1) = x := by
  induction n with
  | zero => simp_all
  | succ n' ih => rw [pow_succ, ih, h_idem]

variable [Pow M ℕ+] [PNatPowAssoc M]

/-- Every element in a finite monoid has a nonzero idempotent power. -/
theorem exists_idempotent_pow [Finite M] (x : M) :
    ∃ (n : ℕ), IsIdempotentElem (x ^ n) ∧ n ≠ 0 := by
  obtain ⟨m, hm⟩ := Semigroup.exists_idempotent_ppow x
  use m; simp_all only [IsIdempotentElem]
  constructor
  · rwa [← ppow_eq_pow]
  · simp [PNat.ne_zero]

/-- In finite monoids, if `x * a * y = a`, then `x` has a positive power that left-cancels,
and `y` has a positive power that right-cancels. -/
theorem exists_pow_sandwich_eq_self [Finite M] {x a y : M} (h : x * a * y = a) :
    ∃ n₁ n₂ : ℕ, n₁ ≠ 0 ∧ n₂ ≠ 0 ∧ x ^ n₁ * a = a ∧ a * y ^ n₂ = a := by
  have loop : ∀ k : ℕ, x ^ k * a * y ^ k = a := by
    intro k; induction k with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ']
      rw [← mul_assoc, mul_assoc _ a, mul_assoc _ x, ← mul_assoc x a y, h, ih]
  have ⟨n₁, ⟨hn₁, hneq₁⟩⟩ := Monoid.exists_idempotent_pow x
  have ⟨n₂, ⟨hn₂, hneq₂⟩⟩ := Monoid.exists_idempotent_pow y
  use n₁, n₂
  constructor
  · exact hneq₁
  constructor
  · exact hneq₂
  constructor
  · rw [← (loop n₁), ← mul_assoc, ← mul_assoc, hn₁]
  · rw [← (loop n₂), mul_assoc, hn₂]

end Monoid

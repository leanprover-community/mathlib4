/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Emirhan Duysak, Adem Alp Gök, Junyan Xu
-/
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Order.BooleanAlgebra.Set

/-!
# The integers form a linear ordered ring

This file contains:
* instances on `ℤ`. The stronger one is `Int.instLinearOrderedCommRing`.
* basic lemmas about integers that involve order properties.

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

open Function Nat

namespace Int

instance instZeroLEOneClass : ZeroLEOneClass ℤ := ⟨Int.zero_lt_one.le⟩
instance instIsStrictOrderedRing : IsStrictOrderedRing ℤ := .of_mul_pos @Int.mul_pos

/-! ### Miscellaneous lemmas -/

lemma isCompl_even_odd : IsCompl { n : ℤ | Even n } { n | Odd n } := by
  simp [← not_even_iff_odd, ← Set.compl_setOf, isCompl_compl]

@[simp]
lemma _root_.Nat.cast_natAbs {α : Type*} [AddGroupWithOne α] (n : ℤ) : (n.natAbs : α) = |n| := by
  rw [← natCast_natAbs, Int.cast_natCast]

lemma two_le_iff_pos_of_even {m : ℤ} (even : Even m) : 2 ≤ m ↔ 0 < m :=
  le_iff_pos_of_dvd (by decide) even.two_dvd

lemma add_two_le_iff_lt_of_even_sub {m n : ℤ} (even : Even (n - m)) : m + 2 ≤ n ↔ m < n := by
  grind

end Int

/-- If the gcd of two natural numbers `p` and `q` divides a third natural number `n`,
and if `n` is at least `(p - 1) * (q - 1)`, then `n` can be represented as an `ℕ`-linear
combination of `p` and `q`.

TODO: show that if `p.gcd q = 1` and `0 ≤ n ≤ (p - 1) * (q - 1) - 1 = N`, then `n` is
representable iff `N - n` is not. In particular `N` is not representable, solving the
coin problem for two coins: https://en.wikipedia.org/wiki/Coin_problem#n_=_2. -/
theorem Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le (p q n : ℕ) (dvd : p.gcd q ∣ n)
    (le : p.pred * q.pred ≤ n) : ∃ a b : ℕ, a * p + b * q = n := by
  obtain _ | p := p
  · have ⟨b, eq⟩ := q.gcd_zero_left ▸ dvd
    exact ⟨0, b, by simpa [mul_comm, eq_comm] using eq⟩
  obtain _ | q := q
  · have ⟨a, eq⟩ := p.gcd_zero_right ▸ dvd
    exact ⟨a, 0, by simpa [mul_comm, eq_comm] using eq⟩
  rw [← Int.gcd_natCast_natCast, Int.gcd_dvd_iff] at dvd
  have ⟨a_n, b_n, eq⟩ := dvd
  let a := a_n % q.succ
  let b := b_n + a_n / q.succ * p.succ
  refine ⟨a.toNat, b.toNat, Nat.cast_injective (R := ℤ) ?_⟩
  have : a * p.succ + b * q.succ = n := by rw [add_mul, ← add_assoc,
    add_right_comm, mul_right_comm, ← add_mul, Int.emod_add_ediv_mul, eq, mul_comm, mul_comm b_n]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Int.natCast_toNat_eq_self.mpr
    (Int.emod_nonneg _ <| by omega), Int.natCast_toNat_eq_self.mpr, this]
  -- show b ≥ 0 by contradiction
  by_contra hb
  replace hb : b ≤ -1 := by omega
  apply lt_irrefl (n : ℤ)
  have ha := Int.emod_lt a_n (by omega : (q.succ : ℤ) ≠ 0)
  rw [p.pred_succ, q.pred_succ] at le
  calc n = a * p.succ + b * q.succ := this.symm
       _ ≤ q * p.succ + -1 * q.succ := by gcongr <;> omega
       _ = p * q - 1 := by simp_rw [Nat.cast_succ, mul_add, mul_comm]; omega
       _ ≤ n - 1 := by rwa [sub_le_sub_iff_right, ← Nat.cast_mul, Nat.cast_le]
       _ < n := by omega

/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Monoid

/-!
# Numbers are frequently ModEq to fixed numbers

In this file we prove that `m ≡ d [MOD n]` frequently as `m → ∞`.
-/


open Filter

namespace Nat

/-- Infinitely many natural numbers are equal to `d` mod `n`. -/
theorem frequently_modEq {n : ℕ} (h : n ≠ 0) (d : ℕ) : ∃ᶠ m in atTop, m ≡ d [MOD n] :=
  ((tendsto_add_atTop_nat d).comp (tendsto_id.nsmul_atTop h.bot_lt)).frequently <|
    Frequently.of_forall fun m => by simp [Nat.modEq_iff_dvd]

theorem frequently_mod_eq {d n : ℕ} (h : d < n) : ∃ᶠ m in atTop, m % n = d := by
  simpa only [Nat.ModEq, mod_eq_of_lt h] using frequently_modEq h.ne_bot d

theorem frequently_even : ∃ᶠ m : ℕ in atTop, Even m := by
  simpa only [even_iff] using frequently_mod_eq zero_lt_two

theorem frequently_odd : ∃ᶠ m : ℕ in atTop, Odd m := by
  simpa only [odd_iff] using frequently_mod_eq one_lt_two

end Nat

theorem Filter.nonneg_of_eventually_pow_nonneg {α : Type*}
    [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}
    (h : ∀ᶠ n in atTop, 0 ≤ a ^ (n : ℕ)) : 0 ≤ a :=
  let ⟨_n, ho, hn⟩ := (Nat.frequently_odd.and_eventually h).exists
  ho.pow_nonneg_iff.1 hn

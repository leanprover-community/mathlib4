/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Benjamin Davidson
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.Parity

#align_import data.nat.parity from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

/-!
# Parity of natural numbers

This file contains theorems about the `Even` and `Odd` predicates on the natural numbers.

## Tags

even, odd
-/


namespace Nat

variable {m n : ℕ}

@[simp]
theorem mod_two_ne_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by
  cases' mod_two_eq_zero_or_one n with h h <;> simp [h]
  -- ⊢ ¬n % 2 = 1 ↔ n % 2 = 0
                                               -- 🎉 no goals
                                               -- 🎉 no goals
#align nat.mod_two_ne_one Nat.mod_two_ne_one

@[simp]
theorem mod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  cases' mod_two_eq_zero_or_one n with h h <;> simp [h]
  -- ⊢ ¬n % 2 = 0 ↔ n % 2 = 1
                                               -- 🎉 no goals
                                               -- 🎉 no goals
#align nat.mod_two_ne_zero Nat.mod_two_ne_zero

theorem even_iff : Even n ↔ n % 2 = 0 :=
  ⟨fun ⟨m, hm⟩ => by simp [← two_mul, hm], fun h =>
                     -- 🎉 no goals
    ⟨n / 2, (mod_add_div n 2).symm.trans (by simp [← two_mul, h])⟩⟩
                                             -- 🎉 no goals
#align nat.even_iff Nat.even_iff

instance : DecidablePred (Even : ℕ → Prop) := fun _ => decidable_of_iff _ even_iff.symm

theorem odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨m, hm⟩ => by norm_num [hm, add_mod],
                     -- 🎉 no goals
    fun h => ⟨n / 2, (mod_add_div n 2).symm.trans (by rw [h, add_comm])⟩⟩
                                                      -- 🎉 no goals
#align nat.odd_iff Nat.odd_iff

instance : DecidablePred (Odd : ℕ → Prop) := fun _ => decidable_of_iff _ odd_iff.symm

theorem not_even_iff : ¬Even n ↔ n % 2 = 1 := by rw [even_iff, mod_two_ne_zero]
                                                 -- 🎉 no goals
#align nat.not_even_iff Nat.not_even_iff

theorem not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by rw [odd_iff, mod_two_ne_one]
                                               -- 🎉 no goals
#align nat.not_odd_iff Nat.not_odd_iff

theorem even_iff_not_odd : Even n ↔ ¬Odd n := by rw [not_odd_iff, even_iff]
                                                 -- 🎉 no goals
#align nat.even_iff_not_odd Nat.even_iff_not_odd

@[simp]
theorem odd_iff_not_even : Odd n ↔ ¬Even n := by rw [not_even_iff, odd_iff]
                                                 -- 🎉 no goals
#align nat.odd_iff_not_even Nat.odd_iff_not_even

theorem _root_.Odd.not_two_dvd_nat (h : Odd n) : ¬(2 ∣ n) := by
  rwa [← even_iff_two_dvd, ← odd_iff_not_even]
  -- 🎉 no goals

theorem isCompl_even_odd : IsCompl { n : ℕ | Even n } { n | Odd n } := by
  simp only [← Set.compl_setOf, isCompl_compl, odd_iff_not_even]
  -- 🎉 no goals
#align nat.is_compl_even_odd Nat.isCompl_even_odd

theorem even_xor_odd (n : ℕ) : Xor' (Even n) (Odd n) := by
  simp [Xor', odd_iff_not_even, Decidable.em (Even n)]
  -- 🎉 no goals
#align nat.even_xor_odd Nat.even_xor_odd

theorem even_or_odd (n : ℕ) : Even n ∨ Odd n :=
  (even_xor_odd n).or
#align nat.even_or_odd Nat.even_or_odd

theorem even_or_odd' (n : ℕ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [← two_mul, exists_or, Odd, Even] using even_or_odd n
  -- 🎉 no goals
#align nat.even_or_odd' Nat.even_or_odd'

theorem even_xor_odd' (n : ℕ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) := by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> use k
  -- ⊢ ∃ k_1, Xor' (k + k = 2 * k_1) (k + k = 2 * k_1 + 1)
                                                      -- ⊢ Xor' (k + k = 2 * k) (k + k = 2 * k + 1)
                                                      -- ⊢ Xor' (2 * k + 1 = 2 * k) (2 * k + 1 = 2 * k + 1)
  · simpa only [← two_mul, eq_self_iff_true, xor_true] using (succ_ne_self (2 * k)).symm
    -- 🎉 no goals
  · simpa only [xor_true, xor_comm] using (succ_ne_self _)
    -- 🎉 no goals
#align nat.even_xor_odd' Nat.even_xor_odd'

@[simp] theorem two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 :=
  even_iff_two_dvd.symm.not.trans not_even_iff
#align nat.two_dvd_ne_zero Nat.two_dvd_ne_zero

theorem mod_two_add_add_odd_mod_two (m : ℕ) {n : ℕ} (hn : Odd n) : m % 2 + (m + n) % 2 = 1 :=
  ((even_or_odd m).elim fun hm => by rw [even_iff.1 hm, odd_iff.1 (hm.add_odd hn)]) fun hm => by
                                     -- 🎉 no goals
    rw [odd_iff.1 hm, even_iff.1 (hm.add_odd hn)]
    -- 🎉 no goals
#align nat.mod_two_add_add_odd_mod_two Nat.mod_two_add_add_odd_mod_two

@[simp]
theorem mod_two_add_succ_mod_two (m : ℕ) : m % 2 + (m + 1) % 2 = 1 :=
  mod_two_add_add_odd_mod_two m odd_one
#align nat.mod_two_add_succ_mod_two Nat.mod_two_add_succ_mod_two

@[simp]
theorem succ_mod_two_add_mod_two (m : ℕ) : (m + 1) % 2 + m % 2 = 1 := by
  rw [add_comm, mod_two_add_succ_mod_two]
  -- 🎉 no goals
#align nat.succ_mod_two_add_mod_two Nat.succ_mod_two_add_mod_two

@[simp] theorem not_even_one : ¬Even 1 := odd_iff_not_even.1 odd_one
#align nat.not_even_one Nat.not_even_one

@[parity_simps]
theorem even_add : Even (m + n) ↔ (Even m ↔ Even n) := by
  cases' mod_two_eq_zero_or_one m with h₁ h₁ <;> cases' mod_two_eq_zero_or_one n with h₂ h₂ <;>
  -- ⊢ Even (m + n) ↔ (Even m ↔ Even n)
                                                 -- ⊢ Even (m + n) ↔ (Even m ↔ Even n)
                                                 -- ⊢ Even (m + n) ↔ (Even m ↔ Even n)
    simp [even_iff, h₁, h₂, Nat.add_mod]
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
#align nat.even_add Nat.even_add

theorem even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by
  rw [even_add, even_iff_not_odd, even_iff_not_odd, not_iff_not]
  -- 🎉 no goals
#align nat.even_add' Nat.even_add'

@[parity_simps]
theorem even_add_one : Even (n + 1) ↔ ¬Even n := by simp [even_add]
                                                    -- 🎉 no goals
#align nat.even_add_one Nat.even_add_one

set_option linter.deprecated false in
@[simp]
theorem not_even_bit1 (n : ℕ) : ¬Even (bit1 n) := by simp [bit1, parity_simps]
                                                     -- 🎉 no goals
#align nat.not_even_bit1 Nat.not_even_bit1

theorem two_not_dvd_two_mul_add_one (n : ℕ) : ¬2 ∣ 2 * n + 1 := by simp [add_mod]
                                                                   -- 🎉 no goals
#align nat.two_not_dvd_two_mul_add_one Nat.two_not_dvd_two_mul_add_one

theorem two_not_dvd_two_mul_sub_one : ∀ {n}, 0 < n → ¬2 ∣ 2 * n - 1
  | n + 1, _ => two_not_dvd_two_mul_add_one n
#align nat.two_not_dvd_two_mul_sub_one Nat.two_not_dvd_two_mul_sub_one

@[parity_simps]
theorem even_sub (h : n ≤ m) : Even (m - n) ↔ (Even m ↔ Even n) := by
  conv_rhs => rw [← tsub_add_cancel_of_le h, even_add]
  -- ⊢ Even (m - n) ↔ ((Even (m - n) ↔ Even n) ↔ Even n)
  by_cases h : Even n <;> simp [h]
  -- ⊢ Even (m - n) ↔ ((Even (m - n) ↔ Even n) ↔ Even n)
                          -- 🎉 no goals
                          -- 🎉 no goals
#align nat.even_sub Nat.even_sub

theorem even_sub' (h : n ≤ m) : Even (m - n) ↔ (Odd m ↔ Odd n) := by
  rw [even_sub h, even_iff_not_odd, even_iff_not_odd, not_iff_not]
  -- 🎉 no goals
#align nat.even_sub' Nat.even_sub'

theorem Odd.sub_odd (hm : Odd m) (hn : Odd n) : Even (m - n) :=
  (le_total n m).elim (fun h => by simp only [even_sub' h, *]) fun h => by
                                   -- 🎉 no goals
    simp only [tsub_eq_zero_iff_le.mpr h, even_zero]
    -- 🎉 no goals
#align nat.odd.sub_odd Nat.Odd.sub_odd

@[parity_simps]
theorem even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  cases' mod_two_eq_zero_or_one m with h₁ h₁ <;> cases' mod_two_eq_zero_or_one n with h₂ h₂ <;>
  -- ⊢ Even (m * n) ↔ Even m ∨ Even n
                                                 -- ⊢ Even (m * n) ↔ Even m ∨ Even n
                                                 -- ⊢ Even (m * n) ↔ Even m ∨ Even n
    simp [even_iff, h₁, h₂, Nat.mul_mod]
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
#align nat.even_mul Nat.even_mul

theorem odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by simp [not_or, even_mul]
                                                    -- 🎉 no goals
#align nat.odd_mul Nat.odd_mul

theorem Odd.of_mul_left (h : Odd (m * n)) : Odd m :=
  (odd_mul.mp h).1
#align nat.odd.of_mul_left Nat.Odd.of_mul_left

theorem Odd.of_mul_right (h : Odd (m * n)) : Odd n :=
  (odd_mul.mp h).2
#align nat.odd.of_mul_right Nat.Odd.of_mul_right

/-- If `m` and `n` are natural numbers, then the natural number `m^n` is even
if and only if `m` is even and `n` is positive. -/
@[parity_simps] theorem even_pow : Even (m ^ n) ↔ Even m ∧ n ≠ 0 := by
  induction' n with n ih <;> simp (config := { contextual := true }) [*, pow_succ', even_mul]
  -- ⊢ Even (m ^ zero) ↔ Even m ∧ zero ≠ 0
                             -- 🎉 no goals
                             -- 🎉 no goals
#align nat.even_pow Nat.even_pow

theorem even_pow' (h : n ≠ 0) : Even (m ^ n) ↔ Even m :=
  even_pow.trans <| and_iff_left h
#align nat.even_pow' Nat.even_pow'

theorem even_div : Even (m / n) ↔ m % (2 * n) / n = 0 := by
  rw [even_iff_two_dvd, dvd_iff_mod_eq_zero, Nat.div_mod_eq_mod_mul_div, mul_comm]
  -- 🎉 no goals
#align nat.even_div Nat.even_div

@[parity_simps] theorem odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_add, not_iff, odd_iff_not_even]
  -- 🎉 no goals
#align nat.odd_add Nat.odd_add

theorem odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by rw [add_comm, odd_add]
                                                        -- 🎉 no goals
#align nat.odd_add' Nat.odd_add'

theorem ne_of_odd_add (h : Odd (m + n)) : m ≠ n := fun hnot => by simp [hnot] at h
                                                                  -- 🎉 no goals
#align nat.ne_of_odd_add Nat.ne_of_odd_add

@[parity_simps] theorem odd_sub (h : n ≤ m) : Odd (m - n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_sub h, not_iff, odd_iff_not_even]
  -- 🎉 no goals
#align nat.odd_sub Nat.odd_sub

theorem Odd.sub_even (h : n ≤ m) (hm : Odd m) (hn : Even n) : Odd (m - n) :=
  (odd_sub h).mpr <| iff_of_true hm hn
#align nat.odd.sub_even Nat.Odd.sub_even

theorem odd_sub' (h : n ≤ m) : Odd (m - n) ↔ (Odd n ↔ Even m) := by
  rw [odd_iff_not_even, even_sub h, not_iff, not_iff_comm, odd_iff_not_even]
  -- 🎉 no goals
#align nat.odd_sub' Nat.odd_sub'

theorem Even.sub_odd (h : n ≤ m) (hm : Even m) (hn : Odd n) : Odd (m - n) :=
  (odd_sub' h).mpr <| iff_of_true hn hm
#align nat.even.sub_odd Nat.Even.sub_odd

theorem even_mul_succ_self (n : ℕ) : Even (n * (n + 1)) := by
  rw [even_mul, even_add_one]
  -- ⊢ Even n ∨ ¬Even n
  exact em _
  -- 🎉 no goals
#align nat.even_mul_succ_self Nat.even_mul_succ_self

theorem even_mul_self_pred : ∀ n : ℕ, Even (n * (n - 1))
  | 0 => even_zero
  | (n + 1) => mul_comm (n + 1 - 1) (n + 1) ▸ even_mul_succ_self n
#align nat.even_mul_self_pred Nat.even_mul_self_pred

theorem two_mul_div_two_of_even : Even n → 2 * (n / 2) = n := fun h =>
  Nat.mul_div_cancel_left' (even_iff_two_dvd.mp h)
#align nat.two_mul_div_two_of_even Nat.two_mul_div_two_of_even

theorem div_two_mul_two_of_even : Even n → n / 2 * 2 = n :=
  fun h => Nat.div_mul_cancel (even_iff_two_dvd.mp h)
#align nat.div_two_mul_two_of_even Nat.div_two_mul_two_of_even

theorem two_mul_div_two_add_one_of_odd (h : Odd n) : 2 * (n / 2) + 1 = n := by
  rw [← odd_iff.mp h, div_add_mod]
  -- 🎉 no goals
#align nat.two_mul_div_two_add_one_of_odd Nat.two_mul_div_two_add_one_of_odd

theorem div_two_mul_two_add_one_of_odd (h : Odd n) : n / 2 * 2 + 1 = n := by
  rw [← odd_iff.mp h, div_add_mod']
  -- 🎉 no goals
#align nat.div_two_mul_two_add_one_of_odd Nat.div_two_mul_two_add_one_of_odd

theorem one_add_div_two_mul_two_of_odd (h : Odd n) : 1 + n / 2 * 2 = n := by
  rw [← odd_iff.mp h, mod_add_div']
  -- 🎉 no goals
#align nat.one_add_div_two_mul_two_of_odd Nat.one_add_div_two_mul_two_of_odd

set_option linter.deprecated false in
section

theorem bit0_div_two : bit0 n / 2 = n := by
  rw [← Nat.bit0_eq_bit0, bit0_eq_two_mul, two_mul_div_two_of_even (even_bit0 n)]
  -- 🎉 no goals
#align nat.bit0_div_two Nat.bit0_div_two

theorem bit1_div_two : bit1 n / 2 = n := by
  rw [← Nat.bit1_eq_bit1, bit1, bit0_eq_two_mul, Nat.two_mul_div_two_add_one_of_odd (odd_bit1 n)]
  -- 🎉 no goals
#align nat.bit1_div_two Nat.bit1_div_two

@[simp]
theorem bit0_div_bit0 : bit0 n / bit0 m = n / m := by
  rw [bit0_eq_two_mul m, ← Nat.div_div_eq_div_mul, bit0_div_two]
  -- 🎉 no goals
#align nat.bit0_div_bit0 Nat.bit0_div_bit0

@[simp]
theorem bit1_div_bit0 : bit1 n / bit0 m = n / m := by
  rw [bit0_eq_two_mul, ← Nat.div_div_eq_div_mul, bit1_div_two]
  -- 🎉 no goals
#align nat.bit1_div_bit0 Nat.bit1_div_bit0

@[simp]
theorem bit0_mod_bit0 : bit0 n % bit0 m = bit0 (n % m) := by
  rw [bit0_eq_two_mul n, bit0_eq_two_mul m, bit0_eq_two_mul (n % m), Nat.mul_mod_mul_left]
  -- 🎉 no goals
#align nat.bit0_mod_bit0 Nat.bit0_mod_bit0

@[simp]
theorem bit1_mod_bit0 : bit1 n % bit0 m = bit1 (n % m) := by
  have h₁ := congr_arg bit1 (Nat.div_add_mod n m)
  -- ⊢ bit1 n % bit0 m = bit1 (n % m)
  -- `∀ m n : ℕ, bit0 m * n = bit0 (m * n)` seems to be missing...
  rw [bit1_add, bit0_eq_two_mul, ← mul_assoc, ← bit0_eq_two_mul] at h₁
  -- ⊢ bit1 n % bit0 m = bit1 (n % m)
  have h₂ := Nat.div_add_mod (bit1 n) (bit0 m)
  -- ⊢ bit1 n % bit0 m = bit1 (n % m)
  rw [bit1_div_bit0] at h₂
  -- ⊢ bit1 n % bit0 m = bit1 (n % m)
  exact add_left_cancel (h₂.trans h₁.symm)
  -- 🎉 no goals
#align nat.bit1_mod_bit0 Nat.bit1_mod_bit0

end

-- Here are examples of how `parity_simps` can be used with `Nat`.
example (m n : ℕ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp [*, two_ne_zero, parity_simps]
  -- 🎉 no goals

/- Porting note: the `simp` lemmas about `bit*` no longer apply, but `simp` in Lean 4 currently
simplifies decidable propositions. This may change in the future. -/
example : ¬Even 25394535 := by simp only
                               -- 🎉 no goals

end Nat

open Nat

namespace Function

namespace Involutive

variable {α : Type*} {f : α → α} {n : ℕ}

set_option linter.deprecated false in
section

theorem iterate_bit0 (hf : Involutive f) (n : ℕ) : f^[bit0 n] = id := by
  rw [bit0, ← two_mul, iterate_mul, involutive_iff_iter_2_eq_id.1 hf, iterate_id]
  -- 🎉 no goals
#align function.involutive.iterate_bit0 Function.Involutive.iterate_bit0

theorem iterate_bit1 (hf : Involutive f) (n : ℕ) : f^[bit1 n] = f := by
  rw [bit1, ←succ_eq_add_one, iterate_succ, hf.iterate_bit0, comp.left_id]
  -- 🎉 no goals
#align function.involutive.iterate_bit1 Function.Involutive.iterate_bit1

end

theorem iterate_two_mul (hf : Involutive f) (n : ℕ) : f^[2 * n] = id := by
  rw [iterate_mul, involutive_iff_iter_2_eq_id.1 hf, iterate_id]
  -- 🎉 no goals

theorem iterate_even (hf : Involutive f) (hn : Even n) : f^[n] = id := by
  rcases hn with ⟨m, rfl⟩
  -- ⊢ f^[m + m] = id
  rw [← two_mul, hf.iterate_two_mul]
  -- 🎉 no goals
#align function.involutive.iterate_even Function.Involutive.iterate_even

theorem iterate_odd (hf : Involutive f) (hn : Odd n) : f^[n] = f := by
  rcases hn with ⟨m, rfl⟩
  -- ⊢ f^[2 * m + 1] = f
  rw [iterate_add, hf.iterate_two_mul, comp.left_id, iterate_one]
  -- 🎉 no goals
#align function.involutive.iterate_odd Function.Involutive.iterate_odd

theorem iterate_eq_self (hf : Involutive f) (hne : f ≠ id) : f^[n] = f ↔ Odd n :=
  ⟨fun H => odd_iff_not_even.2 fun hn => hne <| by rwa [hf.iterate_even hn, eq_comm] at H,
                                                   -- 🎉 no goals
    hf.iterate_odd⟩
#align function.involutive.iterate_eq_self Function.Involutive.iterate_eq_self

theorem iterate_eq_id (hf : Involutive f) (hne : f ≠ id) : f^[n] = id ↔ Even n :=
  ⟨fun H => even_iff_not_odd.2 fun hn => hne <| by rwa [hf.iterate_odd hn] at H, hf.iterate_even⟩
                                                   -- 🎉 no goals
#align function.involutive.iterate_eq_id Function.Involutive.iterate_eq_id

end Involutive

end Function

variable {R : Type*} [Monoid R] [HasDistribNeg R] {n : ℕ}

theorem neg_one_pow_eq_one_iff_even (h : (-1 : R) ≠ 1) : (-1 : R) ^ n = 1 ↔ Even n :=
  ⟨fun h' => of_not_not fun hn => h <| (Odd.neg_one_pow <| odd_iff_not_even.mpr hn).symm.trans h',
    Even.neg_one_pow⟩
#align neg_one_pow_eq_one_iff_even neg_one_pow_eq_one_iff_even

/-- If `a` is even, then `n` is odd iff `n % a` is odd. -/
theorem Odd.mod_even_iff {n a : ℕ} (ha : Even a) : Odd (n % a) ↔ Odd n :=
  ((even_sub' <| mod_le n a).mp <|
      even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm
#align odd.mod_even_iff Odd.mod_even_iff

/-- If `a` is even, then `n` is even iff `n % a` is even. -/
theorem Even.mod_even_iff {n a : ℕ} (ha : Even a) : Even (n % a) ↔ Even n :=
  ((even_sub <| mod_le n a).mp <|
      even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm
#align even.mod_even_iff Even.mod_even_iff

/-- If `n` is odd and `a` is even, then `n % a` is odd. -/
theorem Odd.mod_even {n a : ℕ} (hn : Odd n) (ha : Even a) : Odd (n % a) :=
  (Odd.mod_even_iff ha).mpr hn
#align odd.mod_even Odd.mod_even

/-- If `n` is even and `a` is even, then `n % a` is even. -/
theorem Even.mod_even {n a : ℕ} (hn : Even n) (ha : Even a) : Even (n % a) :=
  (Even.mod_even_iff ha).mpr hn
#align even.mod_even Even.mod_even

theorem Odd.of_dvd_nat {m n : ℕ} (hn : Odd n) (hm : m ∣ n) : Odd m :=
  odd_iff_not_even.2 <| mt hm.even (odd_iff_not_even.1 hn)
#align odd.of_dvd_nat Odd.of_dvd_nat

/-- `2` is not a factor of an odd natural number. -/
theorem Odd.ne_two_of_dvd_nat {m n : ℕ} (hn : Odd n) (hm : m ∣ n) : m ≠ 2 := by
  rintro rfl
  -- ⊢ False
  exact absurd (hn.of_dvd_nat hm) (by decide)
  -- 🎉 no goals
#align odd.ne_two_of_dvd_nat Odd.ne_two_of_dvd_nat

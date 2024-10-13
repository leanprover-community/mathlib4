/-
Copyright (c) 2024 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Ring.RingNF

/-!
# Fermat numbers

The Fermat numbers are a sequence of natural numbers defined as `Nat.fermatNumber n = 2^(2^n) + 1`,
for all natural numbers `n`.

## Main theorems

- `Nat.coprime_fermatNumber_fermatNumber`: two distinct Fermat numbers are coprime.
-/

namespace Nat

open Finset
open scoped BigOperators

/-- Fermat numbers: the `n`-th Fermat number is defined as `2^(2^n) + 1`. -/
def fermatNumber (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1

@[simp] theorem fermatNumber_zero : fermatNumber 0 = 3 := rfl
@[simp] theorem fermatNumber_one : fermatNumber 1 = 5 := rfl
@[simp] theorem fermatNumber_two : fermatNumber 2 = 17 := rfl

theorem strictMono_fermatNumber : StrictMono fermatNumber := by
  intro m n
  simp only [fermatNumber, add_lt_add_iff_right, pow_lt_pow_iff_right (one_lt_two : 1 < 2),
    imp_self]

theorem two_lt_fermatNumber (n : ℕ) : 2 < fermatNumber n := by
  cases n
  · simp
  · exact lt_of_succ_lt <| strictMono_fermatNumber <| zero_lt_succ _

theorem odd_fermatNumber (n : ℕ) : Odd (fermatNumber n) :=
  (even_pow.mpr ⟨even_two, (pow_pos two_pos n).ne'⟩).add_one

theorem fermatNumber_product (n : ℕ) : ∏ k in range n, fermatNumber k = fermatNumber n - 2 := by
  induction' n with n hn
  · rfl
  rw [prod_range_succ, hn, fermatNumber, fermatNumber, mul_comm,
    (show 2 ^ 2 ^ n + 1 - 2 = 2 ^ 2 ^ n - 1 by omega), ← sq_sub_sq]
  ring_nf
  omega

theorem fermatNumber_eq_prod_add_two (n : ℕ) :
    fermatNumber n = (∏ k in range n, fermatNumber k) + 2 := by
  rw [fermatNumber_product, Nat.sub_add_cancel]
  exact le_of_lt <| two_lt_fermatNumber _

/--
**Goldbach's theorem** : no two distinct Fermat numbers share a common factor greater than one.

From a letter to Euler, see page 37 in [juskevic2022].
-/
theorem coprime_fermatNumber_fermatNumber {k n : ℕ} (h : k ≠ n) :
    Coprime (fermatNumber n) (fermatNumber k) := by
  wlog hkn : k < n
  · simpa only [coprime_comm] using this h.symm (by omega)
  let m := (fermatNumber n).gcd (fermatNumber k)
  have h_n : m ∣ fermatNumber n := (fermatNumber n).gcd_dvd_left (fermatNumber k)
  have h_m : m ∣ 2 := (Nat.dvd_add_right <| (gcd_dvd_right _ _).trans <| dvd_prod_of_mem _
    <| mem_range.mpr hkn).mp <| fermatNumber_eq_prod_add_two _ ▸ h_n
  refine ((dvd_prime prime_two).mp h_m).elim id (fun h_two ↦ ?_)
  exact ((odd_fermatNumber _).not_two_dvd_nat (h_two ▸ h_n)).elim

  end Nat

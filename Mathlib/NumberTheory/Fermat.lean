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

The Fermat numbers are a sequence of natural numbers defined as `fermat n = 2^(2^n) + 1`, for all
natural numbers `n`.

## Main theorems

- `coprime_fermat_fermat`: two distinct Fermat numbers are coprime.
-/

open Nat Finset
open scoped BigOperators

/-- Fermat numbers: the `n`-th Fermat number is defined as `2^(2^n) + 1`. -/
def fermat (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1

@[simp] theorem fermat_zero : fermat 0 = 3 := rfl
@[simp] theorem fermat_one : fermat 1 = 5 := rfl
@[simp] theorem fermat_two : fermat 2 = 17 := rfl

theorem strictMono_fermat : StrictMono fermat := by
  intro m n
  simp only [fermat, add_lt_add_iff_right, pow_lt_pow_iff_right (one_lt_two : 1 < 2), imp_self]

theorem two_lt_fermat (n : ℕ) : 2 < fermat n := by
  cases n
  · simp
  · exact lt_of_succ_lt <| strictMono_fermat <| zero_lt_succ _

theorem odd_fermat (n : ℕ) : Odd (fermat n) :=
  (even_pow.mpr ⟨even_two, (pow_pos two_pos n).ne'⟩).add_one

theorem fermat_product (n : ℕ) : ∏ k in range n, fermat k = fermat n - 2 := by
  induction' n with n hn
  · rfl
  rw [prod_range_succ, hn, fermat, fermat, mul_comm,
    (show 2 ^ 2 ^ n + 1 - 2 = 2 ^ 2 ^ n - 1 by omega), ← sq_sub_sq]
  ring_nf
  omega

theorem fermat_eq_prod_add_two (n : ℕ) : fermat n = (∏ k in range n, fermat k) + 2 := by
  rw [fermat_product, Nat.sub_add_cancel]
  exact le_of_lt <| two_lt_fermat _

/--
**Goldbach's theorem** : no two distinct Fermat numbers share a common factor greater than one.

From a letter to Euler, see page 37 in [juskevic2022].
-/
theorem coprime_fermat_fermat {k n : ℕ} (h : k ≠ n) : Coprime (fermat n) (fermat k) := by
  wlog hkn : k < n
  · simpa only [coprime_comm] using this h.symm (by omega)
  let m := (fermat n).gcd (fermat k)
  have h_n : m ∣ fermat n := (fermat n).gcd_dvd_left (fermat k)
  have h_m : m ∣ 2 := (Nat.dvd_add_right <| (gcd_dvd_right _ _).trans <| dvd_prod_of_mem _
    <| mem_range.mpr hkn).mp <| fermat_eq_prod_add_two _ ▸ h_n
  refine ((dvd_prime prime_two).mp h_m).elim id (fun h_two ↦ ?_)
  exact ((odd_fermat _).not_two_dvd_nat (h_two ▸ h_n)).elim

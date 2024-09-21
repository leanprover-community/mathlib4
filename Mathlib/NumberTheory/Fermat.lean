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

The Fermat numbers are a sequence of natural numbers defined as $2^{2^n} + 1$, for all natural
numbers $n$.

## Main theorems
  `coprime_fermat_fermat`: two distinct fermat numbers are coprime.
-/
open Nat
open scoped BigOperators

/-- The Fermat numbers:
the $n$-th Fermat number $F_n$ is defined as $2^{2^n} + 1$. -/
def fermat : ℕ → ℕ := fun n ↦ 2 ^ (2 ^ n) + 1

@[simp]
theorem fermat_zero : fermat 0 = 3 := by rfl

@[simp]
theorem fermat_one : fermat 1 = 5 := by rfl

@[simp]
theorem fermat_two : fermat 2 = 17 := by rfl

theorem strictMono_fermat : StrictMono fermat := by
  apply strictMono_nat_of_lt_succ
  simp only [fermat, add_lt_add_iff_right, Nat.pow_succ]
  exact fun n => (pow_lt_pow_iff_right one_lt_two).mpr (by aesop)

theorem two_lt_fermat {n : ℕ} : 2 < fermat n := by
  cases n
  · simp
  · exact lt_of_succ_lt <| strictMono_fermat <| zero_lt_succ _

theorem odd_fermat {n : ℕ} : Odd (fermat n) := by
  rw [fermat, ← Nat.not_even_iff_odd, Nat.even_add_one, not_not, Nat.even_pow]
  refine ⟨even_two, Nat.ne_of_gt (pow_pos zero_lt_two _)⟩

@[simp]
theorem fermat_product {n : ℕ} : ∏ k in Finset.range n, fermat k = fermat n - 2 := by
  induction' n with n hn
  · trivial
  rw [Finset.prod_range_succ, hn, fermat, fermat, mul_comm,
    (show 2 ^ 2 ^ n + 1 - 2 = 2 ^ 2 ^ n - 1 by omega),  ← Nat.sq_sub_sq]
  ring_nf
  omega

theorem  fermat_prod_add_two {n : ℕ} :  fermat n = (∏ k in Finset.range n, fermat k) + 2 := by
  rw [fermat_product, Nat.sub_add_cancel]
  exact le_of_lt two_lt_fermat

/-- **Goldbach's theorem** : no two distinct Fermat numbers share a common factor greater
than one. From a letter to Euler, see page 37 in [juvskevivc2022].-/
theorem coprime_fermat_fermat  {k n : ℕ} (h : k ≠ n): Coprime (fermat n) (fermat k) := by
  wlog hkn : k < n
  · apply coprime_comm.mp
    exact this h.symm (by omega)
  let m := (fermat n).gcd (fermat k)
  have h_n : m ∣ fermat n := (fermat n).gcd_dvd_left (fermat k)
  have h_m : m ∣ 2 :=  by
    have h_m_prod : m ∣ (∏ k in Finset.range n, fermat k) :=
      dvd_trans ((fermat n).gcd_dvd_right (fermat k))
      (Finset.dvd_prod_of_mem fermat (Finset.mem_range.mpr hkn))
    exact (Nat.dvd_add_right h_m_prod).mp <| fermat_prod_add_two ▸ h_n
  rcases (dvd_prime prime_two).mp h_m with h_one | h_two
  · exact h_one
  · by_contra
    rw [h_two] at h_n
    exact (not_even_iff_odd.mpr odd_fermat) <| even_iff_two_dvd.mpr h_n

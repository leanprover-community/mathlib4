/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Yury Kudryashov, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Squarefree.Basic

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Squarefree
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
meta import Mathlib.Tactic.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Primorial

This file defines the primorial function (the product of primes less than or equal to some bound),
and proves that `primorial n ≤ 4 ^ n`.

## Notation

We use the local notation `n#` for the primorial of `n`: that is, the product of the primes less
than or equal to `n`.
-/

@[expose] public section


open Finset

open Nat

/-- The primorial `n#` of `n` is the product of the primes less than or equal to `n`.
-/
def primorial (n : ℕ) : ℕ := ∏ p ∈ range (n + 1) with p.Prime, p

local notation x "#" => primorial x

@[simp] theorem primorial_zero : 0 # = 1 := by decide

@[simp] theorem primorial_one : 1 # = 1 := by decide

@[simp] theorem primorial_two : 2 # = 2 := by decide

theorem primorial_pos (n : ℕ) : 0 < n# :=
  prod_pos fun _p hp ↦ (mem_filter.1 hp).2.pos

theorem primorial_mono {m n : ℕ} (h : m ≤ n) : m# ≤ n# :=
  prod_le_prod_of_subset_of_one_le' (by gcongr) (by grind)

theorem primorial_monotone : Monotone primorial := fun _ _ ↦ primorial_mono

theorem primorial_dvd_primorial {m n : ℕ} (h : m ≤ n) : m# ∣ n# :=
  prod_dvd_prod_of_subset _ _ _ (by gcongr)

theorem primorial_succ {n : ℕ} (hn1 : n ≠ 1) (hn : Odd n) : (n + 1)# = n# := by
  refine prod_congr ?_ fun _ _ ↦ rfl
  rw [range_add_one, filter_insert, if_neg fun h ↦ not_even_iff_odd.2 hn _]
  exact fun h ↦ h.even_sub_one <| mt succ.inj hn1

theorem primorial_add (m n : ℕ) :
    (m + n)# = m# * ∏ p ∈ Ico (m + 1) (m + n + 1) with p.Prime, p := by
  simp_rw [primorial, ← Ico_zero_eq_range]
  rw [← prod_union, ← filter_union, Ico_union_Ico_eq_Ico]
  exacts [Nat.zero_le _, by lia, disjoint_filter_filter <| Ico_disjoint_Ico_consecutive _ _ _]

theorem primorial_add_dvd {m n : ℕ} (h : n ≤ m) : (m + n)# ∣ m# * choose (m + n) m :=
  calc
    (m + n)# = m# * ∏ p ∈ Ico (m + 1) (m + n + 1) with p.Prime, p := primorial_add _ _
    _ ∣ m# * choose (m + n) m :=
      mul_dvd_mul_left _ <|
        prod_primes_dvd _ (fun _ hk ↦ (mem_filter.1 hk).2.prime) fun p hp ↦ by
          rw [mem_filter, mem_Ico] at hp
          exact hp.2.dvd_choose_add hp.1.1 (h.trans_lt (m.lt_succ_self.trans_le hp.1.1))
              (Nat.lt_succ_iff.1 hp.1.2)

theorem primorial_add_le {m n : ℕ} (h : n ≤ m) : (m + n)# ≤ m# * choose (m + n) m :=
  le_of_dvd (mul_pos (primorial_pos _) (choose_pos <| Nat.le_add_right _ _)) (primorial_add_dvd h)

lemma Nat.Prime.dvd_primorial_iff {p n : ℕ} (hp : Prime p) : p ∣ n# ↔ p ≤ n := by
  refine ⟨?_, fun h ↦ dvd_prod_of_mem _ (by grind)⟩
  intro h
  simp only [primorial, hp.prime.dvd_finset_prod_iff, mem_filter, mem_range_succ_iff] at h
  obtain ⟨q, ⟨hqn, hq⟩, hpq⟩ := h
  exact (Nat.le_of_dvd hq.pos hpq).trans hqn

lemma Nat.Prime.dvd_primorial {p : ℕ} (hp : Prime p) : p ∣ p# :=
  hp.dvd_primorial_iff.2 le_rfl

lemma Squarefree.dvd_primorial {n : ℕ} (hn : Squarefree n) : n ∣ n# := by
  have : (∏ p ∈ n.primeFactors, p) ∣ (∏ p ∈ range (n + 1) with p.Prime, p) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (by grind [le_of_dvd])
  rwa [Nat.prod_primeFactors_of_squarefree hn] at this

lemma lt_primorial_self {n : ℕ} (hn : 2 < n) : n < n# := by
  have : 3 ≤ n# := single_le_prod' (f := id) (by grind [→ Prime.pos]) (by grind [prime_three])
  let q := (n# - 1).minFac
  have : n < q := by
    by_contra! h1
    replace h1 : q ∣ n# := (minFac_prime (by lia)).dvd_primorial_iff.2 h1
    grind [minFac_eq_one_iff, dvd_one, dvd_sub_iff_right, minFac_dvd]
  grind [Nat.minFac_le]

lemma le_primorial_self {n : ℕ} : n ≤ n# := by
  obtain hn | hn := le_or_gt n 2
  · decide +revert
  · exact (lt_primorial_self hn).le

theorem primorial_lt_four_pow (n : ℕ) (hn : n ≠ 0) : n# < 4 ^ n := by
  induction n using Nat.strong_induction_on with | h n ihn =>
  rcases n with - | n; · grind
  rcases n.even_or_odd with ⟨m, rfl⟩ | ho
  · rcases m.eq_zero_or_pos with rfl | hm
    · decide
    calc
      (m + m + 1)# = (m + 1 + m)# := by rw [add_right_comm]
      _ ≤ (m + 1)# * choose (m + 1 + m) (m + 1) := primorial_add_le m.le_succ
      _ = (m + 1)# * choose (2 * m + 1) m := by rw [choose_symm_add, two_mul, add_right_comm]
      _ < 4 ^ (m + 1) * 4 ^ m :=
        Nat.mul_lt_mul_of_lt_of_le (ihn _ (by lia) (by lia)) (choose_middle_le_pow _) (by simp)
      _ ≤ 4 ^ (m + m + 1) := by rw [← pow_add, add_right_comm]
  · rcases Decidable.eq_or_ne n 1 with rfl | hn
    · decide
    · calc
        (n + 1)# = n# := primorial_succ hn ho
        _ < 4 ^ n := ihn n n.lt_succ_self (by grind)
        _ ≤ 4 ^ (n + 1) := Nat.pow_le_pow_right four_pos n.le_succ

theorem primorial_le_four_pow (n : ℕ) : n# ≤ 4 ^ n := by
  obtain rfl | hn := eq_or_ne n 0
  · decide
  · exact (primorial_lt_four_pow n hn).le

@[deprecated (since := "2026-03-21")] alias primorial_le_4_pow := primorial_le_four_pow

/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Yury Kudryashov, Bhavik Mehta, XC0R
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.SmoothNumbers

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.NatSqrt

/-!
# Primorial

This file defines the primorial function (the product of primes less than or equal to some bound),
and proves that `primorial n ≤ 4 ^ n` and `2 ^ (n / 2) ≤ primorial n`.

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

lemma primorial_eq_prod_primesLE (n : ℕ) : n # = ∏ p ∈ primesLE n, p := rfl

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
  simp only [primorial, hp.prime.dvd_finsetProd_iff, mem_filter, mem_range_succ_iff] at h
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

/-!
## Chebyshev's Lower Bound on Primorial

We prove `2 ^ (n / 2 + 1) ≤ n#` for `n ≥ 5` and `2 ^ ((n + 1) / 2) ≤ n#` for `n ≥ 2`, where
`n#` denotes the primorial (product of all primes ≤ n). These are the lower bound complements to
`primorial_le_four_pow` (which gives the upper bound `n# ≤ 4^n`).

### Proof technique

Central binomial decomposition: from `4^n < n * C(2n,n)` (`four_pow_lt_mul_centralBinom`) and
`v_p(C(2n,n)) ≤ log_p(2n)` (`factorization_choose_le_log`), we bound `C(2n,n)` above by
`(2n)^{π(√(2n))} * (2n)#`. Rearranging gives `(2n)# ≥ 2^n` for `n ≥ 29`.

The key analytical step shows `(log₂(2n)+1) * (√(2n)+2) ≤ n` for `n > 400` by factoring
through `r = √n`:
- `2*(log₂(2n)+1) ≤ r` via `2n < 2^(r/2)` (exponential beats polynomial)
- `√(2n)+2 ≤ 2*r`
- Combine with `r² ≤ n`

Base cases `n ∈ [3, 29]` by computation.

### Main results

- `two_pow_succ_lt_primorial`: `2 ^ (n + 1) < (2 * n)#` for `n ≥ 3`
- `two_pow_lt_primorial`: `2 ^ n < (2 * n)#` for `n ≥ 2`
- `two_pow_le_primorial`: `2 ^ n ≤ (2 * n)#` for all `n`
- `two_pow_half_add_one_le_primorial`: `2 ^ (n / 2 + 1) ≤ n#` for `n ≥ 5`
- `two_pow_half_succ_le_primorial`: `2 ^ ((n + 1) / 2) ≤ n#` for `n ≥ 2`
- `two_pow_div_two_le_primorial`: `2 ^ (n / 2) ≤ n#` for all `n`
-/

private lemma primesBelow_filter_le {m n : ℕ} (h : m < n) :
    n.primesBelow.filter (· ≤ m) = (m + 1).primesBelow := by
  ext p; simp [mem_primesBelow, Finset.mem_filter]; lia

/-- `C(2n, n) ≤ (2n)^{π(√(2n))} * (2n)#` for `n ≥ 4`. -/
theorem centralBinom_le_pow_mul_primorial {n : ℕ} (hn : 4 ≤ n) :
    centralBinom n ≤ (2 * n) ^ (sqrt (2 * n) + 1).primesBelow.card * (2 * n)# := by
  set s := sqrt (2 * n)
  let f x := x ^ (centralBinom n).factorization x
  have hS : ∏ x ∈ (2 * n + 1).primesBelow, f x = ∏ x ∈ range (2 * n + 1), f x := by
    refine prod_filter_of_ne fun p _ h ↦ ?_
    contrapose! h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime _ h, pow_zero]
  rw [← prod_pow_factorization_centralBinom, ← hS,
    ← prod_filter_mul_prod_filter_not _ (· ≤ s)]
  gcongr
  · rw [primesBelow_filter_le (sqrt_le_self (2 * n) |>.trans_lt (lt_add_one _))]
    exact prod_le_pow_card _ _ _ fun _ _ ↦ pow_factorization_choose_le (by lia)
  · rw [primorial, ← primesBelow]
    have H : ∀ p ∈ {x ∈ (2 * n + 1).primesBelow | ¬x ≤ s}, f p ≤ p := by
      intro p hp
      nth_rewrite 2 [← pow_one p]
      exact pow_le_pow_right₀ (by grind) <| factorization_choose_le_one <| sqrt_lt'.mp (by grind)
    refine prod_le_prod' H |>.trans ?_
    exact prod_le_prod_of_subset_of_one_le (filter_subset ..) (by lia)
      fun p hp _ ↦ (prime_of_mem_primesBelow hp).one_le

/-- `8u² + 16u + 8 ≤ 2^u` for `u ≥ 10`. -/
theorem eight_mul_sq_add_le_two_pow (u : ℕ) (hu : 10 ≤ u) :
    8 * u ^ 2 + 16 * u + 8 ≤ 2 ^ u := by
  rw [show 8 * u ^ 2 + 16 * u + 8 = 8 * (u + 1) ^ 2 by lia]
  induction u, hu using Nat.le_induction with
  | base => decide
  | succ u hu ih =>
    rw [show (u + 1 + 1) ^ 2 = (u + 1) ^ 2 + (u + 3 + u) by lia, mul_add, pow_succ' 2, two_mul]
    exact Nat.add_le_add ih (ih.trans' (by nlinarith))

/-- `(2n)^{π(√(2n))+1} ≤ 2^n` for `n ≥ 30`. -/
private theorem numerical_bound_aux (n l u k : ℕ)
    (hl : l ≤ n := by lia) (hu : n ≤ u := by lia)
    (hu₀ : 0 < u := by lia) (H : (2 * u) ^ (k + 1) ≤ 2 ^ l := by norm_num)
    (hπ : #((2 * u).sqrt + 1).primesBelow = k := by norm_num [primesBelow]; decide) :
    (2 * n) ^ (#((2 * n).sqrt + 1).primesBelow + 1) ≤ 2 ^ n := by
  set π := #((2 * n).sqrt + 1).primesBelow
  have hcard : π ≤ k := by
    rw [← hπ]
    exact card_le_card <| filter_subset_filter _ <| range_subset_range.mpr (by gcongr)
  calc (2 * n) ^ (π + 1)
      ≤ (2 * u) ^ (π + 1) := Nat.pow_le_pow_left (by gcongr) _
    _ ≤ (2 * u) ^ (k + 1) := pow_le_pow_right₀ (by lia) (by lia)
    _ ≤ 2 ^ l := H
    _ ≤ 2 ^ n := pow_le_pow_right₀ one_le_two hl

private theorem numerical_bound_aux' {n : ℕ} (hn : 400 ≤ n) :
    (2 * n) ^ (#((2 * n).sqrt + 1).primesBelow + 1) ≤ 2 ^ n := by
  set π := (sqrt (2 * n) + 1).primesBelow.card
  have hπ : π ≤ sqrt (2 * n) + 1 :=
    (card_filter_le _ _).trans (card_range _).le
  set s := sqrt (2 * n)
  set L := Nat.log 2 (2 * n)
  have h2n_bound : 2 * n < 2 ^ (L + 1) := lt_pow_succ_log_self (by lia) (2 * n)
  suffices h : (L + 1) * (s + 2) ≤ n by
    calc (2 * n) ^ (π + 1)
        ≤ (2 * n) ^ (s + 2) := by gcongr; lia
      _ ≤ (2 ^ (L + 1)) ^ (s + 2) := (Nat.pow_lt_pow_left h2n_bound (by lia)).le
      _ = 2 ^ ((L + 1) * (s + 2)) := (pow_mul ..).symm
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by lia) h
  set r := sqrt n
  have hr_ge : 20 ≤ r := le_sqrt.mpr (by lia)
  have hr_sq : r * r ≤ n := sqrt_le n
  have hr_lt : n < (r + 1) * (r + 1) := lt_succ_sqrt n
  have hb : s + 2 ≤ 2 * r := by
    suffices hslt : s < 2 * r - 1 by lia
    rw [show s = sqrt (2 * n) from rfl, sqrt_lt]
    zify [show 1 ≤ 2 * r by lia]
    nlinarith [sq_nonneg (r : ℤ)]
  have ha : 2 * (L + 1) ≤ r := by
    suffices L < r / 2 by lia
    suffices 2 * n < 2 ^ (r / 2) from (Nat.log_lt_iff_lt_pow one_lt_two (by lia)).mpr this
    calc 2 * n
        < 2 * ((r + 1) * (r + 1)) := by gcongr
      _ ≤ 2 * ((2 * (r / 2) + 2) * (2 * (r / 2) + 2)) := by gcongr <;> lia
      _ = 8 * (r / 2) ^ 2 + 16 * (r / 2) + 8 := by ring
      _ ≤ 2 ^ (r / 2) := eight_mul_sq_add_le_two_pow (r / 2) (by lia)
  nlinarith

/-- `(2n)^{π(√(2n))+1} ≤ 2^n` for `n ≥ 30`. -/
private theorem numerical_bound {n : ℕ} (hn : 30 ≤ n) :
    (2 * n) ^ ((sqrt (2 * n) + 1).primesBelow.card + 1) ≤ 2 ^ n := by
  set π := (sqrt (2 * n) + 1).primesBelow.card
  have hπ : π ≤ sqrt (2 * n) + 1 :=
    (card_filter_le _ _).trans (card_range _).le
  rcases le_or_gt 400 n with h_large | h_small
  · exact numerical_bound_aux' h_large
  · rcases le_or_gt n 32 with h₁ | h₁
    · exact numerical_bound_aux n 30 32 4
    rcases le_or_gt n 44 with h₂ | h₂
    · exact numerical_bound_aux n 33 44 4
    rcases le_or_gt n 84 with h₃ | h₃
    · exact numerical_bound_aux n 45 84 5
    rcases le_or_gt n 264 with h₄ | h₄
    · exact numerical_bound_aux n 85 264 8
    · set_option exponentiation.threshold 300 in
      refine numerical_bound_aux n 265 400 9

/-- `2 ^ (n + 1) < (2n)#` for `n ≥ 3`. The core Chebyshev lower bound from which all
weaker variants are derived. -/
theorem two_pow_succ_lt_primorial {n : ℕ} (hn : 3 ≤ n) : 2 ^ (n + 1) < (2 * n)# := by
  obtain hn' | hn' := le_or_gt 30 n
  · have h4 : 4 ≤ n := by lia
    set π := (sqrt (2 * n) + 1).primesBelow.card
    apply lt_of_mul_lt_mul_left' (a := n * (2 * n) ^ π)
    calc
      _ = (2 * n) ^ (π + 1) * 2 ^ n := by ring
      _ ≤ 2 ^ n * 2 ^ n := mul_le_mul_left (numerical_bound hn') _
      _ = 4 ^ n := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      _ < n * n.centralBinom := four_pow_lt_mul_centralBinom _ h4
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_left _ (centralBinom_le_pow_mul_primorial h4)
  · decide +revert

/-- **Strict Chebyshev lower bound**. `2 ^ n < (2n)#` for all `n ≥ 2`. -/
theorem two_pow_lt_primorial {n : ℕ} (hn : 2 ≤ n) : 2 ^ n < (2 * n)# := by
  rcases Nat.lt_or_eq_of_le hn with hn | rfl
  · exact (Nat.pow_lt_pow_right (by lia) (by lia)).trans (two_pow_succ_lt_primorial (by lia))
  · decide

/-- **Even Chebyshev lower bound**. `2 ^ n ≤ (2n)#` for all `n`. -/
theorem two_pow_le_primorial {n : ℕ} : 2 ^ n ≤ (2 * n)# := by
  obtain hn | hn := le_or_gt 2 n
  · exact (two_pow_lt_primorial hn).le
  · decide +revert

/-- **Strongest Chebyshev lower bound**. `2 ^ (n / 2 + 1) ≤ n#` for `n ≥ 5`. -/
theorem two_pow_half_add_one_le_primorial {n : ℕ} (hn : 5 ≤ n) : 2 ^ (n / 2 + 1) ≤ n# := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · grind [two_pow_succ_lt_primorial]
  · rw [← primorial_succ (by lia) ⟨k, rfl⟩]
    grind [two_pow_lt_primorial (show 2 ≤ k + 1 by lia)]

/-- **Stronger Chebyshev lower bound**. `2 ^ ((n + 1) / 2) ≤ n#` for `n ≥ 2`. -/
theorem two_pow_half_succ_le_primorial {n : ℕ} (hn : 2 ≤ n) : 2 ^ ((n + 1) / 2) ≤ n# := by
  obtain hn | hn := le_or_gt 5 n
  · exact (pow_le_pow_right₀ (by lia) (by lia)).trans (two_pow_half_add_one_le_primorial hn)
  · decide +revert

/-- **Chebyshev lower bound** (1852). `2 ^ (n / 2) ≤ n#` for all `n`.

The product of all primes up to `n` is at least `2 ^ (n / 2)`. This is the lower bound
complement to `primorial_le_four_pow` (which gives the upper bound `n# ≤ 4 ^ n`).
Note: this is weaker than `√2 ^ n ≤ n#` (see `sqrt_two_pow_le_primorial`) when `n` is odd. -/
theorem two_pow_div_two_le_primorial {n : ℕ} : 2 ^ (n / 2) ≤ n# :=
  two_pow_le_primorial.trans (primorial_mono (Nat.mul_div_le ..))

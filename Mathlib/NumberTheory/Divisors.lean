/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module number_theory.divisors
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Nat.Factors

/-!
# Divisor finsets

This file defines sets of divisors of a natural number. This is particularly useful as background
for defining Dirichlet convolution.

## Main Definitions
Let `n : ℕ`. All of the following definitions are in the `nat` namespace:
 * `divisors n` is the `finset` of natural numbers that divide `n`.
 * `proper_divisors n` is the `finset` of natural numbers that divide `n`, other than `n`.
 * `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.
 * `perfect n` is true when `n` is positive and the sum of `proper_divisors n` is `n`.

## Implementation details
 * `divisors 0`, `proper_divisors 0`, and `divisors_antidiagonal 0` are defined to be `∅`.

## Tags
divisors, perfect numbers

-/


open Classical

open BigOperators

open Finset

namespace Nat

variable (n : ℕ)

/-- `divisors n` is the `finset` of divisors of `n`. As a special case, `divisors 0 = ∅`. -/
def divisors : Finset ℕ :=
  Finset.filter (fun x : ℕ => x ∣ n) (Finset.Ico 1 (n + 1))
#align nat.divisors Nat.divisors

/-- `proper_divisors n` is the `finset` of divisors of `n`, other than `n`.
  As a special case, `proper_divisors 0 = ∅`. -/
def properDivisors : Finset ℕ :=
  Finset.filter (fun x : ℕ => x ∣ n) (Finset.Ico 1 n)
#align nat.proper_divisors Nat.properDivisors

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- `divisors_antidiagonal n` is the `finset` of pairs `(x,y)` such that `x * y = n`.
  As a special case, `divisors_antidiagonal 0 = ∅`. -/
def divisorsAntidiagonal : Finset (ℕ × ℕ) :=
  (Ico 1 (n + 1) ×ˢ Ico 1 (n + 1)).filter fun x => x.fst * x.snd = n
#align nat.divisors_antidiagonal Nat.divisorsAntidiagonal

variable {n}

@[simp]
theorem filter_dvd_eq_divisors (h : n ≠ 0) : (Finset.range n.succ).filter (· ∣ n) = n.divisors :=
  by
  ext
  simp only [divisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)
#align nat.filter_dvd_eq_divisors Nat.filter_dvd_eq_divisors

@[simp]
theorem filter_dvd_eq_properDivisors (h : n ≠ 0) :
    (Finset.range n).filter (· ∣ n) = n.properDivisors :=
  by
  ext
  simp only [proper_divisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)
#align nat.filter_dvd_eq_proper_divisors Nat.filter_dvd_eq_properDivisors

theorem properDivisors.not_self_mem : ¬n ∈ properDivisors n := by simp [proper_divisors]
#align nat.proper_divisors.not_self_mem Nat.properDivisors.not_self_mem

@[simp]
theorem mem_properDivisors {m : ℕ} : n ∈ properDivisors m ↔ n ∣ m ∧ n < m :=
  by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [proper_divisors]
  simp only [and_comm', ← filter_dvd_eq_proper_divisors hm, mem_filter, mem_range]
#align nat.mem_proper_divisors Nat.mem_properDivisors

theorem insert_self_properDivisors (h : n ≠ 0) : insert n (properDivisors n) = divisors n := by
  rw [divisors, proper_divisors, Ico_succ_right_eq_insert_Ico (one_le_iff_ne_zero.2 h),
    Finset.filter_insert, if_pos (dvd_refl n)]
#align nat.insert_self_proper_divisors Nat.insert_self_properDivisors

theorem cons_self_properDivisors (h : n ≠ 0) :
    cons n (properDivisors n) properDivisors.not_self_mem = divisors n := by
  rw [cons_eq_insert, insert_self_proper_divisors h]
#align nat.cons_self_proper_divisors Nat.cons_self_properDivisors

@[simp]
theorem mem_divisors {m : ℕ} : n ∈ divisors m ↔ n ∣ m ∧ m ≠ 0 :=
  by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [divisors]
  simp only [hm, Ne.def, not_false_iff, and_true_iff, ← filter_dvd_eq_divisors hm, mem_filter,
    mem_range, and_iff_right_iff_imp, lt_succ_iff]
  exact le_of_dvd hm.bot_lt
#align nat.mem_divisors Nat.mem_divisors

theorem one_mem_divisors : 1 ∈ divisors n ↔ n ≠ 0 := by simp
#align nat.one_mem_divisors Nat.one_mem_divisors

theorem mem_divisors_self (n : ℕ) (h : n ≠ 0) : n ∈ n.divisors :=
  mem_divisors.2 ⟨dvd_rfl, h⟩
#align nat.mem_divisors_self Nat.mem_divisors_self

theorem dvd_of_mem_divisors {m : ℕ} (h : n ∈ divisors m) : n ∣ m :=
  by
  cases m
  · apply dvd_zero
  · simp [mem_divisors.1 h]
#align nat.dvd_of_mem_divisors Nat.dvd_of_mem_divisors

@[simp]
theorem mem_divisorsAntidiagonal {x : ℕ × ℕ} :
    x ∈ divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n ≠ 0 :=
  by
  simp only [divisors_antidiagonal, Finset.mem_Ico, Ne.def, Finset.mem_filter, Finset.mem_product]
  rw [and_comm']
  apply and_congr_right
  rintro rfl
  constructor <;> intro h
  · contrapose! h
    simp [h]
  · rw [Nat.lt_add_one_iff, Nat.lt_add_one_iff]
    rw [mul_eq_zero, Decidable.not_or_iff_and_not] at h
    simp only [succ_le_of_lt (Nat.pos_of_ne_zero h.1), succ_le_of_lt (Nat.pos_of_ne_zero h.2),
      true_and_iff]
    exact
      ⟨le_mul_of_pos_right (Nat.pos_of_ne_zero h.2), le_mul_of_pos_left (Nat.pos_of_ne_zero h.1)⟩
#align nat.mem_divisors_antidiagonal Nat.mem_divisorsAntidiagonal

variable {n}

theorem divisor_le {m : ℕ} : n ∈ divisors m → n ≤ m :=
  by
  cases m
  · simp
  simp only [mem_divisors, m.succ_ne_zero, and_true_iff, Ne.def, not_false_iff]
  exact Nat.le_of_dvd (Nat.succ_pos m)
#align nat.divisor_le Nat.divisor_le

theorem divisors_subset_of_dvd {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) : divisors m ⊆ divisors n :=
  Finset.subset_iff.2 fun x hx => Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hx).1.trans h, hzero⟩
#align nat.divisors_subset_of_dvd Nat.divisors_subset_of_dvd

theorem divisors_subset_properDivisors {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) (hdiff : m ≠ n) :
    divisors m ⊆ properDivisors n := by
  apply Finset.subset_iff.2
  intro x hx
  exact
    Nat.mem_properDivisors.2
      ⟨(Nat.mem_divisors.1 hx).1.trans h,
        lt_of_le_of_lt (divisor_le hx)
          (lt_of_le_of_ne (divisor_le (Nat.mem_divisors.2 ⟨h, hzero⟩)) hdiff)⟩
#align nat.divisors_subset_proper_divisors Nat.divisors_subset_properDivisors

@[simp]
theorem divisors_zero : divisors 0 = ∅ := by
  ext
  simp
#align nat.divisors_zero Nat.divisors_zero

@[simp]
theorem properDivisors_zero : properDivisors 0 = ∅ :=
  by
  ext
  simp
#align nat.proper_divisors_zero Nat.properDivisors_zero

theorem properDivisors_subset_divisors : properDivisors n ⊆ divisors n :=
  filter_subset_filter _ <| Ico_subset_Ico_right n.le_succ
#align nat.proper_divisors_subset_divisors Nat.properDivisors_subset_divisors

@[simp]
theorem divisors_one : divisors 1 = {1} := by
  ext
  simp
#align nat.divisors_one Nat.divisors_one

@[simp]
theorem properDivisors_one : properDivisors 1 = ∅ := by rw [proper_divisors, Ico_self, filter_empty]
#align nat.proper_divisors_one Nat.properDivisors_one

theorem pos_of_mem_divisors {m : ℕ} (h : m ∈ n.divisors) : 0 < m :=
  by
  cases m
  · rw [mem_divisors, zero_dvd_iff] at h
    cases h.2 h.1
  apply Nat.succ_pos
#align nat.pos_of_mem_divisors Nat.pos_of_mem_divisors

theorem pos_of_mem_properDivisors {m : ℕ} (h : m ∈ n.properDivisors) : 0 < m :=
  pos_of_mem_divisors (properDivisors_subset_divisors h)
#align nat.pos_of_mem_proper_divisors Nat.pos_of_mem_properDivisors

theorem one_mem_properDivisors_iff_one_lt : 1 ∈ n.properDivisors ↔ 1 < n := by
  rw [mem_proper_divisors, and_iff_right (one_dvd _)]
#align nat.one_mem_proper_divisors_iff_one_lt Nat.one_mem_properDivisors_iff_one_lt

@[simp]
theorem divisorsAntidiagonal_zero : divisorsAntidiagonal 0 = ∅ :=
  by
  ext
  simp
#align nat.divisors_antidiagonal_zero Nat.divisorsAntidiagonal_zero

@[simp]
theorem divisorsAntidiagonal_one : divisorsAntidiagonal 1 = {(1, 1)} :=
  by
  ext
  simp [Nat.mul_eq_one_iff, Prod.ext_iff]
#align nat.divisors_antidiagonal_one Nat.divisorsAntidiagonal_one

@[simp]
theorem swap_mem_divisorsAntidiagonal {x : ℕ × ℕ} :
    x.swap ∈ divisorsAntidiagonal n ↔ x ∈ divisorsAntidiagonal n := by
  rw [mem_divisors_antidiagonal, mem_divisors_antidiagonal, mul_comm, Prod.swap]
#align nat.swap_mem_divisors_antidiagonal Nat.swap_mem_divisorsAntidiagonal

theorem fst_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisorsAntidiagonal n) :
    x.fst ∈ divisors n := by
  rw [mem_divisors_antidiagonal] at h
  simp [Dvd.intro _ h.1, h.2]
#align nat.fst_mem_divisors_of_mem_antidiagonal Nat.fst_mem_divisors_of_mem_antidiagonal

theorem snd_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisorsAntidiagonal n) :
    x.snd ∈ divisors n := by
  rw [mem_divisors_antidiagonal] at h
  simp [Dvd.intro_left _ h.1, h.2]
#align nat.snd_mem_divisors_of_mem_antidiagonal Nat.snd_mem_divisors_of_mem_antidiagonal

@[simp]
theorem map_swap_divisorsAntidiagonal :
    (divisorsAntidiagonal n).map (Equiv.prodComm _ _).toEmbedding = divisorsAntidiagonal n :=
  by
  rw [← coe_inj, coe_map, Equiv.coe_toEmbedding, Equiv.coe_prodComm,
    Set.image_swap_eq_preimage_swap]
  ext
  exact swap_mem_divisors_antidiagonal
#align nat.map_swap_divisors_antidiagonal Nat.map_swap_divisorsAntidiagonal

@[simp]
theorem image_fst_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.fst = divisors n :=
  by
  ext
  simp [Dvd.Dvd, @eq_comm _ n (_ * _)]
#align nat.image_fst_divisors_antidiagonal Nat.image_fst_divisorsAntidiagonal

@[simp]
theorem image_snd_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.snd = divisors n :=
  by
  rw [← map_swap_divisors_antidiagonal, map_eq_image, image_image]
  exact image_fst_divisors_antidiagonal
#align nat.image_snd_divisors_antidiagonal Nat.image_snd_divisorsAntidiagonal

theorem map_div_right_divisors :
    n.divisors.map ⟨fun d => (d, n / d), fun p₁ p₂ => congr_arg Prod.fst⟩ =
      n.divisorsAntidiagonal :=
  by
  ext ⟨d, nd⟩
  simp only [mem_map, mem_divisors_antidiagonal, Function.Embedding.coeFn_mk, mem_divisors,
    Prod.ext_iff, exists_prop, and_left_comm, exists_eq_left]
  constructor
  · rintro ⟨⟨⟨k, rfl⟩, hn⟩, rfl⟩
    rw [Nat.mul_div_cancel_left _ (left_ne_zero_of_mul hn).bot_lt]
    exact ⟨rfl, hn⟩
  · rintro ⟨rfl, hn⟩
    exact ⟨⟨dvd_mul_right _ _, hn⟩, Nat.mul_div_cancel_left _ (left_ne_zero_of_mul hn).bot_lt⟩
#align nat.map_div_right_divisors Nat.map_div_right_divisors

theorem map_div_left_divisors :
    n.divisors.map ⟨fun d => (n / d, d), fun p₁ p₂ => congr_arg Prod.snd⟩ =
      n.divisorsAntidiagonal :=
  by
  apply Finset.map_injective (Equiv.prodComm _ _).toEmbedding
  rw [map_swap_divisors_antidiagonal, ← map_div_right_divisors, Finset.map_map]
  rfl
#align nat.map_div_left_divisors Nat.map_div_left_divisors

theorem sum_divisors_eq_sum_properDivisors_add_self :
    (∑ i in divisors n, i) = (∑ i in properDivisors n, i) + n :=
  by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  · rw [← cons_self_proper_divisors hn, Finset.sum_cons, add_comm]
#align nat.sum_divisors_eq_sum_proper_divisors_add_self Nat.sum_divisors_eq_sum_properDivisors_add_self

/-- `n : ℕ` is perfect if and only the sum of the proper divisors of `n` is `n` and `n`
  is positive. -/
def Perfect (n : ℕ) : Prop :=
  (∑ i in properDivisors n, i) = n ∧ 0 < n
#align nat.perfect Nat.Perfect

theorem perfect_iff_sum_properDivisors (h : 0 < n) : Perfect n ↔ (∑ i in properDivisors n, i) = n :=
  and_iff_left h
#align nat.perfect_iff_sum_proper_divisors Nat.perfect_iff_sum_properDivisors

theorem perfect_iff_sum_divisors_eq_two_mul (h : 0 < n) :
    Perfect n ↔ (∑ i in divisors n, i) = 2 * n :=
  by
  rw [perfect_iff_sum_proper_divisors h, sum_divisors_eq_sum_proper_divisors_add_self, two_mul]
  constructor <;> intro h
  · rw [h]
  · apply add_right_cancel h
#align nat.perfect_iff_sum_divisors_eq_two_mul Nat.perfect_iff_sum_divisors_eq_two_mul

theorem mem_divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) {x : ℕ} :
    x ∈ divisors (p ^ k) ↔ ∃ (j : ℕ)(H : j ≤ k), x = p ^ j := by
  rw [mem_divisors, Nat.dvd_prime_pow pp, and_iff_left (ne_of_gt (pow_pos pp.pos k))]
#align nat.mem_divisors_prime_pow Nat.mem_divisors_prime_pow

theorem Prime.divisors {p : ℕ} (pp : p.Prime) : divisors p = {1, p} :=
  by
  ext
  rw [mem_divisors, dvd_prime pp, and_iff_left pp.ne_zero, Finset.mem_insert, Finset.mem_singleton]
#align nat.prime.divisors Nat.Prime.divisors

theorem Prime.properDivisors {p : ℕ} (pp : p.Prime) : properDivisors p = {1} := by
  rw [← erase_insert proper_divisors.not_self_mem, insert_self_proper_divisors pp.ne_zero,
    pp.divisors, pair_comm, erase_insert fun con => pp.ne_one (mem_singleton.1 Con)]
#align nat.prime.proper_divisors Nat.Prime.properDivisors

theorem divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) :
    divisors (p ^ k) = (Finset.range (k + 1)).map ⟨pow p, pow_right_injective pp.two_le⟩ :=
  by
  ext
  simp [mem_divisors_prime_pow, pp, Nat.lt_succ_iff, @eq_comm _ a]
#align nat.divisors_prime_pow Nat.divisors_prime_pow

theorem eq_properDivisors_of_subset_of_sum_eq_sum {s : Finset ℕ} (hsub : s ⊆ n.properDivisors) :
    ((∑ x in s, x) = ∑ x in n.properDivisors, x) → s = n.properDivisors :=
  by
  cases n
  · rw [proper_divisors_zero, subset_empty] at hsub
    simp [hsub]
  classical
    rw [← sum_sdiff hsub]
    intro h
    apply subset.antisymm hsub
    rw [← sdiff_eq_empty_iff_subset]
    contrapose h
    rw [← Ne.def, ← nonempty_iff_ne_empty] at h
    apply ne_of_lt
    rw [← zero_add (∑ x in s, x), ← add_assoc, add_zero]
    apply add_lt_add_right
    have hlt :=
      sum_lt_sum_of_nonempty h fun x hx => pos_of_mem_proper_divisors (sdiff_subset _ _ hx)
    simp only [sum_const_zero] at hlt
    apply hlt
#align nat.eq_proper_divisors_of_subset_of_sum_eq_sum Nat.eq_properDivisors_of_subset_of_sum_eq_sum

theorem sum_properDivisors_dvd (h : (∑ x in n.properDivisors, x) ∣ n) :
    (∑ x in n.properDivisors, x) = 1 ∨ (∑ x in n.properDivisors, x) = n :=
  by
  cases n
  · simp
  cases n
  · contrapose! h
    simp
  rw [or_iff_not_imp_right]
  intro ne_n
  have hlt : (∑ x in n.succ.succ.proper_divisors, x) < n.succ.succ :=
    lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h) ne_n
  symm
  rw [← mem_singleton,
    eq_proper_divisors_of_subset_of_sum_eq_sum
      (singleton_subset_iff.2 (mem_proper_divisors.2 ⟨h, hlt⟩)) sum_singleton,
    mem_proper_divisors]
  refine' ⟨one_dvd _, Nat.succ_lt_succ (Nat.succ_pos _)⟩
#align nat.sum_proper_divisors_dvd Nat.sum_properDivisors_dvd

@[simp, to_additive]
theorem Prime.prod_properDivisors {α : Type _} [CommMonoid α] {p : ℕ} {f : ℕ → α} (h : p.Prime) :
    (∏ x in p.properDivisors, f x) = f 1 := by simp [h.proper_divisors]
#align nat.prime.prod_proper_divisors Nat.Prime.prod_properDivisors
#align nat.prime.sum_proper_divisors Nat.Prime.sum_properDivisors

@[simp, to_additive]
theorem Prime.prod_divisors {α : Type _} [CommMonoid α] {p : ℕ} {f : ℕ → α} (h : p.Prime) :
    (∏ x in p.divisors, f x) = f p * f 1 := by
  rw [← cons_self_proper_divisors h.ne_zero, prod_cons, h.prod_proper_divisors]
#align nat.prime.prod_divisors Nat.Prime.prod_divisors
#align nat.prime.sum_divisors Nat.Prime.sum_divisors

theorem properDivisors_eq_singleton_one_iff_prime : n.properDivisors = {1} ↔ n.Prime :=
  ⟨fun h => by
    have h1 := mem_singleton.2 rfl
    rw [← h, mem_proper_divisors] at h1
    refine' nat.prime_def_lt''.mpr ⟨h1.2, fun m hdvd => _⟩
    rw [← mem_singleton, ← h, mem_proper_divisors]
    have hle := Nat.le_of_dvd (lt_trans (Nat.succ_pos _) h1.2) hdvd
    exact Or.imp_left (fun hlt => ⟨hdvd, hlt⟩) hle.lt_or_eq, Prime.properDivisors⟩
#align nat.proper_divisors_eq_singleton_one_iff_prime Nat.properDivisors_eq_singleton_one_iff_prime

theorem sum_properDivisors_eq_one_iff_prime : (∑ x in n.properDivisors, x) = 1 ↔ n.Prime :=
  by
  cases n
  · simp [Nat.not_prime_zero]
  cases n
  · simp [Nat.not_prime_one]
  rw [← proper_divisors_eq_singleton_one_iff_prime]
  refine' ⟨fun h => _, fun h => h.symm ▸ sum_singleton⟩
  rw [@eq_comm (Finset ℕ) _ _]
  apply
    eq_proper_divisors_of_subset_of_sum_eq_sum
      (singleton_subset_iff.2
        (one_mem_proper_divisors_iff_one_lt.2 (succ_lt_succ (Nat.succ_pos _))))
      (Eq.trans sum_singleton h.symm)
#align nat.sum_proper_divisors_eq_one_iff_prime Nat.sum_properDivisors_eq_one_iff_prime

theorem mem_properDivisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) {x : ℕ} :
    x ∈ properDivisors (p ^ k) ↔ ∃ (j : ℕ)(H : j < k), x = p ^ j :=
  by
  rw [mem_proper_divisors, Nat.dvd_prime_pow pp, ← exists_and_right]
  simp only [exists_prop, and_assoc']
  apply exists_congr
  intro a
  constructor <;> intro h
  · rcases h with ⟨h_left, rfl, h_right⟩
    rwa [pow_lt_pow_iff pp.one_lt] at h_right
    simpa
  · rcases h with ⟨h_left, rfl⟩
    rwa [pow_lt_pow_iff pp.one_lt]
    simp [h_left, le_of_lt]
#align nat.mem_proper_divisors_prime_pow Nat.mem_properDivisors_prime_pow

theorem properDivisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) :
    properDivisors (p ^ k) = (Finset.range k).map ⟨pow p, pow_right_injective pp.two_le⟩ :=
  by
  ext
  simp [mem_proper_divisors_prime_pow, pp, Nat.lt_succ_iff, @eq_comm _ a]
#align nat.proper_divisors_prime_pow Nat.properDivisors_prime_pow

@[simp, to_additive]
theorem prod_properDivisors_prime_pow {α : Type _} [CommMonoid α] {k p : ℕ} {f : ℕ → α}
    (h : p.Prime) : (∏ x in (p ^ k).properDivisors, f x) = ∏ x in range k, f (p ^ x) := by
  simp [h, proper_divisors_prime_pow]
#align nat.prod_proper_divisors_prime_pow Nat.prod_properDivisors_prime_pow
#align nat.sum_proper_divisors_prime_nsmul Nat.sum_properDivisors_prime_nsmul

@[simp, to_additive sum_divisors_prime_pow]
theorem prod_divisors_prime_pow {α : Type _} [CommMonoid α] {k p : ℕ} {f : ℕ → α} (h : p.Prime) :
    (∏ x in (p ^ k).divisors, f x) = ∏ x in range (k + 1), f (p ^ x) := by
  simp [h, divisors_prime_pow]
#align nat.prod_divisors_prime_pow Nat.prod_divisors_prime_pow
#align nat.sum_divisors_prime_pow Nat.sum_divisors_prime_pow

@[to_additive]
theorem prod_divisorsAntidiagonal {M : Type _} [CommMonoid M] (f : ℕ → ℕ → M) {n : ℕ} :
    (∏ i in n.divisorsAntidiagonal, f i.1 i.2) = ∏ i in n.divisors, f i (n / i) :=
  by
  rw [← map_div_right_divisors, Finset.prod_map]
  rfl
#align nat.prod_divisors_antidiagonal Nat.prod_divisorsAntidiagonal
#align nat.sum_divisors_antidiagonal Nat.sum_divisorsAntidiagonal

@[to_additive]
theorem prod_divisors_antidiagonal' {M : Type _} [CommMonoid M] (f : ℕ → ℕ → M) {n : ℕ} :
    (∏ i in n.divisorsAntidiagonal, f i.1 i.2) = ∏ i in n.divisors, f (n / i) i :=
  by
  rw [← map_swap_divisors_antidiagonal, Finset.prod_map]
  exact prod_divisors_antidiagonal fun i j => f j i
#align nat.prod_divisors_antidiagonal' Nat.prod_divisors_antidiagonal'
#align nat.sum_divisors_antidiagonal' Nat.sum_divisors_antidiagonal'

/-- The factors of `n` are the prime divisors -/
theorem prime_divisors_eq_to_filter_divisors_prime (n : ℕ) :
    n.factors.toFinset = (divisors n).filter Prime :=
  by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  · ext q
    simpa [hn, hn.ne', mem_factors] using and_comm' (Prime q) (q ∣ n)
#align nat.prime_divisors_eq_to_filter_divisors_prime Nat.prime_divisors_eq_to_filter_divisors_prime

@[simp]
theorem image_div_divisors_eq_divisors (n : ℕ) :
    image (fun x : ℕ => n / x) n.divisors = n.divisors :=
  by
  by_cases hn : n = 0; · simp [hn]
  ext
  constructor
  · rw [mem_image]
    rintro ⟨x, hx1, hx2⟩
    rw [mem_divisors] at *
    refine' ⟨_, hn⟩
    rw [← hx2]
    exact div_dvd_of_dvd hx1.1
  · rw [mem_divisors, mem_image]
    rintro ⟨h1, -⟩
    exact ⟨n / a, mem_divisors.mpr ⟨div_dvd_of_dvd h1, hn⟩, Nat.div_div_self h1 hn⟩
#align nat.image_div_divisors_eq_divisors Nat.image_div_divisors_eq_divisors

@[simp, to_additive sum_div_divisors]
theorem prod_div_divisors {α : Type _} [CommMonoid α] (n : ℕ) (f : ℕ → α) :
    (∏ d in n.divisors, f (n / d)) = n.divisors.Prod f :=
  by
  by_cases hn : n = 0; · simp [hn]
  rw [← prod_image]
  · exact prod_congr (image_div_divisors_eq_divisors n) (by simp)
  · intro x hx y hy h
    rw [mem_divisors] at hx hy
    exact (div_eq_iff_eq_of_dvd_dvd hn hx.1 hy.1).mp h
#align nat.prod_div_divisors Nat.prod_div_divisors
#align nat.sum_div_divisors Nat.sum_div_divisors

end Nat


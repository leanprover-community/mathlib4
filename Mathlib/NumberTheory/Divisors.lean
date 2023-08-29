/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Factors

#align_import number_theory.divisors from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Divisor Finsets

This file defines sets of divisors of a natural number. This is particularly useful as background
for defining Dirichlet convolution.

## Main Definitions
Let `n : ℕ`. All of the following definitions are in the `Nat` namespace:
 * `divisors n` is the `Finset` of natural numbers that divide `n`.
 * `properDivisors n` is the `Finset` of natural numbers that divide `n`, other than `n`.
 * `divisorsAntidiagonal n` is the `Finset` of pairs `(x,y)` such that `x * y = n`.
 * `Perfect n` is true when `n` is positive and the sum of `properDivisors n` is `n`.

## Implementation details
 * `divisors 0`, `properDivisors 0`, and `divisorsAntidiagonal 0` are defined to be `∅`.

## Tags
divisors, perfect numbers

-/


open BigOperators Classical Finset

namespace Nat

variable (n : ℕ)

/-- `divisors n` is the `Finset` of divisors of `n`. As a special case, `divisors 0 = ∅`. -/
def divisors : Finset ℕ :=
  Finset.filter (fun x : ℕ => x ∣ n) (Finset.Ico 1 (n + 1))
#align nat.divisors Nat.divisors

/-- `properDivisors n` is the `Finset` of divisors of `n`, other than `n`.
  As a special case, `properDivisors 0 = ∅`. -/
def properDivisors : Finset ℕ :=
  Finset.filter (fun x : ℕ => x ∣ n) (Finset.Ico 1 n)
#align nat.proper_divisors Nat.properDivisors

/-- `divisorsAntidiagonal n` is the `Finset` of pairs `(x,y)` such that `x * y = n`.
  As a special case, `divisorsAntidiagonal 0 = ∅`. -/
def divisorsAntidiagonal : Finset (ℕ × ℕ) :=
  Finset.filter (fun x => x.fst * x.snd = n) (Ico 1 (n + 1) ×ˢ Ico 1 (n + 1))
#align nat.divisors_antidiagonal Nat.divisorsAntidiagonal

variable {n}

@[simp]
theorem filter_dvd_eq_divisors (h : n ≠ 0) : (Finset.range n.succ).filter (· ∣ n) = n.divisors := by
  ext
  -- ⊢ a✝ ∈ filter (fun x => x ∣ n) (range (succ n)) ↔ a✝ ∈ divisors n
  simp only [divisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  -- ⊢ a✝ ∣ n → a✝ < succ n → 1 ≤ a✝
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)
  -- 🎉 no goals
#align nat.filter_dvd_eq_divisors Nat.filter_dvd_eq_divisors

@[simp]
theorem filter_dvd_eq_properDivisors (h : n ≠ 0) :
    (Finset.range n).filter (· ∣ n) = n.properDivisors := by
  ext
  -- ⊢ a✝ ∈ filter (fun x => x ∣ n) (range n) ↔ a✝ ∈ properDivisors n
  simp only [properDivisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  -- ⊢ a✝ ∣ n → a✝ < n → 1 ≤ a✝
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)
  -- 🎉 no goals
#align nat.filter_dvd_eq_proper_divisors Nat.filter_dvd_eq_properDivisors

theorem properDivisors.not_self_mem : ¬n ∈ properDivisors n := by simp [properDivisors]
                                                                  -- 🎉 no goals
#align nat.proper_divisors.not_self_mem Nat.properDivisors.not_self_mem

@[simp]
theorem mem_properDivisors {m : ℕ} : n ∈ properDivisors m ↔ n ∣ m ∧ n < m := by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [properDivisors]
  -- ⊢ n ∈ properDivisors 0 ↔ n ∣ 0 ∧ n < 0
                                         -- 🎉 no goals
  simp only [and_comm, ← filter_dvd_eq_properDivisors hm, mem_filter, mem_range]
  -- 🎉 no goals
#align nat.mem_proper_divisors Nat.mem_properDivisors

theorem insert_self_properDivisors (h : n ≠ 0) : insert n (properDivisors n) = divisors n := by
  rw [divisors, properDivisors, Ico_succ_right_eq_insert_Ico (one_le_iff_ne_zero.2 h),
    Finset.filter_insert, if_pos (dvd_refl n)]
#align nat.insert_self_proper_divisors Nat.insert_self_properDivisors

theorem cons_self_properDivisors (h : n ≠ 0) :
    cons n (properDivisors n) properDivisors.not_self_mem = divisors n := by
  rw [cons_eq_insert, insert_self_properDivisors h]
  -- 🎉 no goals
#align nat.cons_self_proper_divisors Nat.cons_self_properDivisors

@[simp]
theorem mem_divisors {m : ℕ} : n ∈ divisors m ↔ n ∣ m ∧ m ≠ 0 := by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [divisors]
  -- ⊢ n ∈ divisors 0 ↔ n ∣ 0 ∧ 0 ≠ 0
                                         -- 🎉 no goals
  simp only [hm, Ne.def, not_false_iff, and_true_iff, ← filter_dvd_eq_divisors hm, mem_filter,
    mem_range, and_iff_right_iff_imp, lt_succ_iff]
  exact le_of_dvd hm.bot_lt
  -- 🎉 no goals
#align nat.mem_divisors Nat.mem_divisors

theorem one_mem_divisors : 1 ∈ divisors n ↔ n ≠ 0 := by simp
                                                        -- 🎉 no goals
#align nat.one_mem_divisors Nat.one_mem_divisors

theorem mem_divisors_self (n : ℕ) (h : n ≠ 0) : n ∈ n.divisors :=
  mem_divisors.2 ⟨dvd_rfl, h⟩
#align nat.mem_divisors_self Nat.mem_divisors_self

theorem dvd_of_mem_divisors {m : ℕ} (h : n ∈ divisors m) : n ∣ m := by
  cases m
  -- ⊢ n ∣ zero
  · apply dvd_zero
    -- 🎉 no goals
  · simp [mem_divisors.1 h]
    -- 🎉 no goals
#align nat.dvd_of_mem_divisors Nat.dvd_of_mem_divisors

@[simp]
theorem mem_divisorsAntidiagonal {x : ℕ × ℕ} :
    x ∈ divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n ≠ 0 := by
  simp only [divisorsAntidiagonal, Finset.mem_Ico, Ne.def, Finset.mem_filter, Finset.mem_product]
  -- ⊢ ((1 ≤ x.fst ∧ x.fst < n + 1) ∧ 1 ≤ x.snd ∧ x.snd < n + 1) ∧ x.fst * x.snd =  …
  rw [and_comm]
  -- ⊢ x.fst * x.snd = n ∧ (1 ≤ x.fst ∧ x.fst < n + 1) ∧ 1 ≤ x.snd ∧ x.snd < n + 1  …
  apply and_congr_right
  -- ⊢ x.fst * x.snd = n → ((1 ≤ x.fst ∧ x.fst < n + 1) ∧ 1 ≤ x.snd ∧ x.snd < n + 1 …
  rintro rfl
  -- ⊢ (1 ≤ x.fst ∧ x.fst < x.fst * x.snd + 1) ∧ 1 ≤ x.snd ∧ x.snd < x.fst * x.snd  …
  constructor <;> intro h
  -- ⊢ (1 ≤ x.fst ∧ x.fst < x.fst * x.snd + 1) ∧ 1 ≤ x.snd ∧ x.snd < x.fst * x.snd  …
                  -- ⊢ ¬x.fst * x.snd = 0
                  -- ⊢ (1 ≤ x.fst ∧ x.fst < x.fst * x.snd + 1) ∧ 1 ≤ x.snd ∧ x.snd < x.fst * x.snd  …
  · contrapose! h
    -- ⊢ 1 ≤ x.fst ∧ x.fst < x.fst * x.snd + 1 → 1 ≤ x.snd → x.fst * x.snd + 1 ≤ x.snd
    simp [h]
    -- 🎉 no goals
  · rw [Nat.lt_add_one_iff, Nat.lt_add_one_iff]
    -- ⊢ (1 ≤ x.fst ∧ x.fst ≤ x.fst * x.snd) ∧ 1 ≤ x.snd ∧ x.snd ≤ x.fst * x.snd
    rw [mul_eq_zero, not_or] at h
    -- ⊢ (1 ≤ x.fst ∧ x.fst ≤ x.fst * x.snd) ∧ 1 ≤ x.snd ∧ x.snd ≤ x.fst * x.snd
    simp only [succ_le_of_lt (Nat.pos_of_ne_zero h.1), succ_le_of_lt (Nat.pos_of_ne_zero h.2),
      true_and_iff]
    exact
      ⟨le_mul_of_pos_right (Nat.pos_of_ne_zero h.2), le_mul_of_pos_left (Nat.pos_of_ne_zero h.1)⟩
#align nat.mem_divisors_antidiagonal Nat.mem_divisorsAntidiagonal

-- Porting note: Redundant binder annotation update
-- variable {n}

theorem divisor_le {m : ℕ} : n ∈ divisors m → n ≤ m := by
  cases' m with m
  -- ⊢ n ∈ divisors zero → n ≤ zero
  · simp
    -- 🎉 no goals
  · simp only [mem_divisors, Nat.succ_ne_zero m, and_true_iff, Ne.def, not_false_iff]
    -- ⊢ n ∣ succ m → n ≤ succ m
    exact Nat.le_of_dvd (Nat.succ_pos m)
    -- 🎉 no goals
#align nat.divisor_le Nat.divisor_le

theorem divisors_subset_of_dvd {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) : divisors m ⊆ divisors n :=
  Finset.subset_iff.2 fun _x hx => Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hx).1.trans h, hzero⟩
#align nat.divisors_subset_of_dvd Nat.divisors_subset_of_dvd

theorem divisors_subset_properDivisors {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) (hdiff : m ≠ n) :
    divisors m ⊆ properDivisors n := by
  apply Finset.subset_iff.2
  -- ⊢ ∀ ⦃x : ℕ⦄, x ∈ divisors m → x ∈ properDivisors n
  intro x hx
  -- ⊢ x ∈ properDivisors n
  exact
    Nat.mem_properDivisors.2
      ⟨(Nat.mem_divisors.1 hx).1.trans h,
        lt_of_le_of_lt (divisor_le hx)
          (lt_of_le_of_ne (divisor_le (Nat.mem_divisors.2 ⟨h, hzero⟩)) hdiff)⟩
#align nat.divisors_subset_proper_divisors Nat.divisors_subset_properDivisors

@[simp]
theorem divisors_zero : divisors 0 = ∅ := by
  ext
  -- ⊢ a✝ ∈ divisors 0 ↔ a✝ ∈ ∅
  simp
  -- 🎉 no goals
#align nat.divisors_zero Nat.divisors_zero

@[simp]
theorem properDivisors_zero : properDivisors 0 = ∅ := by
  ext
  -- ⊢ a✝ ∈ properDivisors 0 ↔ a✝ ∈ ∅
  simp
  -- 🎉 no goals
#align nat.proper_divisors_zero Nat.properDivisors_zero

theorem properDivisors_subset_divisors : properDivisors n ⊆ divisors n :=
  filter_subset_filter _ <| Ico_subset_Ico_right n.le_succ
#align nat.proper_divisors_subset_divisors Nat.properDivisors_subset_divisors

@[simp]
theorem divisors_one : divisors 1 = {1} := by
  ext
  -- ⊢ a✝ ∈ divisors 1 ↔ a✝ ∈ {1}
  simp
  -- 🎉 no goals
#align nat.divisors_one Nat.divisors_one

@[simp]
theorem properDivisors_one : properDivisors 1 = ∅ := by rw [properDivisors, Ico_self, filter_empty]
                                                        -- 🎉 no goals
#align nat.proper_divisors_one Nat.properDivisors_one

theorem pos_of_mem_divisors {m : ℕ} (h : m ∈ n.divisors) : 0 < m := by
  cases m
  -- ⊢ 0 < zero
  · rw [mem_divisors, zero_eq, zero_dvd_iff (a := n)] at h
    -- ⊢ 0 < zero
    cases h.2 h.1
    -- 🎉 no goals
  apply Nat.succ_pos
  -- 🎉 no goals
#align nat.pos_of_mem_divisors Nat.pos_of_mem_divisors

theorem pos_of_mem_properDivisors {m : ℕ} (h : m ∈ n.properDivisors) : 0 < m :=
  pos_of_mem_divisors (properDivisors_subset_divisors h)
#align nat.pos_of_mem_proper_divisors Nat.pos_of_mem_properDivisors

theorem one_mem_properDivisors_iff_one_lt : 1 ∈ n.properDivisors ↔ 1 < n := by
  rw [mem_properDivisors, and_iff_right (one_dvd _)]
  -- 🎉 no goals
#align nat.one_mem_proper_divisors_iff_one_lt Nat.one_mem_properDivisors_iff_one_lt

@[simp]
theorem divisorsAntidiagonal_zero : divisorsAntidiagonal 0 = ∅ := by
  ext
  -- ⊢ a✝ ∈ divisorsAntidiagonal 0 ↔ a✝ ∈ ∅
  simp
  -- 🎉 no goals
#align nat.divisors_antidiagonal_zero Nat.divisorsAntidiagonal_zero

@[simp]
theorem divisorsAntidiagonal_one : divisorsAntidiagonal 1 = {(1, 1)} := by
  ext
  -- ⊢ a✝ ∈ divisorsAntidiagonal 1 ↔ a✝ ∈ {(1, 1)}
  simp [mul_eq_one, Prod.ext_iff]
  -- 🎉 no goals
#align nat.divisors_antidiagonal_one Nat.divisorsAntidiagonal_one

/- Porting note: simpnf linter; added aux lemma below
Left-hand side simplifies from
  Prod.swap x ∈ Nat.divisorsAntidiagonal n
to
  x.snd * x.fst = n ∧ ¬n = 0-/
-- @[simp]
theorem swap_mem_divisorsAntidiagonal {x : ℕ × ℕ} :
    x.swap ∈ divisorsAntidiagonal n ↔ x ∈ divisorsAntidiagonal n := by
  rw [mem_divisorsAntidiagonal, mem_divisorsAntidiagonal, mul_comm, Prod.swap]
  -- 🎉 no goals
#align nat.swap_mem_divisors_antidiagonal Nat.swap_mem_divisorsAntidiagonal

-- Porting note: added below thm to replace the simp from the previous thm
@[simp]
theorem swap_mem_divisorsAntidiagonal_aux {x : ℕ × ℕ} :
    x.snd * x.fst = n ∧ ¬n = 0 ↔ x ∈ divisorsAntidiagonal n := by
  rw [mem_divisorsAntidiagonal, mul_comm]
  -- 🎉 no goals

theorem fst_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisorsAntidiagonal n) :
    x.fst ∈ divisors n := by
  rw [mem_divisorsAntidiagonal] at h
  -- ⊢ x.fst ∈ divisors n
  simp [Dvd.intro _ h.1, h.2]
  -- 🎉 no goals
#align nat.fst_mem_divisors_of_mem_antidiagonal Nat.fst_mem_divisors_of_mem_antidiagonal

theorem snd_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisorsAntidiagonal n) :
    x.snd ∈ divisors n := by
  rw [mem_divisorsAntidiagonal] at h
  -- ⊢ x.snd ∈ divisors n
  simp [Dvd.intro_left _ h.1, h.2]
  -- 🎉 no goals
#align nat.snd_mem_divisors_of_mem_antidiagonal Nat.snd_mem_divisors_of_mem_antidiagonal

@[simp]
theorem map_swap_divisorsAntidiagonal :
    (divisorsAntidiagonal n).map (Equiv.prodComm _ _).toEmbedding = divisorsAntidiagonal n := by
  rw [← coe_inj, coe_map, Equiv.coe_toEmbedding, Equiv.coe_prodComm,
    Set.image_swap_eq_preimage_swap]
  ext
  -- ⊢ x✝ ∈ Prod.swap ⁻¹' ↑(divisorsAntidiagonal n) ↔ x✝ ∈ ↑(divisorsAntidiagonal n)
  exact swap_mem_divisorsAntidiagonal
  -- 🎉 no goals
#align nat.map_swap_divisors_antidiagonal Nat.map_swap_divisorsAntidiagonal

@[simp]
theorem image_fst_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.fst = divisors n := by
  ext
  -- ⊢ a✝ ∈ image Prod.fst (divisorsAntidiagonal n) ↔ a✝ ∈ divisors n
  simp [Dvd.dvd, @eq_comm _ n (_ * _)]
  -- 🎉 no goals
#align nat.image_fst_divisors_antidiagonal Nat.image_fst_divisorsAntidiagonal

@[simp]
theorem image_snd_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.snd = divisors n := by
  rw [← map_swap_divisorsAntidiagonal, map_eq_image, image_image]
  -- ⊢ image (Prod.snd ∘ ↑(Equiv.toEmbedding (Equiv.prodComm ℕ ℕ))) (divisorsAntidi …
  exact image_fst_divisorsAntidiagonal
  -- 🎉 no goals
#align nat.image_snd_divisors_antidiagonal Nat.image_snd_divisorsAntidiagonal

theorem map_div_right_divisors :
    n.divisors.map ⟨fun d => (d, n / d), fun p₁ p₂ => congr_arg Prod.fst⟩ =
      n.divisorsAntidiagonal := by
  ext ⟨d, nd⟩
  -- ⊢ (d, nd) ∈ map { toFun := fun d => (d, n / d), inj' := (_ : ∀ (p₁ p₂ : ℕ), (f …
  simp only [mem_map, mem_divisorsAntidiagonal, Function.Embedding.coeFn_mk, mem_divisors,
    Prod.ext_iff, exists_prop, and_left_comm, exists_eq_left]
  constructor
  -- ⊢ (d ∣ n ∧ n ≠ 0) ∧ n / d = nd → d * nd = n ∧ n ≠ 0
  · rintro ⟨⟨⟨k, rfl⟩, hn⟩, rfl⟩
    -- ⊢ d * (d * k / d) = d * k ∧ d * k ≠ 0
    rw [Nat.mul_div_cancel_left _ (left_ne_zero_of_mul hn).bot_lt]
    -- ⊢ d * k = d * k ∧ d * k ≠ 0
    exact ⟨rfl, hn⟩
    -- 🎉 no goals
  · rintro ⟨rfl, hn⟩
    -- ⊢ (d ∣ d * nd ∧ d * nd ≠ 0) ∧ d * nd / d = nd
    exact ⟨⟨dvd_mul_right _ _, hn⟩, Nat.mul_div_cancel_left _ (left_ne_zero_of_mul hn).bot_lt⟩
    -- 🎉 no goals
#align nat.map_div_right_divisors Nat.map_div_right_divisors

theorem map_div_left_divisors :
    n.divisors.map ⟨fun d => (n / d, d), fun p₁ p₂ => congr_arg Prod.snd⟩ =
      n.divisorsAntidiagonal := by
  apply Finset.map_injective (Equiv.prodComm _ _).toEmbedding
  -- ⊢ map (Equiv.toEmbedding (Equiv.prodComm ℕ ℕ)) (map { toFun := fun d => (n / d …
  rw [map_swap_divisorsAntidiagonal, ← map_div_right_divisors, Finset.map_map]
  -- ⊢ map (Function.Embedding.trans { toFun := fun d => (n / d, d), inj' := (_ : ∀ …
  rfl
  -- 🎉 no goals
#align nat.map_div_left_divisors Nat.map_div_left_divisors

theorem sum_divisors_eq_sum_properDivisors_add_self :
    ∑ i in divisors n, i = (∑ i in properDivisors n, i) + n := by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  -- ⊢ ∑ i in divisors 0, i = ∑ i in properDivisors 0, i + 0
  · simp
    -- 🎉 no goals
  · rw [← cons_self_properDivisors hn, Finset.sum_cons, add_comm]
    -- 🎉 no goals
#align nat.sum_divisors_eq_sum_proper_divisors_add_self Nat.sum_divisors_eq_sum_properDivisors_add_self

/-- `n : ℕ` is perfect if and only the sum of the proper divisors of `n` is `n` and `n`
  is positive. -/
def Perfect (n : ℕ) : Prop :=
  ∑ i in properDivisors n, i = n ∧ 0 < n
#align nat.perfect Nat.Perfect

theorem perfect_iff_sum_properDivisors (h : 0 < n) : Perfect n ↔ ∑ i in properDivisors n, i = n :=
  and_iff_left h
#align nat.perfect_iff_sum_proper_divisors Nat.perfect_iff_sum_properDivisors

theorem perfect_iff_sum_divisors_eq_two_mul (h : 0 < n) :
    Perfect n ↔ ∑ i in divisors n, i = 2 * n := by
  rw [perfect_iff_sum_properDivisors h, sum_divisors_eq_sum_properDivisors_add_self, two_mul]
  -- ⊢ ∑ i in properDivisors n, i = n ↔ ∑ i in properDivisors n, i + n = n + n
  constructor <;> intro h
  -- ⊢ ∑ i in properDivisors n, i = n → ∑ i in properDivisors n, i + n = n + n
                  -- ⊢ ∑ i in properDivisors n, i + n = n + n
                  -- ⊢ ∑ i in properDivisors n, i = n
  · rw [h]
    -- 🎉 no goals
  · apply add_right_cancel h
    -- 🎉 no goals
#align nat.perfect_iff_sum_divisors_eq_two_mul Nat.perfect_iff_sum_divisors_eq_two_mul

theorem mem_divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) {x : ℕ} :
    x ∈ divisors (p ^ k) ↔ ∃ (j : ℕ) (_ : j ≤ k), x = p ^ j := by
  rw [mem_divisors, Nat.dvd_prime_pow pp, and_iff_left (ne_of_gt (pow_pos pp.pos k))]
  -- ⊢ (∃ k_1, k_1 ≤ k ∧ x = p ^ k_1) ↔ ∃ j x_1, x = p ^ j
  simp
  -- 🎉 no goals
#align nat.mem_divisors_prime_pow Nat.mem_divisors_prime_pow

theorem Prime.divisors {p : ℕ} (pp : p.Prime) : divisors p = {1, p} := by
  ext
  -- ⊢ a✝ ∈ Nat.divisors p ↔ a✝ ∈ {1, p}
  rw [mem_divisors, dvd_prime pp, and_iff_left pp.ne_zero, Finset.mem_insert, Finset.mem_singleton]
  -- 🎉 no goals
#align nat.prime.divisors Nat.Prime.divisors

theorem Prime.properDivisors {p : ℕ} (pp : p.Prime) : properDivisors p = {1} := by
  rw [← erase_insert properDivisors.not_self_mem, insert_self_properDivisors pp.ne_zero,
    pp.divisors, pair_comm, erase_insert fun con => pp.ne_one (mem_singleton.1 con)]
#align nat.prime.proper_divisors Nat.Prime.properDivisors

-- Porting note: Specified pow to Nat.pow
theorem divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) :
    divisors (p ^ k) = (Finset.range (k + 1)).map ⟨Nat.pow p, pow_right_injective pp.two_le⟩ := by
  ext a
  -- ⊢ a ∈ divisors (p ^ k) ↔ a ∈ map { toFun := Nat.pow p, inj' := (_ : Function.I …
  simp only [mem_divisors, mem_map, mem_range, lt_succ_iff, Function.Embedding.coeFn_mk, Nat.pow_eq,
    mem_divisors_prime_pow pp k]
  have := mem_divisors_prime_pow pp k (x := a)
  -- ⊢ a ∣ p ^ k ∧ p ^ k ≠ 0 ↔ ∃ a_1, a_1 ≤ k ∧ p ^ a_1 = a
  rw [mem_divisors] at this
  -- ⊢ a ∣ p ^ k ∧ p ^ k ≠ 0 ↔ ∃ a_1, a_1 ≤ k ∧ p ^ a_1 = a
  rw [this]
  -- ⊢ (∃ j x, a = p ^ j) ↔ ∃ a_1, a_1 ≤ k ∧ p ^ a_1 = a
  refine ⟨?_, ?_⟩
  -- ⊢ (∃ j x, a = p ^ j) → ∃ a_2, a_2 ≤ k ∧ p ^ a_2 = a
  · intro h; rcases h with ⟨x, hx, hap⟩; use x; tauto
    -- ⊢ ∃ a_1, a_1 ≤ k ∧ p ^ a_1 = a
             -- ⊢ ∃ a_1, a_1 ≤ k ∧ p ^ a_1 = a
                                         -- ⊢ x ≤ k ∧ p ^ x = a
                                                -- 🎉 no goals
  · tauto
    -- 🎉 no goals
#align nat.divisors_prime_pow Nat.divisors_prime_pow

theorem eq_properDivisors_of_subset_of_sum_eq_sum {s : Finset ℕ} (hsub : s ⊆ n.properDivisors) :
    ((∑ x in s, x) = ∑ x in n.properDivisors, x) → s = n.properDivisors := by
  cases n
  -- ⊢ ∑ x in s, x = ∑ x in properDivisors zero, x → s = properDivisors zero
  · rw [properDivisors_zero, subset_empty] at hsub
    -- ⊢ ∑ x in s, x = ∑ x in properDivisors zero, x → s = properDivisors zero
    simp [hsub]
    -- 🎉 no goals
  classical
    rw [← sum_sdiff hsub]
    intro h
    apply Subset.antisymm hsub
    rw [← sdiff_eq_empty_iff_subset]
    contrapose h
    rw [← Ne.def, ← nonempty_iff_ne_empty] at h
    apply ne_of_lt
    rw [← zero_add (∑ x in s, x), ← add_assoc, add_zero]
    apply add_lt_add_right
    have hlt :=
      sum_lt_sum_of_nonempty h fun x hx => pos_of_mem_properDivisors (sdiff_subset _ _ hx)
    simp only [sum_const_zero] at hlt
    apply hlt
#align nat.eq_proper_divisors_of_subset_of_sum_eq_sum Nat.eq_properDivisors_of_subset_of_sum_eq_sum

theorem sum_properDivisors_dvd (h : (∑ x in n.properDivisors, x) ∣ n) :
    ∑ x in n.properDivisors, x = 1 ∨ ∑ x in n.properDivisors, x = n := by
  cases' n with n
  -- ⊢ ∑ x in properDivisors zero, x = 1 ∨ ∑ x in properDivisors zero, x = zero
  · simp
    -- 🎉 no goals
  · cases' n with n
    -- ⊢ ∑ x in properDivisors (succ zero), x = 1 ∨ ∑ x in properDivisors (succ zero) …
    · contrapose! h
      -- ⊢ ¬∑ x in properDivisors (succ zero), x ∣ succ zero
      simp
      -- 🎉 no goals
    · rw [or_iff_not_imp_right]
      -- ⊢ ¬∑ x in properDivisors (succ (succ n)), x = succ (succ n) → ∑ x in properDiv …
      intro ne_n
      -- ⊢ ∑ x in properDivisors (succ (succ n)), x = 1
      have hlt : ∑ x in n.succ.succ.properDivisors, x < n.succ.succ :=
        lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h) ne_n
      symm
      -- ⊢ 1 = ∑ x in properDivisors (succ (succ n)), x
      rw [← mem_singleton,
        eq_properDivisors_of_subset_of_sum_eq_sum
          (singleton_subset_iff.2 (mem_properDivisors.2 ⟨h, hlt⟩)) sum_singleton,
        mem_properDivisors]
      refine' ⟨one_dvd _, Nat.succ_lt_succ (Nat.succ_pos _)⟩
      -- 🎉 no goals
#align nat.sum_proper_divisors_dvd Nat.sum_properDivisors_dvd

@[to_additive (attr := simp)]
theorem Prime.prod_properDivisors {α : Type*} [CommMonoid α] {p : ℕ} {f : ℕ → α} (h : p.Prime) :
    ∏ x in p.properDivisors, f x = f 1 := by simp [h.properDivisors]
                                             -- 🎉 no goals
#align nat.prime.prod_proper_divisors Nat.Prime.prod_properDivisors
#align nat.prime.sum_proper_divisors Nat.Prime.sum_properDivisors

@[to_additive (attr := simp)]
theorem Prime.prod_divisors {α : Type*} [CommMonoid α] {p : ℕ} {f : ℕ → α} (h : p.Prime) :
    ∏ x in p.divisors, f x = f p * f 1 := by
  rw [← cons_self_properDivisors h.ne_zero, prod_cons, h.prod_properDivisors]
  -- 🎉 no goals
#align nat.prime.prod_divisors Nat.Prime.prod_divisors
#align nat.prime.sum_divisors Nat.Prime.sum_divisors

theorem properDivisors_eq_singleton_one_iff_prime : n.properDivisors = {1} ↔ n.Prime := by
  refine ⟨?_, ?_⟩
  -- ⊢ properDivisors n = {1} → Prime n
  · intro h
    -- ⊢ Prime n
    refine' Nat.prime_def_lt''.mpr ⟨_, fun m hdvd => _⟩
    -- ⊢ 2 ≤ n
    · match n with
      | 0 => contradiction
      | 1 => contradiction
      | Nat.succ (Nat.succ n) => simp [succ_le_succ]
    · rw [← mem_singleton, ← h, mem_properDivisors]
      -- ⊢ m ∣ n ∧ m < n ∨ m = n
      have := Nat.le_of_dvd ?_ hdvd
      -- ⊢ m ∣ n ∧ m < n ∨ m = n
      · simp [hdvd, this]
        -- ⊢ m < n ∨ m = n
        exact (le_iff_eq_or_lt.mp this).symm
        -- 🎉 no goals
      · by_contra'
        -- ⊢ False
        simp [nonpos_iff_eq_zero.mp this, this] at h
        -- 🎉 no goals
  · exact fun h => Prime.properDivisors h
    -- 🎉 no goals
#align nat.proper_divisors_eq_singleton_one_iff_prime Nat.properDivisors_eq_singleton_one_iff_prime

theorem sum_properDivisors_eq_one_iff_prime : ∑ x in n.properDivisors, x = 1 ↔ n.Prime := by
  cases' n with n
  -- ⊢ ∑ x in properDivisors zero, x = 1 ↔ Prime zero
  · simp [Nat.not_prime_zero]
    -- 🎉 no goals
  · cases n
    -- ⊢ ∑ x in properDivisors (succ zero), x = 1 ↔ Prime (succ zero)
    · simp [Nat.not_prime_one]
      -- 🎉 no goals
    · rw [← properDivisors_eq_singleton_one_iff_prime]
      -- ⊢ ∑ x in properDivisors (succ (succ n✝)), x = 1 ↔ properDivisors (succ (succ n …
      refine' ⟨fun h => _, fun h => h.symm ▸ sum_singleton⟩
      -- ⊢ properDivisors (succ (succ n✝)) = {1}
      rw [@eq_comm (Finset ℕ) _ _]
      -- ⊢ {1} = properDivisors (succ (succ n✝))
      apply
        eq_properDivisors_of_subset_of_sum_eq_sum
          (singleton_subset_iff.2
            (one_mem_properDivisors_iff_one_lt.2 (succ_lt_succ (Nat.succ_pos _))))
          (Eq.trans sum_singleton h.symm)
#align nat.sum_proper_divisors_eq_one_iff_prime Nat.sum_properDivisors_eq_one_iff_prime

theorem mem_properDivisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) {x : ℕ} :
    x ∈ properDivisors (p ^ k) ↔ ∃ (j : ℕ) (_ : j < k), x = p ^ j := by
  rw [mem_properDivisors, Nat.dvd_prime_pow pp, ← exists_and_right]
  -- ⊢ (∃ x_1, (x_1 ≤ k ∧ x = p ^ x_1) ∧ x < p ^ k) ↔ ∃ j x_1, x = p ^ j
  simp only [exists_prop, and_assoc]
  -- ⊢ (∃ x_1, x_1 ≤ k ∧ x = p ^ x_1 ∧ x < p ^ k) ↔ ∃ j, j < k ∧ x = p ^ j
  apply exists_congr
  -- ⊢ ∀ (a : ℕ), a ≤ k ∧ x = p ^ a ∧ x < p ^ k ↔ a < k ∧ x = p ^ a
  intro a
  -- ⊢ a ≤ k ∧ x = p ^ a ∧ x < p ^ k ↔ a < k ∧ x = p ^ a
  constructor <;> intro h
  -- ⊢ a ≤ k ∧ x = p ^ a ∧ x < p ^ k → a < k ∧ x = p ^ a
                  -- ⊢ a < k ∧ x = p ^ a
                  -- ⊢ a ≤ k ∧ x = p ^ a ∧ x < p ^ k
  · rcases h with ⟨_h_left, rfl, h_right⟩
    -- ⊢ a < k ∧ p ^ a = p ^ a
    rw [pow_lt_pow_iff pp.one_lt] at h_right
    -- ⊢ a < k ∧ p ^ a = p ^ a
    exact ⟨h_right, by rfl⟩
    -- 🎉 no goals
  · rcases h with ⟨h_left, rfl⟩
    -- ⊢ a ≤ k ∧ p ^ a = p ^ a ∧ p ^ a < p ^ k
    rw [pow_lt_pow_iff pp.one_lt]
    -- ⊢ a ≤ k ∧ p ^ a = p ^ a ∧ a < k
    simp [h_left, le_of_lt]
    -- 🎉 no goals
#align nat.mem_proper_divisors_prime_pow Nat.mem_properDivisors_prime_pow

-- Porting note: Specified pow to Nat.pow
theorem properDivisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) :
    properDivisors (p ^ k) = (Finset.range k).map ⟨Nat.pow p, pow_right_injective pp.two_le⟩ := by
  ext a
  -- ⊢ a ∈ properDivisors (p ^ k) ↔ a ∈ map { toFun := Nat.pow p, inj' := (_ : Func …
  simp only [mem_properDivisors, Nat.isUnit_iff, mem_map, mem_range, Function.Embedding.coeFn_mk,
    pow_eq]
  have := mem_properDivisors_prime_pow pp k (x := a)
  -- ⊢ a ∣ p ^ k ∧ a < p ^ k ↔ ∃ a_1, a_1 < k ∧ p ^ a_1 = a
  rw [mem_properDivisors] at this
  -- ⊢ a ∣ p ^ k ∧ a < p ^ k ↔ ∃ a_1, a_1 < k ∧ p ^ a_1 = a
  rw [this]
  -- ⊢ (∃ j x, a = p ^ j) ↔ ∃ a_1, a_1 < k ∧ p ^ a_1 = a
  refine ⟨?_, ?_⟩
  -- ⊢ (∃ j x, a = p ^ j) → ∃ a_2, a_2 < k ∧ p ^ a_2 = a
  · intro h; rcases h with ⟨j, hj, hap⟩; use j; tauto
    -- ⊢ ∃ a_1, a_1 < k ∧ p ^ a_1 = a
             -- ⊢ ∃ a_1, a_1 < k ∧ p ^ a_1 = a
                                         -- ⊢ j < k ∧ p ^ j = a
                                                -- 🎉 no goals
  · tauto
    -- 🎉 no goals
#align nat.proper_divisors_prime_pow Nat.properDivisors_prime_pow

@[to_additive (attr := simp)]
theorem prod_properDivisors_prime_pow {α : Type*} [CommMonoid α] {k p : ℕ} {f : ℕ → α}
    (h : p.Prime) : (∏ x in (p ^ k).properDivisors, f x) = ∏ x in range k, f (p ^ x) := by
  simp [h, properDivisors_prime_pow]
  -- 🎉 no goals
#align nat.prod_proper_divisors_prime_pow Nat.prod_properDivisors_prime_pow
#align nat.sum_proper_divisors_prime_nsmul Nat.sum_properDivisors_prime_nsmul

@[to_additive (attr := simp) sum_divisors_prime_pow]
theorem prod_divisors_prime_pow {α : Type*} [CommMonoid α] {k p : ℕ} {f : ℕ → α} (h : p.Prime) :
    (∏ x in (p ^ k).divisors, f x) = ∏ x in range (k + 1), f (p ^ x) := by
  simp [h, divisors_prime_pow]
  -- 🎉 no goals
#align nat.prod_divisors_prime_pow Nat.prod_divisors_prime_pow
#align nat.sum_divisors_prime_pow Nat.sum_divisors_prime_pow

@[to_additive]
theorem prod_divisorsAntidiagonal {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) {n : ℕ} :
    ∏ i in n.divisorsAntidiagonal, f i.1 i.2 = ∏ i in n.divisors, f i (n / i) := by
  rw [← map_div_right_divisors, Finset.prod_map]
  -- ⊢ ∏ x in divisors n, f (↑{ toFun := fun d => (d, n / d), inj' := (_ : ∀ (p₁ p₂ …
  rfl
  -- 🎉 no goals
#align nat.prod_divisors_antidiagonal Nat.prod_divisorsAntidiagonal
#align nat.sum_divisors_antidiagonal Nat.sum_divisorsAntidiagonal

@[to_additive]
theorem prod_divisorsAntidiagonal' {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) {n : ℕ} :
    ∏ i in n.divisorsAntidiagonal, f i.1 i.2 = ∏ i in n.divisors, f (n / i) i := by
  rw [← map_swap_divisorsAntidiagonal, Finset.prod_map]
  -- ⊢ ∏ x in divisorsAntidiagonal n, f (↑(Equiv.toEmbedding (Equiv.prodComm ℕ ℕ))  …
  exact prod_divisorsAntidiagonal fun i j => f j i
  -- 🎉 no goals
#align nat.prod_divisors_antidiagonal' Nat.prod_divisorsAntidiagonal'
#align nat.sum_divisors_antidiagonal' Nat.sum_divisorsAntidiagonal'

/-- The factors of `n` are the prime divisors -/
theorem prime_divisors_eq_to_filter_divisors_prime (n : ℕ) :
    n.factors.toFinset = (divisors n).filter Prime := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  -- ⊢ List.toFinset (factors 0) = filter Prime (divisors 0)
  · simp
    -- 🎉 no goals
  · ext q
    -- ⊢ q ∈ List.toFinset (factors n) ↔ q ∈ filter Prime (divisors n)
    simpa [hn, hn.ne', mem_factors] using and_comm
    -- 🎉 no goals
#align nat.prime_divisors_eq_to_filter_divisors_prime Nat.prime_divisors_eq_to_filter_divisors_prime

@[simp]
theorem image_div_divisors_eq_divisors (n : ℕ) :
    image (fun x : ℕ => n / x) n.divisors = n.divisors := by
  by_cases hn : n = 0
  -- ⊢ image (fun x => n / x) (divisors n) = divisors n
  · simp [hn]
    -- 🎉 no goals
  ext a
  -- ⊢ a ∈ image (fun x => n / x) (divisors n) ↔ a ∈ divisors n
  constructor
  -- ⊢ a ∈ image (fun x => n / x) (divisors n) → a ∈ divisors n
  · rw [mem_image]
    -- ⊢ (∃ a_1, a_1 ∈ divisors n ∧ n / a_1 = a) → a ∈ divisors n
    rintro ⟨x, hx1, hx2⟩
    -- ⊢ a ∈ divisors n
    rw [mem_divisors] at *
    -- ⊢ a ∣ n ∧ n ≠ 0
    refine' ⟨_, hn⟩
    -- ⊢ a ∣ n
    rw [← hx2]
    -- ⊢ n / x ∣ n
    exact div_dvd_of_dvd hx1.1
    -- 🎉 no goals
  · rw [mem_divisors, mem_image]
    -- ⊢ a ∣ n ∧ n ≠ 0 → ∃ a_2, a_2 ∈ divisors n ∧ n / a_2 = a
    rintro ⟨h1, -⟩
    -- ⊢ ∃ a_1, a_1 ∈ divisors n ∧ n / a_1 = a
    exact ⟨n / a, mem_divisors.mpr ⟨div_dvd_of_dvd h1, hn⟩, Nat.div_div_self h1 hn⟩
    -- 🎉 no goals
#align nat.image_div_divisors_eq_divisors Nat.image_div_divisors_eq_divisors

/- Porting note: Removed simp; simp_nf linter:
Left-hand side does not simplify, when using the simp lemma on itself.
This usually means that it will never apply. -/
@[to_additive sum_div_divisors]
theorem prod_div_divisors {α : Type*} [CommMonoid α] (n : ℕ) (f : ℕ → α) :
    (∏ d in n.divisors, f (n / d)) = n.divisors.prod f := by
  by_cases hn : n = 0; · simp [hn]
  -- ⊢ ∏ d in divisors n, f (n / d) = Finset.prod (divisors n) f
                         -- 🎉 no goals
  rw [← prod_image]
  -- ⊢ ∏ x in image (fun d => n / d) (divisors n), f x = Finset.prod (divisors n) f
  · exact prod_congr (image_div_divisors_eq_divisors n) (by simp)
    -- 🎉 no goals
  · intro x hx y hy h
    -- ⊢ x = y
    rw [mem_divisors] at hx hy
    -- ⊢ x = y
    exact (div_eq_iff_eq_of_dvd_dvd hn hx.1 hy.1).mp h
    -- 🎉 no goals
#align nat.prod_div_divisors Nat.prod_div_divisors
#align nat.sum_div_divisors Nat.sum_div_divisors

end Nat

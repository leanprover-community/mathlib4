/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Interval.Finset.Nat

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


open scoped Classical
open Finset

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
  simp only [divisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)
#align nat.filter_dvd_eq_divisors Nat.filter_dvd_eq_divisors

@[simp]
theorem filter_dvd_eq_properDivisors (h : n ≠ 0) :
    (Finset.range n).filter (· ∣ n) = n.properDivisors := by
  ext
  simp only [properDivisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)
#align nat.filter_dvd_eq_proper_divisors Nat.filter_dvd_eq_properDivisors

theorem properDivisors.not_self_mem : ¬n ∈ properDivisors n := by simp [properDivisors]
#align nat.proper_divisors.not_self_mem Nat.properDivisors.not_self_mem

@[simp]
theorem mem_properDivisors {m : ℕ} : n ∈ properDivisors m ↔ n ∣ m ∧ n < m := by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [properDivisors]
  simp only [and_comm, ← filter_dvd_eq_properDivisors hm, mem_filter, mem_range]
#align nat.mem_proper_divisors Nat.mem_properDivisors

theorem insert_self_properDivisors (h : n ≠ 0) : insert n (properDivisors n) = divisors n := by
  rw [divisors, properDivisors, Ico_succ_right_eq_insert_Ico (one_le_iff_ne_zero.2 h),
    Finset.filter_insert, if_pos (dvd_refl n)]
#align nat.insert_self_proper_divisors Nat.insert_self_properDivisors

theorem cons_self_properDivisors (h : n ≠ 0) :
    cons n (properDivisors n) properDivisors.not_self_mem = divisors n := by
  rw [cons_eq_insert, insert_self_properDivisors h]
#align nat.cons_self_proper_divisors Nat.cons_self_properDivisors

@[simp]
theorem mem_divisors {m : ℕ} : n ∈ divisors m ↔ n ∣ m ∧ m ≠ 0 := by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [divisors]
  simp only [hm, Ne, not_false_iff, and_true_iff, ← filter_dvd_eq_divisors hm, mem_filter,
    mem_range, and_iff_right_iff_imp, Nat.lt_succ_iff]
  exact le_of_dvd hm.bot_lt
#align nat.mem_divisors Nat.mem_divisors

theorem one_mem_divisors : 1 ∈ divisors n ↔ n ≠ 0 := by simp
#align nat.one_mem_divisors Nat.one_mem_divisors

theorem mem_divisors_self (n : ℕ) (h : n ≠ 0) : n ∈ n.divisors :=
  mem_divisors.2 ⟨dvd_rfl, h⟩
#align nat.mem_divisors_self Nat.mem_divisors_self

theorem dvd_of_mem_divisors {m : ℕ} (h : n ∈ divisors m) : n ∣ m := by
  cases m
  · apply dvd_zero
  · simp [mem_divisors.1 h]
#align nat.dvd_of_mem_divisors Nat.dvd_of_mem_divisors

@[simp]
theorem mem_divisorsAntidiagonal {x : ℕ × ℕ} :
    x ∈ divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n ≠ 0 := by
  simp only [divisorsAntidiagonal, Finset.mem_Ico, Ne, Finset.mem_filter, Finset.mem_product]
  rw [and_comm]
  apply and_congr_right
  rintro rfl
  constructor <;> intro h
  · contrapose! h
    simp [h]
  · rw [Nat.lt_add_one_iff, Nat.lt_add_one_iff]
    rw [mul_eq_zero, not_or] at h
    simp only [succ_le_of_lt (Nat.pos_of_ne_zero h.1), succ_le_of_lt (Nat.pos_of_ne_zero h.2),
      true_and_iff]
    exact
      ⟨Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h.2),
        Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h.1)⟩
#align nat.mem_divisors_antidiagonal Nat.mem_divisorsAntidiagonal

lemma ne_zero_of_mem_divisorsAntidiagonal {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) :
    p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  obtain ⟨hp₁, hp₂⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  exact mul_ne_zero_iff.mp (hp₁.symm ▸ hp₂)

lemma left_ne_zero_of_mem_divisorsAntidiagonal {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) :
    p.1 ≠ 0 :=
  (ne_zero_of_mem_divisorsAntidiagonal hp).1

lemma right_ne_zero_of_mem_divisorsAntidiagonal {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) :
    p.2 ≠ 0 :=
  (ne_zero_of_mem_divisorsAntidiagonal hp).2

theorem divisor_le {m : ℕ} : n ∈ divisors m → n ≤ m := by
  cases' m with m
  · simp
  · simp only [mem_divisors, Nat.succ_ne_zero m, and_true_iff, Ne, not_false_iff]
    exact Nat.le_of_dvd (Nat.succ_pos m)
#align nat.divisor_le Nat.divisor_le

theorem divisors_subset_of_dvd {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) : divisors m ⊆ divisors n :=
  Finset.subset_iff.2 fun _x hx => Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hx).1.trans h, hzero⟩
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

lemma divisors_filter_dvd_of_dvd {n m : ℕ} (hn : n ≠ 0) (hm : m ∣ n) :
    (n.divisors.filter (· ∣ m)) = m.divisors := by
  ext k
  simp_rw [mem_filter, mem_divisors]
  exact ⟨fun ⟨_, hkm⟩ ↦ ⟨hkm, ne_zero_of_dvd_ne_zero hn hm⟩, fun ⟨hk, _⟩ ↦ ⟨⟨hk.trans hm, hn⟩, hk⟩⟩

@[simp]
theorem divisors_zero : divisors 0 = ∅ := by
  ext
  simp
#align nat.divisors_zero Nat.divisors_zero

@[simp]
theorem properDivisors_zero : properDivisors 0 = ∅ := by
  ext
  simp
#align nat.proper_divisors_zero Nat.properDivisors_zero

@[simp]
lemma nonempty_divisors : (divisors n).Nonempty ↔ n ≠ 0 :=
  ⟨fun ⟨m, hm⟩ hn ↦ by simp [hn] at hm, fun hn ↦ ⟨1, one_mem_divisors.2 hn⟩⟩

@[simp]
lemma divisors_eq_empty : divisors n = ∅ ↔ n = 0 :=
  not_nonempty_iff_eq_empty.symm.trans nonempty_divisors.not_left

theorem properDivisors_subset_divisors : properDivisors n ⊆ divisors n :=
  filter_subset_filter _ <| Ico_subset_Ico_right n.le_succ
#align nat.proper_divisors_subset_divisors Nat.properDivisors_subset_divisors

@[simp]
theorem divisors_one : divisors 1 = {1} := by
  ext
  simp
#align nat.divisors_one Nat.divisors_one

@[simp]
theorem properDivisors_one : properDivisors 1 = ∅ := by rw [properDivisors, Ico_self, filter_empty]
#align nat.proper_divisors_one Nat.properDivisors_one

theorem pos_of_mem_divisors {m : ℕ} (h : m ∈ n.divisors) : 0 < m := by
  cases m
  · rw [mem_divisors, zero_dvd_iff (a := n)] at h
    cases h.2 h.1
  apply Nat.succ_pos
#align nat.pos_of_mem_divisors Nat.pos_of_mem_divisors

theorem pos_of_mem_properDivisors {m : ℕ} (h : m ∈ n.properDivisors) : 0 < m :=
  pos_of_mem_divisors (properDivisors_subset_divisors h)
#align nat.pos_of_mem_proper_divisors Nat.pos_of_mem_properDivisors

theorem one_mem_properDivisors_iff_one_lt : 1 ∈ n.properDivisors ↔ 1 < n := by
  rw [mem_properDivisors, and_iff_right (one_dvd _)]
#align nat.one_mem_proper_divisors_iff_one_lt Nat.one_mem_properDivisors_iff_one_lt

@[simp]
lemma sup_divisors_id (n : ℕ) : n.divisors.sup id = n := by
  refine le_antisymm (Finset.sup_le fun _ ↦ divisor_le) ?_
  rcases Decidable.eq_or_ne n 0 with rfl | hn
  · apply zero_le
  · exact Finset.le_sup (f := id) <| mem_divisors_self n hn

lemma one_lt_of_mem_properDivisors {m n : ℕ} (h : m ∈ n.properDivisors) : 1 < n :=
  lt_of_le_of_lt (pos_of_mem_properDivisors h) (mem_properDivisors.1 h).2

lemma one_lt_div_of_mem_properDivisors {m n : ℕ} (h : m ∈ n.properDivisors) :
    1 < n / m := by
  obtain ⟨h_dvd, h_lt⟩ := mem_properDivisors.mp h
  rwa [Nat.lt_div_iff_mul_lt h_dvd, mul_one]

/-- See also `Nat.mem_properDivisors`. -/
lemma mem_properDivisors_iff_exists {m n : ℕ} (hn : n ≠ 0) :
    m ∈ n.properDivisors ↔ ∃ k > 1, n = m * k := by
  refine ⟨fun h ↦ ⟨n / m, one_lt_div_of_mem_properDivisors h, ?_⟩, ?_⟩
  · exact (Nat.mul_div_cancel' (mem_properDivisors.mp h).1).symm
  · rintro ⟨k, hk, rfl⟩
    rw [mul_ne_zero_iff] at hn
    exact mem_properDivisors.mpr ⟨⟨k, rfl⟩, lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hn.1) hk⟩

@[simp]
lemma nonempty_properDivisors : n.properDivisors.Nonempty ↔ 1 < n :=
  ⟨fun ⟨_m, hm⟩ ↦ one_lt_of_mem_properDivisors hm, fun hn ↦
    ⟨1, one_mem_properDivisors_iff_one_lt.2 hn⟩⟩

@[simp]
lemma properDivisors_eq_empty : n.properDivisors = ∅ ↔ n ≤ 1 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_properDivisors, not_lt]

@[simp]
theorem divisorsAntidiagonal_zero : divisorsAntidiagonal 0 = ∅ := by
  ext
  simp
#align nat.divisors_antidiagonal_zero Nat.divisorsAntidiagonal_zero

@[simp]
theorem divisorsAntidiagonal_one : divisorsAntidiagonal 1 = {(1, 1)} := by
  ext
  simp [mul_eq_one, Prod.ext_iff]
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
#align nat.swap_mem_divisors_antidiagonal Nat.swap_mem_divisorsAntidiagonal

-- Porting note: added below thm to replace the simp from the previous thm
@[simp]
theorem swap_mem_divisorsAntidiagonal_aux {x : ℕ × ℕ} :
    x.snd * x.fst = n ∧ ¬n = 0 ↔ x ∈ divisorsAntidiagonal n := by
  rw [mem_divisorsAntidiagonal, mul_comm]

theorem fst_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisorsAntidiagonal n) :
    x.fst ∈ divisors n := by
  rw [mem_divisorsAntidiagonal] at h
  simp [Dvd.intro _ h.1, h.2]
#align nat.fst_mem_divisors_of_mem_antidiagonal Nat.fst_mem_divisors_of_mem_antidiagonal

theorem snd_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisorsAntidiagonal n) :
    x.snd ∈ divisors n := by
  rw [mem_divisorsAntidiagonal] at h
  simp [Dvd.intro_left _ h.1, h.2]
#align nat.snd_mem_divisors_of_mem_antidiagonal Nat.snd_mem_divisors_of_mem_antidiagonal

@[simp]
theorem map_swap_divisorsAntidiagonal :
    (divisorsAntidiagonal n).map (Equiv.prodComm _ _).toEmbedding = divisorsAntidiagonal n := by
  rw [← coe_inj, coe_map, Equiv.coe_toEmbedding, Equiv.coe_prodComm,
    Set.image_swap_eq_preimage_swap]
  ext
  exact swap_mem_divisorsAntidiagonal
#align nat.map_swap_divisors_antidiagonal Nat.map_swap_divisorsAntidiagonal

@[simp]
theorem image_fst_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.fst = divisors n := by
  ext
  simp [Dvd.dvd, @eq_comm _ n (_ * _)]
#align nat.image_fst_divisors_antidiagonal Nat.image_fst_divisorsAntidiagonal

@[simp]
theorem image_snd_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.snd = divisors n := by
  rw [← map_swap_divisorsAntidiagonal, map_eq_image, image_image]
  exact image_fst_divisorsAntidiagonal
#align nat.image_snd_divisors_antidiagonal Nat.image_snd_divisorsAntidiagonal

theorem map_div_right_divisors :
    n.divisors.map ⟨fun d => (d, n / d), fun p₁ p₂ => congr_arg Prod.fst⟩ =
      n.divisorsAntidiagonal := by
  ext ⟨d, nd⟩
  simp only [mem_map, mem_divisorsAntidiagonal, Function.Embedding.coeFn_mk, mem_divisors,
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
      n.divisorsAntidiagonal := by
  apply Finset.map_injective (Equiv.prodComm _ _).toEmbedding
  ext
  rw [map_swap_divisorsAntidiagonal, ← map_div_right_divisors, Finset.map_map]
  simp
#align nat.map_div_left_divisors Nat.map_div_left_divisors

theorem sum_divisors_eq_sum_properDivisors_add_self :
    ∑ i ∈ divisors n, i = (∑ i ∈ properDivisors n, i) + n := by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  · rw [← cons_self_properDivisors hn, Finset.sum_cons, add_comm]
#align nat.sum_divisors_eq_sum_proper_divisors_add_self Nat.sum_divisors_eq_sum_properDivisors_add_self

/-- `n : ℕ` is perfect if and only the sum of the proper divisors of `n` is `n` and `n`
  is positive. -/
def Perfect (n : ℕ) : Prop :=
  ∑ i ∈ properDivisors n, i = n ∧ 0 < n
#align nat.perfect Nat.Perfect

theorem perfect_iff_sum_properDivisors (h : 0 < n) : Perfect n ↔ ∑ i ∈ properDivisors n, i = n :=
  and_iff_left h
#align nat.perfect_iff_sum_proper_divisors Nat.perfect_iff_sum_properDivisors

theorem perfect_iff_sum_divisors_eq_two_mul (h : 0 < n) :
    Perfect n ↔ ∑ i ∈ divisors n, i = 2 * n := by
  rw [perfect_iff_sum_properDivisors h, sum_divisors_eq_sum_properDivisors_add_self, two_mul]
  constructor <;> intro h
  · rw [h]
  · apply add_right_cancel h
#align nat.perfect_iff_sum_divisors_eq_two_mul Nat.perfect_iff_sum_divisors_eq_two_mul

theorem mem_divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) {x : ℕ} :
    x ∈ divisors (p ^ k) ↔ ∃ j ≤ k, x = p ^ j := by
  rw [mem_divisors, Nat.dvd_prime_pow pp, and_iff_left (ne_of_gt (pow_pos pp.pos k))]
#align nat.mem_divisors_prime_pow Nat.mem_divisors_prime_pow

theorem Prime.divisors {p : ℕ} (pp : p.Prime) : divisors p = {1, p} := by
  ext
  rw [mem_divisors, dvd_prime pp, and_iff_left pp.ne_zero, Finset.mem_insert, Finset.mem_singleton]
#align nat.prime.divisors Nat.Prime.divisors

theorem Prime.properDivisors {p : ℕ} (pp : p.Prime) : properDivisors p = {1} := by
  rw [← erase_insert properDivisors.not_self_mem, insert_self_properDivisors pp.ne_zero,
    pp.divisors, pair_comm, erase_insert fun con => pp.ne_one (mem_singleton.1 con)]
#align nat.prime.proper_divisors Nat.Prime.properDivisors

theorem divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) :
    divisors (p ^ k) = (Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_injective pp.two_le⟩ := by
  ext a
  rw [mem_divisors_prime_pow pp]
  simp [Nat.lt_succ, eq_comm]
#align nat.divisors_prime_pow Nat.divisors_prime_pow

theorem divisors_injective : Function.Injective divisors :=
  Function.LeftInverse.injective sup_divisors_id

@[simp]
theorem divisors_inj {a b : ℕ} : a.divisors = b.divisors ↔ a = b :=
  divisors_injective.eq_iff

theorem eq_properDivisors_of_subset_of_sum_eq_sum {s : Finset ℕ} (hsub : s ⊆ n.properDivisors) :
    ((∑ x ∈ s, x) = ∑ x ∈ n.properDivisors, x) → s = n.properDivisors := by
  cases n
  · rw [properDivisors_zero, subset_empty] at hsub
    simp [hsub]
  classical
    rw [← sum_sdiff hsub]
    intro h
    apply Subset.antisymm hsub
    rw [← sdiff_eq_empty_iff_subset]
    contrapose h
    rw [← Ne, ← nonempty_iff_ne_empty] at h
    apply ne_of_lt
    rw [← zero_add (∑ x ∈ s, x), ← add_assoc, add_zero]
    apply add_lt_add_right
    have hlt :=
      sum_lt_sum_of_nonempty h fun x hx => pos_of_mem_properDivisors (sdiff_subset hx)
    simp only [sum_const_zero] at hlt
    apply hlt
#align nat.eq_proper_divisors_of_subset_of_sum_eq_sum Nat.eq_properDivisors_of_subset_of_sum_eq_sum

theorem sum_properDivisors_dvd (h : (∑ x ∈ n.properDivisors, x) ∣ n) :
    ∑ x ∈ n.properDivisors, x = 1 ∨ ∑ x ∈ n.properDivisors, x = n := by
  cases' n with n
  · simp
  · cases' n with n
    · simp at h
    · rw [or_iff_not_imp_right]
      intro ne_n
      have hlt : ∑ x ∈ n.succ.succ.properDivisors, x < n.succ.succ :=
        lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h) ne_n
      symm
      rw [← mem_singleton, eq_properDivisors_of_subset_of_sum_eq_sum (singleton_subset_iff.2
        (mem_properDivisors.2 ⟨h, hlt⟩)) (sum_singleton _ _), mem_properDivisors]
      exact ⟨one_dvd _, Nat.succ_lt_succ (Nat.succ_pos _)⟩
#align nat.sum_proper_divisors_dvd Nat.sum_properDivisors_dvd

@[to_additive (attr := simp)]
theorem Prime.prod_properDivisors {α : Type*} [CommMonoid α] {p : ℕ} {f : ℕ → α} (h : p.Prime) :
    ∏ x ∈ p.properDivisors, f x = f 1 := by simp [h.properDivisors]
#align nat.prime.prod_proper_divisors Nat.Prime.prod_properDivisors
#align nat.prime.sum_proper_divisors Nat.Prime.sum_properDivisors

@[to_additive (attr := simp)]
theorem Prime.prod_divisors {α : Type*} [CommMonoid α] {p : ℕ} {f : ℕ → α} (h : p.Prime) :
    ∏ x ∈ p.divisors, f x = f p * f 1 := by
  rw [← cons_self_properDivisors h.ne_zero, prod_cons, h.prod_properDivisors]
#align nat.prime.prod_divisors Nat.Prime.prod_divisors
#align nat.prime.sum_divisors Nat.Prime.sum_divisors

theorem properDivisors_eq_singleton_one_iff_prime : n.properDivisors = {1} ↔ n.Prime := by
  refine ⟨?_, ?_⟩
  · intro h
    refine Nat.prime_def_lt''.mpr ⟨?_, fun m hdvd => ?_⟩
    · match n with
      | 0 => contradiction
      | 1 => contradiction
      | Nat.succ (Nat.succ n) => simp [succ_le_succ]
    · rw [← mem_singleton, ← h, mem_properDivisors]
      have := Nat.le_of_dvd ?_ hdvd
      · simp [hdvd, this]
        exact (le_iff_eq_or_lt.mp this).symm
      · by_contra!
        simp only [nonpos_iff_eq_zero.mp this, this] at h
        contradiction
  · exact fun h => Prime.properDivisors h
#align nat.proper_divisors_eq_singleton_one_iff_prime Nat.properDivisors_eq_singleton_one_iff_prime

theorem sum_properDivisors_eq_one_iff_prime : ∑ x ∈ n.properDivisors, x = 1 ↔ n.Prime := by
  cases' n with n
  · simp [Nat.not_prime_zero]
  · cases n
    · simp [Nat.not_prime_one]
    · rw [← properDivisors_eq_singleton_one_iff_prime]
      refine ⟨fun h => ?_, fun h => h.symm ▸ sum_singleton _ _⟩
      rw [@eq_comm (Finset ℕ) _ _]
      apply
        eq_properDivisors_of_subset_of_sum_eq_sum
          (singleton_subset_iff.2
            (one_mem_properDivisors_iff_one_lt.2 (succ_lt_succ (Nat.succ_pos _))))
          ((sum_singleton _ _).trans h.symm)
#align nat.sum_proper_divisors_eq_one_iff_prime Nat.sum_properDivisors_eq_one_iff_prime

theorem mem_properDivisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) {x : ℕ} :
    x ∈ properDivisors (p ^ k) ↔ ∃ (j : ℕ) (_ : j < k), x = p ^ j := by
  rw [mem_properDivisors, Nat.dvd_prime_pow pp, ← exists_and_right]
  simp only [exists_prop, and_assoc]
  apply exists_congr
  intro a
  constructor <;> intro h
  · rcases h with ⟨_h_left, rfl, h_right⟩
    rw [Nat.pow_lt_pow_iff_right pp.one_lt] at h_right
    exact ⟨h_right, rfl⟩
  · rcases h with ⟨h_left, rfl⟩
    rw [Nat.pow_lt_pow_iff_right pp.one_lt]
    simp [h_left, le_of_lt]
#align nat.mem_proper_divisors_prime_pow Nat.mem_properDivisors_prime_pow

theorem properDivisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) :
    properDivisors (p ^ k) = (Finset.range k).map ⟨(p ^ ·), Nat.pow_right_injective pp.two_le⟩ := by
  ext a
  simp only [mem_properDivisors, Nat.isUnit_iff, mem_map, mem_range, Function.Embedding.coeFn_mk,
    pow_eq]
  have := mem_properDivisors_prime_pow pp k (x := a)
  rw [mem_properDivisors] at this
  rw [this]
  refine ⟨?_, ?_⟩
  · intro h; rcases h with ⟨j, hj, hap⟩; use j; tauto
  · tauto
#align nat.proper_divisors_prime_pow Nat.properDivisors_prime_pow

@[to_additive (attr := simp)]
theorem prod_properDivisors_prime_pow {α : Type*} [CommMonoid α] {k p : ℕ} {f : ℕ → α}
    (h : p.Prime) : (∏ x ∈ (p ^ k).properDivisors, f x) = ∏ x ∈ range k, f (p ^ x) := by
  simp [h, properDivisors_prime_pow]
#align nat.prod_proper_divisors_prime_pow Nat.prod_properDivisors_prime_pow
#align nat.sum_proper_divisors_prime_nsmul Nat.sum_properDivisors_prime_nsmul

@[to_additive (attr := simp) sum_divisors_prime_pow]
theorem prod_divisors_prime_pow {α : Type*} [CommMonoid α] {k p : ℕ} {f : ℕ → α} (h : p.Prime) :
    (∏ x ∈ (p ^ k).divisors, f x) = ∏ x ∈ range (k + 1), f (p ^ x) := by
  simp [h, divisors_prime_pow]
#align nat.prod_divisors_prime_pow Nat.prod_divisors_prime_pow
#align nat.sum_divisors_prime_pow Nat.sum_divisors_prime_pow

@[to_additive]
theorem prod_divisorsAntidiagonal {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) {n : ℕ} :
    ∏ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∏ i ∈ n.divisors, f i (n / i) := by
  rw [← map_div_right_divisors, Finset.prod_map]
  rfl
#align nat.prod_divisors_antidiagonal Nat.prod_divisorsAntidiagonal
#align nat.sum_divisors_antidiagonal Nat.sum_divisorsAntidiagonal

@[to_additive]
theorem prod_divisorsAntidiagonal' {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) {n : ℕ} :
    ∏ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∏ i ∈ n.divisors, f (n / i) i := by
  rw [← map_swap_divisorsAntidiagonal, Finset.prod_map]
  exact prod_divisorsAntidiagonal fun i j => f j i
#align nat.prod_divisors_antidiagonal' Nat.prod_divisorsAntidiagonal'
#align nat.sum_divisors_antidiagonal' Nat.sum_divisorsAntidiagonal'

/-- The factors of `n` are the prime divisors -/
theorem prime_divisors_eq_to_filter_divisors_prime (n : ℕ) :
    n.factors.toFinset = (divisors n).filter Prime := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  · ext q
    simpa [hn, hn.ne', mem_factors] using and_comm
#align nat.prime_divisors_eq_to_filter_divisors_prime Nat.prime_divisors_eq_to_filter_divisors_prime

lemma prime_divisors_filter_dvd_of_dvd {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) :
    n.factors.toFinset.filter (· ∣ m) = m.factors.toFinset := by
  simp_rw [prime_divisors_eq_to_filter_divisors_prime, filter_comm,
    divisors_filter_dvd_of_dvd hn hmn]

@[simp]
theorem image_div_divisors_eq_divisors (n : ℕ) :
    image (fun x : ℕ => n / x) n.divisors = n.divisors := by
  by_cases hn : n = 0
  · simp [hn]
  ext a
  constructor
  · rw [mem_image]
    rintro ⟨x, hx1, hx2⟩
    rw [mem_divisors] at *
    refine ⟨?_, hn⟩
    rw [← hx2]
    exact div_dvd_of_dvd hx1.1
  · rw [mem_divisors, mem_image]
    rintro ⟨h1, -⟩
    exact ⟨n / a, mem_divisors.mpr ⟨div_dvd_of_dvd h1, hn⟩, Nat.div_div_self h1 hn⟩
#align nat.image_div_divisors_eq_divisors Nat.image_div_divisors_eq_divisors

/- Porting note: Removed simp; simp_nf linter:
Left-hand side does not simplify, when using the simp lemma on itself.
This usually means that it will never apply. -/
@[to_additive sum_div_divisors]
theorem prod_div_divisors {α : Type*} [CommMonoid α] (n : ℕ) (f : ℕ → α) :
    (∏ d ∈ n.divisors, f (n / d)) = n.divisors.prod f := by
  by_cases hn : n = 0; · simp [hn]
  rw [← prod_image]
  · exact prod_congr (image_div_divisors_eq_divisors n) (by simp)
  · intro x hx y hy h
    rw [mem_divisors] at hx hy
    exact (div_eq_iff_eq_of_dvd_dvd hn hx.1 hy.1).mp h
#align nat.prod_div_divisors Nat.prod_div_divisors
#align nat.sum_div_divisors Nat.sum_div_divisors

end Nat

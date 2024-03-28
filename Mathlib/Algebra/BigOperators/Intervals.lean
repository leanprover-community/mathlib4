/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Nat.Interval

#align_import algebra.big_operators.intervals from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Results about big operators over intervals

We prove results about big operators over intervals.
-/

open Nat
open scoped BigOperators

variable {α M : Type*}

namespace Finset
section PartialOrder
variable [PartialOrder α] [CommMonoid M] {f : α → M} {a b : α}

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

@[to_additive]
lemma mul_prod_Ico_eq_prod_Icc (h : a ≤ b) : f b * ∏ x in Ico a b, f x = ∏ x in Icc a b, f x := by
  rw [Icc_eq_cons_Ico h, prod_cons]

@[to_additive]
lemma prod_Ico_mul_eq_prod_Icc (h : a ≤ b) : (∏ x in Ico a b, f x) * f b = ∏ x in Icc a b, f x := by
  rw [mul_comm, mul_prod_Ico_eq_prod_Icc h]

@[to_additive]
lemma mul_prod_Ioc_eq_prod_Icc (h : a ≤ b) : f a * ∏ x in Ioc a b, f x = ∏ x in Icc a b, f x := by
  rw [Icc_eq_cons_Ioc h, prod_cons]

@[to_additive]
lemma prod_Ioc_mul_eq_prod_Icc (h : a ≤ b) : (∏ x in Ioc a b, f x) * f a = ∏ x in Icc a b, f x := by
  rw [mul_comm, mul_prod_Ioc_eq_prod_Icc h]

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

@[to_additive]
lemma mul_prod_Ioi_eq_prod_Ici (a : α) : f a * ∏ x in Ioi a, f x = ∏ x in Ici a, f x := by
  rw [Ici_eq_cons_Ioi, prod_cons]

@[to_additive]
lemma prod_Ioi_mul_eq_prod_Ici (a : α) : (∏ x in Ioi a, f x) * f a = ∏ x in Ici a, f x := by
  rw [mul_comm, mul_prod_Ioi_eq_prod_Ici]

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[to_additive]
lemma mul_prod_Iio_eq_prod_Iic (a : α) : f a * ∏ x in Iio a, f x = ∏ x in Iic a, f x := by
  rw [Iic_eq_cons_Iio, prod_cons]

@[to_additive]
lemma prod_Iio_mul_eq_prod_Iic (a : α) : (∏ x in Iio a, f x) * f a = ∏ x in Iic a, f x := by
  rw [mul_comm, mul_prod_Iio_eq_prod_Iic]

end LocallyFiniteOrderBot
end PartialOrder

section LinearOrder
variable [Fintype α] [LinearOrder α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]
  [CommMonoid M]

@[to_additive]
lemma prod_prod_Ioi_mul_eq_prod_prod_off_diag (f : α → α → M) :
    ∏ i, ∏ j in Ioi i, f j i * f i j = ∏ i, ∏ j in {i}ᶜ, f j i := by
  simp_rw [← Ioi_disjUnion_Iio, prod_disjUnion, prod_mul_distrib]
  congr 1
  rw [prod_sigma', prod_sigma']
  refine' prod_nbij' (fun i ↦ ⟨i.2, i.1⟩) (fun i ↦ ⟨i.2, i.1⟩) _ _ _ _ _ <;> simp
#align finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag
#align finset.sum_sum_Ioi_add_eq_sum_sum_off_diag Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag

end LinearOrder

section Generic
variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α → M}

@[to_additive]
theorem prod_Ico_add' [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → M) (a b c : α) : (∏ x in Ico a b, f (x + c)) = ∏ x in Ico (a + c) (b + c), f x := by
  rw [← map_add_right_Ico, prod_map]
  rfl
#align finset.prod_Ico_add' Finset.prod_Ico_add'
#align finset.sum_Ico_add' Finset.sum_Ico_add'

@[to_additive]
theorem prod_Ico_add [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → M) (a b c : α) : (∏ x in Ico a b, f (c + x)) = ∏ x in Ico (a + c) (b + c), f x := by
  convert prod_Ico_add' f a b c using 2
  rw [add_comm]
#align finset.prod_Ico_add Finset.prod_Ico_add
#align finset.sum_Ico_add Finset.sum_Ico_add

@[to_additive]
theorem prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → M) :
    (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b := by
  rw [Nat.Ico_succ_right_eq_insert_Ico hab, prod_insert right_not_mem_Ico, mul_comm]
#align finset.prod_Ico_succ_top Finset.prod_Ico_succ_top
#align finset.sum_Ico_succ_top Finset.sum_Ico_succ_top

@[to_additive]
theorem prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → M) :
    ∏ k in Ico a b, f k = f a * ∏ k in Ico (a + 1) b, f k := by
  have ha : a ∉ Ico (a + 1) b := by simp
  rw [← prod_insert ha, Nat.Ico_insert_succ_left hab]
#align finset.prod_eq_prod_Ico_succ_bot Finset.prod_eq_prod_Ico_succ_bot
#align finset.sum_eq_sum_Ico_succ_bot Finset.sum_eq_sum_Ico_succ_bot

@[to_additive]
theorem prod_Ico_consecutive (f : ℕ → M) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i in Ico m n, f i) * ∏ i in Ico n k, f i) = ∏ i in Ico m k, f i :=
  Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm (prod_union (Ico_disjoint_Ico_consecutive m n k))
#align finset.prod_Ico_consecutive Finset.prod_Ico_consecutive
#align finset.sum_Ico_consecutive Finset.sum_Ico_consecutive

@[to_additive]
theorem prod_Ioc_consecutive (f : ℕ → M) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i in Ioc m n, f i) * ∏ i in Ioc n k, f i) = ∏ i in Ioc m k, f i := by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk, prod_union]
  apply disjoint_left.2 fun x hx h'x => _
  intros x hx h'x
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)
#align finset.prod_Ioc_consecutive Finset.prod_Ioc_consecutive
#align finset.sum_Ioc_consecutive Finset.sum_Ioc_consecutive

@[to_additive]
theorem prod_Ioc_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → M) :
    (∏ k in Ioc a (b + 1), f k) = (∏ k in Ioc a b, f k) * f (b + 1) := by
  rw [← prod_Ioc_consecutive _ hab (Nat.le_succ b), Nat.Ioc_succ_singleton, prod_singleton]
#align finset.prod_Ioc_succ_top Finset.prod_Ioc_succ_top
#align finset.sum_Ioc_succ_top Finset.sum_Ioc_succ_top

@[to_additive]
theorem prod_range_mul_prod_Ico (f : ℕ → M) {m n : ℕ} (h : m ≤ n) :
    ((∏ k in range m, f k) * ∏ k in Ico m n, f k) = ∏ k in range n, f k :=
  Nat.Ico_zero_eq_range ▸ Nat.Ico_zero_eq_range ▸ prod_Ico_consecutive f m.zero_le h
#align finset.prod_range_mul_prod_Ico Finset.prod_range_mul_prod_Ico
#align finset.sum_range_add_sum_Ico Finset.sum_range_add_sum_Ico

@[to_additive]
theorem prod_Ico_eq_mul_inv {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k in Ico m n, f k = (∏ k in range n, f k) * (∏ k in range m, f k)⁻¹ :=
  eq_mul_inv_iff_mul_eq.2 <| by (rw [mul_comm]; exact prod_range_mul_prod_Ico f h)
#align finset.prod_Ico_eq_mul_inv Finset.prod_Ico_eq_mul_inv
#align finset.sum_Ico_eq_add_neg Finset.sum_Ico_eq_add_neg

@[to_additive]
theorem prod_Ico_eq_div {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k in Ico m n, f k = (∏ k in range n, f k) / ∏ k in range m, f k := by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h
#align finset.prod_Ico_eq_div Finset.prod_Ico_eq_div
#align finset.sum_Ico_eq_sub Finset.sum_Ico_eq_sub

@[to_additive]
theorem prod_range_div_prod_range {α : Type*} [CommGroup α] {f : ℕ → α} {n m : ℕ} (hnm : n ≤ m) :
    ((∏ k in range m, f k) / ∏ k in range n, f k) =
    ∏ k in (range m).filter fun k => n ≤ k, f k := by
  rw [← prod_Ico_eq_div f hnm]
  congr
  apply Finset.ext
  simp only [mem_Ico, mem_filter, mem_range, *]
  tauto
#align finset.prod_range_sub_prod_range Finset.prod_range_div_prod_range
#align finset.sum_range_sub_sum_range Finset.sum_range_sub_sum_range

/-- The two ways of summing over `(i, j)` in the range `a ≤ i ≤ j < b` are equal. -/
theorem sum_Ico_Ico_comm {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i in Finset.Ico a b, ∑ j in Finset.Ico i b, f i j) =
      ∑ j in Finset.Ico a b, ∑ i in Finset.Ico a (j + 1), f i j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine' sum_nbij' (fun x ↦ ⟨x.2, x.1⟩) (fun x ↦ ⟨x.2, x.1⟩) _ _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  rintro a b ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
  refine' ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;>
  omega
#align finset.sum_Ico_Ico_comm Finset.sum_Ico_Ico_comm

/-- The two ways of summing over `(i, j)` in the range `a ≤ i < j < b` are equal. -/
theorem sum_Ico_Ico_comm' {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i in Finset.Ico a b, ∑ j in Finset.Ico (i + 1) b, f i j) =
      ∑ j in Finset.Ico a b, ∑ i in Finset.Ico a j, f i j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine' sum_nbij' (fun x ↦ ⟨x.2, x.1⟩) (fun x ↦ ⟨x.2, x.1⟩) _ _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  rintro a b ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
  refine' ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;>
  omega

@[to_additive]
theorem prod_Ico_eq_prod_range (f : ℕ → M) (m n : ℕ) :
    ∏ k in Ico m n, f k = ∏ k in range (n - m), f (m + k) := by
  by_cases h : m ≤ n
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h : n ≤ m := le_of_not_ge h
    rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty]
#align finset.prod_Ico_eq_prod_range Finset.prod_Ico_eq_prod_range
#align finset.sum_Ico_eq_sum_range Finset.sum_Ico_eq_sum_range

theorem prod_Ico_reflect (f : ℕ → M) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
    (∏ j in Ico k m, f (n - j)) = ∏ j in Ico (n + 1 - m) (n + 1 - k), f j := by
  have : ∀ i < m, i ≤ n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  cases' lt_or_le k m with hkm hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine' (prod_image _).symm
    simp only [mem_Ico]
    rintro i ⟨_, im⟩ j ⟨_, jm⟩ Hij
    rw [← tsub_tsub_cancel_of_le (this _ im), Hij, tsub_tsub_cancel_of_le (this _ jm)]
  · have : n + 1 - k ≤ n + 1 - m := by
      rw [tsub_le_tsub_iff_left h]
      exact hkm
    simp only [ge_iff_le, hkm, Ico_eq_empty_of_le, prod_empty, tsub_le_iff_right, Ico_eq_empty_of_le
      this]
#align finset.prod_Ico_reflect Finset.prod_Ico_reflect

theorem sum_Ico_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
    (h : m ≤ n + 1) : (∑ j in Ico k m, f (n - j)) = ∑ j in Ico (n + 1 - m) (n + 1 - k), f j :=
  @prod_Ico_reflect (Multiplicative δ) _ f k m n h
#align finset.sum_Ico_reflect Finset.sum_Ico_reflect

theorem prod_range_reflect (f : ℕ → M) (n : ℕ) :
    (∏ j in range n, f (n - 1 - j)) = ∏ j in range n, f j := by
  cases n
  · simp
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [prod_Ico_reflect _ _ le_rfl]
    simp
#align finset.prod_range_reflect Finset.prod_range_reflect

theorem sum_range_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (n : ℕ) :
    (∑ j in range n, f (n - 1 - j)) = ∑ j in range n, f j :=
  @prod_range_reflect (Multiplicative δ) _ f n
#align finset.sum_range_reflect Finset.sum_range_reflect

@[simp]
theorem prod_Ico_id_eq_factorial : ∀ n : ℕ, (∏ x in Ico 1 (n + 1), x) = n !
  | 0 => rfl
  | n + 1 => by
    rw [prod_Ico_succ_top <| Nat.succ_le_succ <| Nat.zero_le n, Nat.factorial_succ,
      prod_Ico_id_eq_factorial n, Nat.succ_eq_add_one, mul_comm]
#align finset.prod_Ico_id_eq_factorial Finset.prod_Ico_id_eq_factorial

@[simp]
theorem prod_range_add_one_eq_factorial : ∀ n : ℕ, (∏ x in range n, (x + 1)) = n !
  | 0 => rfl
  | n + 1 => by simp [factorial, Finset.range_succ, prod_range_add_one_eq_factorial n]
#align finset.prod_range_add_one_eq_factorial Finset.prod_range_add_one_eq_factorial

section GaussSum

/-- Gauss' summation formula -/
theorem sum_range_id_mul_two (n : ℕ) : (∑ i in range n, i) * 2 = n * (n - 1) :=
  calc
    (∑ i in range n, i) * 2 = (∑ i in range n, i) + ∑ i in range n, (n - 1 - i) := by
      rw [sum_range_reflect (fun i => i) n, mul_two]
    _ = ∑ i in range n, (i + (n - 1 - i)) := sum_add_distrib.symm
    _ = ∑ i in range n, (n - 1) :=
      sum_congr rfl fun i hi => add_tsub_cancel_of_le <| Nat.le_sub_one_of_lt <| mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]
#align finset.sum_range_id_mul_two Finset.sum_range_id_mul_two

/-- Gauss' summation formula -/
theorem sum_range_id (n : ℕ) : ∑ i in range n, i = n * (n - 1) / 2 := by
  rw [← sum_range_id_mul_two n, Nat.mul_div_cancel _ zero_lt_two]
#align finset.sum_range_id Finset.sum_range_id

end GaussSum

@[to_additive]
lemma prod_range_diag_flip (n : ℕ) (f : ℕ → ℕ → M) :
    (∏ m in range n, ∏ k in range (m + 1), f k (m - k)) =
      ∏ m in range n, ∏ k in range (n - m), f m k := by
  rw [prod_sigma', prod_sigma']
  refine prod_nbij' (fun a ↦ ⟨a.2, a.1 - a.2⟩) (fun a ↦ ⟨a.1 + a.2, a.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { contextual := true }) only [mem_sigma, mem_range, lt_tsub_iff_left,
      Nat.lt_succ_iff, le_add_iff_nonneg_right, Nat.zero_le, and_true, and_imp, imp_self,
      implies_true, Sigma.forall, forall_const, add_tsub_cancel_of_le, Sigma.mk.inj_iff,
      add_tsub_cancel_left, heq_eq_eq]
  · exact fun a b han hba ↦ lt_of_le_of_lt hba han
#align sum_range_diag_flip Finset.sum_range_diag_flip

end Generic

section Nat
variable {M : Type*} (f g : ℕ → M) {m n : ℕ}

section CommMonoid
variable [CommMonoid M]

/-- A product over `powerset s` is equal to the double product over sets of subsets of `s` with
`card s = k`, for `k = 1, ..., card s`. -/
@[to_additive "A sum over `powerset s` is equal to the double sum over sets of subsets of `s` with
  `card s = k`, for `k = 1, ..., card s`"]
lemma prod_powerset (s : Finset α) (f : Finset α → M) :
    ∏ t in powerset s, f t = ∏ j in range (card s + 1), ∏ t in powersetCard j s, f t := by
  rw [powerset_card_disjiUnion, prod_disjiUnion]
#align finset.prod_powerset Finset.prod_powerset
#align finset.sum_powerset Finset.sum_powerset

@[to_additive]
lemma prod_range_succ_comm (f : ℕ → M) (n : ℕ) :
    (∏ x in range (n + 1), f x) = f n * ∏ x in range n, f x := by
  rw [range_succ, prod_insert not_mem_range_self]
#align finset.prod_range_succ_comm Finset.prod_range_succ_comm
#align finset.sum_range_succ_comm Finset.sum_range_succ_comm

@[to_additive]
lemma prod_range_succ (f : ℕ → M) (n : ℕ) :
    (∏ x in range (n + 1), f x) = (∏ x in range n, f x) * f n := by
  simp only [mul_comm, prod_range_succ_comm]
#align finset.prod_range_succ Finset.prod_range_succ
#align finset.sum_range_succ Finset.sum_range_succ

@[to_additive]
lemma prod_range_succ' (f : ℕ → M) :
    ∀ n, ∏ k in range (n + 1), f k = (∏ k in range n, f (k + 1)) * f 0
  | 0 => prod_range_succ _ _
  | n + 1 => by rw [prod_range_succ _ n, mul_right_comm, ← prod_range_succ' _ n, prod_range_succ]
#align finset.prod_range_succ' Finset.prod_range_succ'
#align finset.sum_range_succ' Finset.sum_range_succ'

@[to_additive]
lemma eventually_constant_prod {u : ℕ → M} {N : ℕ} (hu : ∀ n ≥ N, u n = 1) {n : ℕ} (hn : N ≤ n) :
    ∏ k in range n, u k = ∏ k in range N, u k := by
  obtain ⟨m, rfl : n = N + m⟩ := le_iff_exists_add.mp hn
  clear hn
  induction' m with m hm
  · simp
  erw [prod_range_succ]
  simp [*]
#align finset.eventually_constant_prod Finset.eventually_constant_prod
#align finset.eventually_constant_sum Finset.eventually_constant_sum

@[to_additive]
lemma prod_range_add (f : ℕ → M) (n m : ℕ) :
    (∏ x in range (n + m), f x) = (∏ x in range n, f x) * ∏ x in range m, f (n + x) := by
  induction' m with m hm
  · simp
  · erw [Nat.add_succ, prod_range_succ, prod_range_succ, hm, mul_assoc]
#align finset.prod_range_add Finset.prod_range_add
#align finset.sum_range_add Finset.sum_range_add

@[to_additive]
lemma prod_range_add_div_prod_range {α : Type*} [CommGroup α] (f : ℕ → α) (n m : ℕ) :
    (∏ k in range (n + m), f k) / ∏ k in range n, f k = ∏ k in Finset.range m, f (n + k) :=
  div_eq_of_eq_mul' (prod_range_add f n m)
#align finset.prod_range_add_div_prod_range Finset.prod_range_add_div_prod_range
#align finset.sum_range_add_sub_sum_range Finset.sum_range_add_sub_sum_range

@[to_additive]
lemma prod_range_zero (f : ℕ → M) : ∏ k in range 0, f k = 1 := by rw [range_zero, prod_empty]
#align finset.prod_range_zero Finset.prod_range_zero
#align finset.sum_range_zero Finset.sum_range_zero

@[to_additive sum_range_one]
lemma prod_range_one (f : ℕ → M) : ∏ k in range 1, f k = f 0 := by
  rw [range_one, prod_singleton]
#align finset.prod_range_one Finset.prod_range_one
#align finset.sum_range_one Finset.sum_range_one

/-- For any product along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can verify
that it's equal to a different function just by checking ratios of adjacent terms.

This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
@[to_additive "For any sum along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can
verify that it's equal to a different function just by checking differences of adjacent terms.

This is a discrete analogue of the fundamental theorem of calculus."]
lemma prod_range_induction (f s : ℕ → M) (base : s 0 = 1)
    (step : ∀ n, s (n + 1) = s n * f n) (n : ℕ) :
    ∏ k in Finset.range n, f k = s n := by
  induction' n with k hk
  · rw [Finset.prod_range_zero, base]
  · simp only [hk, Finset.prod_range_succ, step, mul_comm]
#align finset.prod_range_induction Finset.prod_range_induction
#align finset.sum_range_induction Finset.sum_range_induction

/-- A telescoping product along `{0, ..., n - 1}` of a commutative group valued function reduces to
the ratio of the last and first factors. -/
@[to_additive "A telescoping sum along `{0, ..., n - 1}` of an additive commutative group valued
function reduces to the difference of the last and first terms."]
lemma prod_range_div {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i in range n, f (i + 1) / f i) = f n / f 0 := by apply prod_range_induction <;> simp
#align finset.prod_range_div Finset.prod_range_div
#align finset.sum_range_sub Finset.sum_range_sub

@[to_additive]
lemma prod_range_div' {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i in range n, f i / f (i + 1)) = f 0 / f n := by apply prod_range_induction <;> simp
#align finset.prod_range_div' Finset.prod_range_div'
#align finset.sum_range_sub' Finset.sum_range_sub'

@[to_additive]
lemma eq_prod_range_div {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = f 0 * ∏ i in range n, f (i + 1) / f i := by rw [prod_range_div, mul_div_cancel]
#align finset.eq_prod_range_div Finset.eq_prod_range_div
#align finset.eq_sum_range_sub Finset.eq_sum_range_sub

@[to_additive]
lemma eq_prod_range_div' {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = ∏ i in range (n + 1), if i = 0 then f 0 else f i / f (i - 1) := by
  conv_lhs => rw [Finset.eq_prod_range_div f]
  simp [Finset.prod_range_succ', mul_comm]
#align finset.eq_prod_range_div' Finset.eq_prod_range_div'
#align finset.eq_sum_range_sub' Finset.eq_sum_range_sub'

/-- A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function
reduces to the difference of the last and first terms
when the function we are summing is monotone.
-/
lemma sum_range_tsub [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] {f : ℕ → α} (h : Monotone f) (n : ℕ) :
    ∑ i in range n, (f (i + 1) - f i) = f n - f 0 := by
  apply sum_range_induction
  case base => apply tsub_self
  case step =>
    intro n
    have h₁ : f n ≤ f (n + 1) := h (Nat.le_succ _)
    have h₂ : f 0 ≤ f n := h (Nat.zero_le _)
    rw [tsub_add_eq_add_tsub h₂, add_tsub_cancel_of_le h₁]
#align finset.sum_range_tsub Finset.sum_range_tsub

@[to_additive]
lemma pow_eq_prod_const (b : M) : ∀ n, b ^ n = ∏ _k in range n, b := by simp
#align finset.pow_eq_prod_const Finset.pow_eq_prod_const
#align finset.nsmul_eq_sum_const Finset.nsmul_eq_sum_const

@[to_additive]
lemma prod_flip {n : ℕ} (f : ℕ → M) :
    (∏ r in range (n + 1), f (n - r)) = ∏ k in range (n + 1), f k := by
  induction' n with n ih
  · rw [prod_range_one, prod_range_one]
  · rw [prod_range_succ', prod_range_succ _ (Nat.succ n)]
    simp [← ih]
#align finset.prod_flip Finset.prod_flip
#align finset.sum_flip Finset.sum_flip

end CommMonoid

section CommGroup
variable [CommGroup M]

@[to_additive]
theorem prod_range_succ_div_prod : ((∏ i in range (n + 1), f i) / ∏ i in range n, f i) = f n :=
  div_eq_iff_eq_mul'.mpr <| prod_range_succ f n
#align finset.prod_range_succ_div_prod Finset.prod_range_succ_div_prod
#align finset.sum_range_succ_sub_sum Finset.sum_range_succ_sub_sum

@[to_additive]
theorem prod_range_succ_div_top : (∏ i in range (n + 1), f i) / f n = ∏ i in range n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_range_succ f n
#align finset.prod_range_succ_div_top Finset.prod_range_succ_div_top
#align finset.sum_range_succ_sub_top Finset.sum_range_succ_sub_top

@[to_additive]
theorem prod_Ico_div_bot (hmn : m < n) : (∏ i in Ico m n, f i) / f m = ∏ i in Ico (m + 1) n, f i :=
  div_eq_iff_eq_mul'.mpr <| prod_eq_prod_Ico_succ_bot hmn _
#align finset.prod_Ico_div_bot Finset.prod_Ico_div_bot
#align finset.sum_Ico_sub_bot Finset.sum_Ico_sub_bot

@[to_additive]
theorem prod_Ico_succ_div_top (hmn : m ≤ n) :
    (∏ i in Ico m (n + 1), f i) / f n = ∏ i in Ico m n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_Ico_succ_top hmn _
#align finset.prod_Ico_succ_div_top Finset.prod_Ico_succ_div_top
#align finset.sum_Ico_succ_sub_top Finset.sum_Ico_succ_sub_top

end CommGroup

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring α]

lemma sum_range_succ_mul_sum_range_succ (m n : ℕ) (f g : ℕ → α) :
    (∑ i in range (m + 1), f i) * ∑ i in range (n + 1), g i =
      (∑ i in range m, f i) * ∑ i in range n, g i +
        f m * ∑ i in range n, g i + (∑ i in range m, f i) * g n + f m * g n := by
  simp only [add_mul, mul_add, add_assoc, sum_range_succ]
#align finset.sum_range_succ_mul_sum_range_succ Finset.sum_range_succ_mul_sum_range_succ

end NonUnitalNonAssocSemiring

section CommRing
variable [CommRing α]

lemma prod_range_cast_nat_sub (n k : ℕ) :
    ∏ i in range k, (n - i : α) = (∏ i in range k, (n - i) : ℕ) := by
  rw [prod_natCast]
  rcases le_or_lt k n with hkn | hnk
  · exact prod_congr rfl fun i hi => (Nat.cast_sub <| (mem_range.1 hi).le.trans hkn).symm
  · rw [← mem_range] at hnk
    rw [prod_eq_zero hnk, prod_eq_zero hnk] <;> simp
#align finset.prod_range_cast_nat_sub Finset.prod_range_cast_nat_sub

end CommRing
end Nat
end Finset

lemma Multiset.sup_powersetCard {α : Type*} [DecidableEq α] (x : Multiset α) :
    (Finset.range (card x + 1)).sup x.powersetCard = x.powerset := by
  convert bind_powerset_len x using 1
  rw [Multiset.bind, Multiset.join, ← Finset.range_val, ← Finset.sum_eq_multiset_sum, eq_comm]
  exact finset_sum_eq_sup_iff_disjoint.mpr fun _ _ _ _ h ↦ pairwise_disjoint_powersetCard x h#align multiset.sup_powerset_len Multiset.sup_powersetCard

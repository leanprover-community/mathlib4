/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Interval.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

#align_import algebra.big_operators.intervals from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Results about big operators over intervals

We prove results about big operators over intervals.
-/

open Nat

variable {α M : Type*}

namespace Finset
section PartialOrder
variable [PartialOrder α] [CommMonoid M] {f : α → M} {a b : α}

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

@[to_additive]
lemma mul_prod_Ico_eq_prod_Icc (h : a ≤ b) : f b * ∏ x ∈ Ico a b, f x = ∏ x ∈ Icc a b, f x := by
  rw [Icc_eq_cons_Ico h, prod_cons]

@[to_additive]
lemma prod_Ico_mul_eq_prod_Icc (h : a ≤ b) : (∏ x ∈ Ico a b, f x) * f b = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, mul_prod_Ico_eq_prod_Icc h]

@[to_additive]
lemma mul_prod_Ioc_eq_prod_Icc (h : a ≤ b) : f a * ∏ x ∈ Ioc a b, f x = ∏ x ∈ Icc a b, f x := by
  rw [Icc_eq_cons_Ioc h, prod_cons]

@[to_additive]
lemma prod_Ioc_mul_eq_prod_Icc (h : a ≤ b) : (∏ x ∈ Ioc a b, f x) * f a = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, mul_prod_Ioc_eq_prod_Icc h]

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

@[to_additive]
lemma mul_prod_Ioi_eq_prod_Ici (a : α) : f a * ∏ x ∈ Ioi a, f x = ∏ x ∈ Ici a, f x := by
  rw [Ici_eq_cons_Ioi, prod_cons]

@[to_additive]
lemma prod_Ioi_mul_eq_prod_Ici (a : α) : (∏ x ∈ Ioi a, f x) * f a = ∏ x ∈ Ici a, f x := by
  rw [mul_comm, mul_prod_Ioi_eq_prod_Ici]

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[to_additive]
lemma mul_prod_Iio_eq_prod_Iic (a : α) : f a * ∏ x ∈ Iio a, f x = ∏ x ∈ Iic a, f x := by
  rw [Iic_eq_cons_Iio, prod_cons]

@[to_additive]
lemma prod_Iio_mul_eq_prod_Iic (a : α) : (∏ x ∈ Iio a, f x) * f a = ∏ x ∈ Iic a, f x := by
  rw [mul_comm, mul_prod_Iio_eq_prod_Iic]

end LocallyFiniteOrderBot
end PartialOrder

section LinearOrder
variable [Fintype α] [LinearOrder α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]
  [CommMonoid M]

@[to_additive]
lemma prod_prod_Ioi_mul_eq_prod_prod_off_diag (f : α → α → M) :
    ∏ i, ∏ j ∈ Ioi i, f j i * f i j = ∏ i, ∏ j ∈ {i}ᶜ, f j i := by
  simp_rw [← Ioi_disjUnion_Iio, prod_disjUnion, prod_mul_distrib]
  congr 1
  rw [prod_sigma', prod_sigma']
  refine prod_nbij' (fun i ↦ ⟨i.2, i.1⟩) (fun i ↦ ⟨i.2, i.1⟩) ?_ ?_ ?_ ?_ ?_ <;> simp
#align finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag
#align finset.sum_sum_Ioi_add_eq_sum_sum_off_diag Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag

end LinearOrder

section Generic
variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α → M}

@[to_additive]
theorem prod_Ico_add' [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → M) (a b c : α) : (∏ x ∈ Ico a b, f (x + c)) = ∏ x ∈ Ico (a + c) (b + c), f x := by
  rw [← map_add_right_Ico, prod_map]
  rfl
#align finset.prod_Ico_add' Finset.prod_Ico_add'
#align finset.sum_Ico_add' Finset.sum_Ico_add'

@[to_additive]
theorem prod_Ico_add [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → M) (a b c : α) : (∏ x ∈ Ico a b, f (c + x)) = ∏ x ∈ Ico (a + c) (b + c), f x := by
  convert prod_Ico_add' f a b c using 2
  rw [add_comm]
#align finset.prod_Ico_add Finset.prod_Ico_add
#align finset.sum_Ico_add Finset.sum_Ico_add

@[to_additive]
theorem prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → M) :
    (∏ k ∈ Ico a (b + 1), f k) = (∏ k ∈ Ico a b, f k) * f b := by
  rw [Nat.Ico_succ_right_eq_insert_Ico hab, prod_insert right_not_mem_Ico, mul_comm]
#align finset.prod_Ico_succ_top Finset.prod_Ico_succ_top
#align finset.sum_Ico_succ_top Finset.sum_Ico_succ_top

@[to_additive]
theorem prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → M) :
    ∏ k ∈ Ico a b, f k = f a * ∏ k ∈ Ico (a + 1) b, f k := by
  have ha : a ∉ Ico (a + 1) b := by simp
  rw [← prod_insert ha, Nat.Ico_insert_succ_left hab]
#align finset.prod_eq_prod_Ico_succ_bot Finset.prod_eq_prod_Ico_succ_bot
#align finset.sum_eq_sum_Ico_succ_bot Finset.sum_eq_sum_Ico_succ_bot

@[to_additive]
theorem prod_Ico_consecutive (f : ℕ → M) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i ∈ Ico m n, f i) * ∏ i ∈ Ico n k, f i) = ∏ i ∈ Ico m k, f i :=
  Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm (prod_union (Ico_disjoint_Ico_consecutive m n k))
#align finset.prod_Ico_consecutive Finset.prod_Ico_consecutive
#align finset.sum_Ico_consecutive Finset.sum_Ico_consecutive

@[to_additive]
theorem prod_Ioc_consecutive (f : ℕ → M) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i ∈ Ioc m n, f i) * ∏ i ∈ Ioc n k, f i) = ∏ i ∈ Ioc m k, f i := by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk, prod_union]
  apply disjoint_left.2 fun x hx h'x => _
  intros x hx h'x
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)
#align finset.prod_Ioc_consecutive Finset.prod_Ioc_consecutive
#align finset.sum_Ioc_consecutive Finset.sum_Ioc_consecutive

@[to_additive]
theorem prod_Ioc_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → M) :
    (∏ k ∈ Ioc a (b + 1), f k) = (∏ k ∈ Ioc a b, f k) * f (b + 1) := by
  rw [← prod_Ioc_consecutive _ hab (Nat.le_succ b), Nat.Ioc_succ_singleton, prod_singleton]
#align finset.prod_Ioc_succ_top Finset.prod_Ioc_succ_top
#align finset.sum_Ioc_succ_top Finset.sum_Ioc_succ_top

@[to_additive]
theorem prod_Icc_succ_top {a b : ℕ} (hab : a ≤ b + 1) (f : ℕ → M) :
    (∏ k in Icc a (b + 1), f k) = (∏ k in Icc a b, f k) * f (b + 1) := by
  rw [← Nat.Ico_succ_right, prod_Ico_succ_top hab, Nat.Ico_succ_right]

@[to_additive]
theorem prod_range_mul_prod_Ico (f : ℕ → M) {m n : ℕ} (h : m ≤ n) :
    ((∏ k ∈ range m, f k) * ∏ k ∈ Ico m n, f k) = ∏ k ∈ range n, f k :=
  Nat.Ico_zero_eq_range ▸ Nat.Ico_zero_eq_range ▸ prod_Ico_consecutive f m.zero_le h
#align finset.prod_range_mul_prod_Ico Finset.prod_range_mul_prod_Ico
#align finset.sum_range_add_sum_Ico Finset.sum_range_add_sum_Ico

@[to_additive]
theorem prod_Ico_eq_mul_inv {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k ∈ Ico m n, f k = (∏ k ∈ range n, f k) * (∏ k ∈ range m, f k)⁻¹ :=
  eq_mul_inv_iff_mul_eq.2 <| by (rw [mul_comm]; exact prod_range_mul_prod_Ico f h)
#align finset.prod_Ico_eq_mul_inv Finset.prod_Ico_eq_mul_inv
#align finset.sum_Ico_eq_add_neg Finset.sum_Ico_eq_add_neg

@[to_additive]
theorem prod_Ico_eq_div {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k ∈ Ico m n, f k = (∏ k ∈ range n, f k) / ∏ k ∈ range m, f k := by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h
#align finset.prod_Ico_eq_div Finset.prod_Ico_eq_div
#align finset.sum_Ico_eq_sub Finset.sum_Ico_eq_sub

@[to_additive]
theorem prod_range_div_prod_range {α : Type*} [CommGroup α] {f : ℕ → α} {n m : ℕ} (hnm : n ≤ m) :
    ((∏ k ∈ range m, f k) / ∏ k ∈ range n, f k) =
    ∏ k ∈ (range m).filter fun k => n ≤ k, f k := by
  rw [← prod_Ico_eq_div f hnm]
  congr
  apply Finset.ext
  simp only [mem_Ico, mem_filter, mem_range, *]
  tauto
#align finset.prod_range_sub_prod_range Finset.prod_range_div_prod_range
#align finset.sum_range_sub_sum_range Finset.sum_range_sub_sum_range

/-- The two ways of summing over `(i, j)` in the range `a ≤ i ≤ j < b` are equal. -/
theorem sum_Ico_Ico_comm {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico i b, f i j) =
      ∑ j ∈ Finset.Ico a b, ∑ i ∈ Finset.Ico a (j + 1), f i j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine sum_nbij' (fun x ↦ ⟨x.2, x.1⟩) (fun x ↦ ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  rintro a b ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
  refine ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;>
  omega
#align finset.sum_Ico_Ico_comm Finset.sum_Ico_Ico_comm

/-- The two ways of summing over `(i, j)` in the range `a ≤ i < j < b` are equal. -/
theorem sum_Ico_Ico_comm' {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico (i + 1) b, f i j) =
      ∑ j ∈ Finset.Ico a b, ∑ i ∈ Finset.Ico a j, f i j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine sum_nbij' (fun x ↦ ⟨x.2, x.1⟩) (fun x ↦ ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  rintro a b ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
  refine ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;>
  omega

@[to_additive]
theorem prod_Ico_eq_prod_range (f : ℕ → M) (m n : ℕ) :
    ∏ k ∈ Ico m n, f k = ∏ k ∈ range (n - m), f (m + k) := by
  by_cases h : m ≤ n
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h : n ≤ m := le_of_not_ge h
    rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty]
#align finset.prod_Ico_eq_prod_range Finset.prod_Ico_eq_prod_range
#align finset.sum_Ico_eq_sum_range Finset.sum_Ico_eq_sum_range

theorem prod_Ico_reflect (f : ℕ → M) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
    (∏ j ∈ Ico k m, f (n - j)) = ∏ j ∈ Ico (n + 1 - m) (n + 1 - k), f j := by
  have : ∀ i < m, i ≤ n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  cases' lt_or_le k m with hkm hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine (prod_image ?_).symm
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
    (h : m ≤ n + 1) : (∑ j ∈ Ico k m, f (n - j)) = ∑ j ∈ Ico (n + 1 - m) (n + 1 - k), f j :=
  @prod_Ico_reflect (Multiplicative δ) _ f k m n h
#align finset.sum_Ico_reflect Finset.sum_Ico_reflect

theorem prod_range_reflect (f : ℕ → M) (n : ℕ) :
    (∏ j ∈ range n, f (n - 1 - j)) = ∏ j ∈ range n, f j := by
  cases n
  · simp
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [prod_Ico_reflect _ _ le_rfl]
    simp
#align finset.prod_range_reflect Finset.prod_range_reflect

theorem sum_range_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (n : ℕ) :
    (∑ j ∈ range n, f (n - 1 - j)) = ∑ j ∈ range n, f j :=
  @prod_range_reflect (Multiplicative δ) _ f n
#align finset.sum_range_reflect Finset.sum_range_reflect

@[simp]
theorem prod_Ico_id_eq_factorial : ∀ n : ℕ, (∏ x ∈ Ico 1 (n + 1), x) = n !
  | 0 => rfl
  | n + 1 => by
    rw [prod_Ico_succ_top <| Nat.succ_le_succ <| Nat.zero_le n, Nat.factorial_succ,
      prod_Ico_id_eq_factorial n, Nat.succ_eq_add_one, mul_comm]
#align finset.prod_Ico_id_eq_factorial Finset.prod_Ico_id_eq_factorial

@[simp]
theorem prod_range_add_one_eq_factorial : ∀ n : ℕ, (∏ x ∈ range n, (x + 1)) = n !
  | 0 => rfl
  | n + 1 => by simp [factorial, Finset.range_succ, prod_range_add_one_eq_factorial n]
#align finset.prod_range_add_one_eq_factorial Finset.prod_range_add_one_eq_factorial

section GaussSum

/-- Gauss' summation formula -/
theorem sum_range_id_mul_two (n : ℕ) : (∑ i ∈ range n, i) * 2 = n * (n - 1) :=
  calc
    (∑ i ∈ range n, i) * 2 = (∑ i ∈ range n, i) + ∑ i ∈ range n, (n - 1 - i) := by
      rw [sum_range_reflect (fun i => i) n, mul_two]
    _ = ∑ i ∈ range n, (i + (n - 1 - i)) := sum_add_distrib.symm
    _ = ∑ i ∈ range n, (n - 1) :=
      sum_congr rfl fun i hi => add_tsub_cancel_of_le <| Nat.le_sub_one_of_lt <| mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]
#align finset.sum_range_id_mul_two Finset.sum_range_id_mul_two

/-- Gauss' summation formula -/
theorem sum_range_id (n : ℕ) : ∑ i ∈ range n, i = n * (n - 1) / 2 := by
  rw [← sum_range_id_mul_two n, Nat.mul_div_cancel _ zero_lt_two]
#align finset.sum_range_id Finset.sum_range_id

end GaussSum

@[to_additive]
lemma prod_range_diag_flip (n : ℕ) (f : ℕ → ℕ → M) :
    (∏ m ∈ range n, ∏ k ∈ range (m + 1), f k (m - k)) =
      ∏ m ∈ range n, ∏ k ∈ range (n - m), f m k := by
  rw [prod_sigma', prod_sigma']
  refine prod_nbij' (fun a ↦ ⟨a.2, a.1 - a.2⟩) (fun a ↦ ⟨a.1 + a.2, a.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { contextual := true }) only [mem_sigma, mem_range, lt_tsub_iff_left,
      Nat.lt_succ_iff, le_add_iff_nonneg_right, Nat.zero_le, and_true, and_imp, imp_self,
      implies_true, Sigma.forall, forall_const, add_tsub_cancel_of_le, Sigma.mk.inj_iff,
      add_tsub_cancel_left, heq_eq_eq]
  exact fun a b han hba ↦ lt_of_le_of_lt hba han
#align sum_range_diag_flip Finset.sum_range_diag_flip

end Generic

section Nat

variable {M : Type*}
variable (f g : ℕ → M) {m n : ℕ}

section Group

variable [CommGroup M]

@[to_additive]
theorem prod_range_succ_div_prod : ((∏ i ∈ range (n + 1), f i) / ∏ i ∈ range n, f i) = f n :=
  div_eq_iff_eq_mul'.mpr <| prod_range_succ f n
#align finset.prod_range_succ_div_prod Finset.prod_range_succ_div_prod
#align finset.sum_range_succ_sub_sum Finset.sum_range_succ_sub_sum

@[to_additive]
theorem prod_range_succ_div_top : (∏ i ∈ range (n + 1), f i) / f n = ∏ i ∈ range n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_range_succ f n
#align finset.prod_range_succ_div_top Finset.prod_range_succ_div_top
#align finset.sum_range_succ_sub_top Finset.sum_range_succ_sub_top

@[to_additive]
theorem prod_Ico_div_bot (hmn : m < n) : (∏ i ∈ Ico m n, f i) / f m = ∏ i ∈ Ico (m + 1) n, f i :=
  div_eq_iff_eq_mul'.mpr <| prod_eq_prod_Ico_succ_bot hmn _
#align finset.prod_Ico_div_bot Finset.prod_Ico_div_bot
#align finset.sum_Ico_sub_bot Finset.sum_Ico_sub_bot

@[to_additive]
theorem prod_Ico_succ_div_top (hmn : m ≤ n) :
    (∏ i ∈ Ico m (n + 1), f i) / f n = ∏ i ∈ Ico m n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_Ico_succ_top hmn _
#align finset.prod_Ico_succ_div_top Finset.prod_Ico_succ_div_top
#align finset.sum_Ico_succ_sub_top Finset.sum_Ico_succ_sub_top

end Group

end Nat
end Finset

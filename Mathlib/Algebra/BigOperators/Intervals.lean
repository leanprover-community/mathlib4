/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Results about big operators over intervals

We prove results about big operators over intervals.
-/

open Nat

variable {α G M : Type*}

namespace Finset

section Generic
variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α → M}

@[to_additive]
theorem prod_Ico_add' [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → M) (a b c : α) : (∏ x ∈ Ico a b, f (x + c)) = ∏ x ∈ Ico (a + c) (b + c), f x := by
  rw [← map_add_right_Ico, prod_map]
  rfl

@[to_additive]
theorem prod_Ico_add [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → M) (a b c : α) : (∏ x ∈ Ico a b, f (c + x)) = ∏ x ∈ Ico (a + c) (b + c), f x := by
  convert prod_Ico_add' f a b c using 2
  rw [add_comm]

@[to_additive (attr := simp)]
theorem prod_Ico_add_right_sub_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [ExistsAddOfLE α] [LocallyFiniteOrder α] [Sub α] [OrderedSub α] (a b c : α) :
    ∏ x ∈ Ico (a + c) (b + c), f (x - c) = ∏ x ∈ Ico a b, f x := by
  simp only [← map_add_right_Ico, prod_map, addRightEmbedding_apply, add_tsub_cancel_right]

@[to_additive]
theorem prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → M) :
    (∏ k ∈ Ico a (b + 1), f k) = (∏ k ∈ Ico a b, f k) * f b := by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab, prod_insert right_notMem_Ico, mul_comm]

@[to_additive]
theorem prod_Ico_consecutive (f : ℕ → M) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i ∈ Ico m n, f i) * ∏ i ∈ Ico n k, f i) = ∏ i ∈ Ico m k, f i :=
  Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm (prod_union (Ico_disjoint_Ico_consecutive m n k))

@[to_additive]
theorem prod_Ioc_consecutive (f : ℕ → M) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i ∈ Ioc m n, f i) * ∏ i ∈ Ioc n k, f i) = ∏ i ∈ Ioc m k, f i := by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk, prod_union]
  apply disjoint_left.2 fun x hx h'x => _
  intro x hx h'x
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)

@[to_additive]
theorem prod_Ioc_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → M) :
    (∏ k ∈ Ioc a (b + 1), f k) = (∏ k ∈ Ioc a b, f k) * f (b + 1) := by
  rw [← prod_Ioc_consecutive _ hab (Nat.le_succ b), Nat.Ioc_succ_singleton, prod_singleton]

@[to_additive]
theorem prod_Icc_succ_top {a b : ℕ} (hab : a ≤ b + 1) (f : ℕ → M) :
    (∏ k ∈ Icc a (b + 1), f k) = (∏ k ∈ Icc a b, f k) * f (b + 1) := by
  rw [← Ico_add_one_right_eq_Icc, prod_Ico_succ_top hab, Ico_add_one_right_eq_Icc]

@[to_additive]
theorem prod_range_mul_prod_Ico (f : ℕ → M) {m n : ℕ} (h : m ≤ n) :
    ((∏ k ∈ range m, f k) * ∏ k ∈ Ico m n, f k) = ∏ k ∈ range n, f k :=
  Nat.Ico_zero_eq_range ▸ Nat.Ico_zero_eq_range ▸ prod_Ico_consecutive f m.zero_le h

@[to_additive]
theorem prod_range_eq_mul_Ico (f : ℕ → M) {n : ℕ} (hn : 0 < n) :
    ∏ x ∈ Finset.range n, f x = f 0 * ∏ x ∈ Ico 1 n, f x :=
  Finset.range_eq_Ico ▸ Finset.prod_eq_prod_Ico_succ_bot hn f

@[to_additive]
theorem prod_Ico_eq_mul_inv {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k ∈ Ico m n, f k = (∏ k ∈ range n, f k) * (∏ k ∈ range m, f k)⁻¹ :=
  eq_mul_inv_iff_mul_eq.2 <| by (rw [mul_comm]; exact prod_range_mul_prod_Ico f h)

@[to_additive]
theorem prod_Ico_eq_div {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k ∈ Ico m n, f k = (∏ k ∈ range n, f k) / ∏ k ∈ range m, f k := by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h

@[to_additive]
theorem prod_range_div_prod_range {G : Type*} [CommGroup G] {f : ℕ → G} {n m : ℕ} (hnm : n ≤ m) :
    ((∏ k ∈ range m, f k) / ∏ k ∈ range n, f k) = ∏ k ∈ range m with n ≤ k, f k := by
  rw [← prod_Ico_eq_div f hnm]
  congr
  apply Finset.ext
  simp only [mem_Ico, mem_filter, mem_range, *]
  tauto

/-- The two ways of summing over `(i, j)` in the range `a ≤ i ≤ j < b` are equal. -/
theorem sum_Ico_Ico_comm {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico i b, f i j) =
      ∑ j ∈ Finset.Ico a b, ∑ i ∈ Finset.Ico a (j + 1), f i j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine sum_nbij' (fun x ↦ ⟨x.2, x.1⟩) (fun x ↦ ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  rintro a b ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
  omega

/-- The two ways of summing over `(i, j)` in the range `a ≤ i < j < b` are equal. -/
theorem sum_Ico_Ico_comm' {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico (i + 1) b, f i j) =
      ∑ j ∈ Finset.Ico a b, ∑ i ∈ Finset.Ico a j, f i j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine sum_nbij' (fun x ↦ ⟨x.2, x.1⟩) (fun x ↦ ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  rintro a b ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
  omega

@[to_additive]
theorem prod_Ico_eq_prod_range (f : ℕ → M) (m n : ℕ) :
    ∏ k ∈ Ico m n, f k = ∏ k ∈ range (n - m), f (m + k) := by
  by_cases h : m ≤ n
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h : n ≤ m := le_of_not_ge h
    rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty]

theorem prod_Ico_reflect (f : ℕ → M) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
    (∏ j ∈ Ico k m, f (n - j)) = ∏ j ∈ Ico (n + 1 - m) (n + 1 - k), f j := by
  have : ∀ i < m, i ≤ n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  rcases lt_or_ge k m with hkm | hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine (prod_image ?_).symm
    simp only [mem_Ico, Set.InjOn, mem_coe]
    rintro i ⟨_, im⟩ j ⟨_, jm⟩ Hij
    rw [← tsub_tsub_cancel_of_le (this _ im), Hij, tsub_tsub_cancel_of_le (this _ jm)]
  · have : n + 1 - k ≤ n + 1 - m := by
      rw [tsub_le_tsub_iff_left h]
      exact hkm
    simp only [hkm, Ico_eq_empty_of_le, prod_empty, Ico_eq_empty_of_le this]

theorem sum_Ico_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
    (h : m ≤ n + 1) : (∑ j ∈ Ico k m, f (n - j)) = ∑ j ∈ Ico (n + 1 - m) (n + 1 - k), f j :=
  @prod_Ico_reflect (Multiplicative δ) _ f k m n h

theorem prod_range_reflect (f : ℕ → M) (n : ℕ) :
    (∏ j ∈ range n, f (n - 1 - j)) = ∏ j ∈ range n, f j := by
  cases n
  · simp
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [prod_Ico_reflect _ _ le_rfl]
    simp

theorem sum_range_reflect {δ : Type*} [AddCommMonoid δ] (f : ℕ → δ) (n : ℕ) :
    (∑ j ∈ range n, f (n - 1 - j)) = ∑ j ∈ range n, f j :=
  @prod_range_reflect (Multiplicative δ) _ f n

@[simp]
theorem prod_Ico_id_eq_factorial : ∀ n : ℕ, (∏ x ∈ Ico 1 (n + 1), x) = n !
  | 0 => rfl
  | n + 1 => by
    rw [prod_Ico_succ_top <| Nat.succ_le_succ <| Nat.zero_le n, Nat.factorial_succ,
      prod_Ico_id_eq_factorial n, Nat.succ_eq_add_one, mul_comm]

@[simp]
theorem prod_range_add_one_eq_factorial : ∀ n : ℕ, (∏ x ∈ range n, (x + 1)) = n !
  | 0 => rfl
  | n + 1 => by simp [factorial, Finset.range_add_one, prod_range_add_one_eq_factorial n]

section GaussSum

/-- Gauss' summation formula -/
theorem sum_range_id_mul_two (n : ℕ) : (∑ i ∈ range n, i) * 2 = n * (n - 1) :=
  calc
    (∑ i ∈ range n, i) * 2 = (∑ i ∈ range n, i) + ∑ i ∈ range n, (n - 1 - i) := by
      rw [sum_range_reflect (fun i => i) n, mul_two]
    _ = ∑ i ∈ range n, (i + (n - 1 - i)) := sum_add_distrib.symm
    _ = ∑ _ ∈ range n, (n - 1) :=
      sum_congr rfl fun _ hi => add_tsub_cancel_of_le <| Nat.le_sub_one_of_lt <| mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]

/-- Gauss' summation formula -/
theorem sum_range_id (n : ℕ) : ∑ i ∈ range n, i = n * (n - 1) / 2 := by
  rw [← sum_range_id_mul_two n, Nat.mul_div_cancel _ Nat.zero_lt_two]

end GaussSum

@[to_additive]
lemma prod_range_diag_flip (n : ℕ) (f : ℕ → ℕ → M) :
    (∏ m ∈ range n, ∏ k ∈ range (m + 1), f k (m - k)) =
      ∏ m ∈ range n, ∏ k ∈ range (n - m), f m k := by
  rw [prod_sigma', prod_sigma']
  refine prod_nbij' (fun a ↦ ⟨a.2, a.1 - a.2⟩) (fun a ↦ ⟨a.1 + a.2, a.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp +contextual only [mem_sigma, mem_range, lt_tsub_iff_left,
      Nat.lt_succ_iff, le_add_iff_nonneg_right, Nat.zero_le, and_true, and_imp, implies_true,
      Sigma.forall, add_tsub_cancel_of_le, add_tsub_cancel_left]
  exact fun a b han hba ↦ lt_of_le_of_lt hba han

end Generic

section Nat

variable {M : Type*}
variable (f g : ℕ → M) {m n : ℕ}

section Group

variable [CommGroup M]

@[to_additive]
theorem prod_range_succ_div_prod : ((∏ i ∈ range (n + 1), f i) / ∏ i ∈ range n, f i) = f n :=
  div_eq_iff_eq_mul'.mpr <| prod_range_succ f n

@[to_additive]
theorem prod_range_succ_div_top : (∏ i ∈ range (n + 1), f i) / f n = ∏ i ∈ range n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_range_succ f n

@[to_additive]
theorem prod_Ico_div_bot (hmn : m < n) : (∏ i ∈ Ico m n, f i) / f m = ∏ i ∈ Ico (m + 1) n, f i :=
  div_eq_iff_eq_mul'.mpr <| prod_eq_prod_Ico_succ_bot hmn _

@[to_additive]
theorem prod_Ico_succ_div_top (hmn : m ≤ n) :
    (∏ i ∈ Ico m (n + 1), f i) / f n = ∏ i ∈ Ico m n, f i :=
  div_eq_iff_eq_mul.mpr <| prod_Ico_succ_top hmn _

@[to_additive]
theorem prod_Ico_div (hmn : m ≤ n) : ∏ i ∈ Ico m n, f (i + 1) / f i = f n / f m := by
  rw [prod_Ico_eq_div _ hmn, prod_range_div, prod_range_div, div_div_div_cancel_right]

end Group

end Nat
end Finset

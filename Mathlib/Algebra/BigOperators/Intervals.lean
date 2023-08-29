/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Tactic.Linarith

#align_import algebra.big_operators.intervals from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Results about big operators over intervals

We prove results about big operators over intervals (mostly the `ℕ`-valued `Ico m n`).
-/


universe u v w

open BigOperators
open Nat

namespace Finset

section Generic

variable {α : Type u} {β : Type v} {γ : Type w} {s₂ s₁ s : Finset α} {a : α} {g f : α → β}

variable [CommMonoid β]

@[to_additive]
theorem prod_Ico_add' [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → β) (a b c : α) : (∏ x in Ico a b, f (x + c)) = ∏ x in Ico (a + c) (b + c), f x := by
  rw [← map_add_right_Ico, prod_map]
  -- ⊢ ∏ x in Ico a b, f (x + c) = ∏ x in Ico a b, f (↑(addRightEmbedding c) x)
  rfl
  -- 🎉 no goals
#align finset.prod_Ico_add' Finset.prod_Ico_add'
#align finset.sum_Ico_add' Finset.sum_Ico_add'

@[to_additive]
theorem prod_Ico_add [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → β) (a b c : α) : (∏ x in Ico a b, f (c + x)) = ∏ x in Ico (a + c) (b + c), f x := by
  convert prod_Ico_add' f a b c using 2
  -- ⊢ f (c + x✝) = f (x✝ + c)
  rw [add_comm]
  -- 🎉 no goals
#align finset.prod_Ico_add Finset.prod_Ico_add
#align finset.sum_Ico_add Finset.sum_Ico_add

@[to_additive]
theorem prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
    (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b := by
  rw [Nat.Ico_succ_right_eq_insert_Ico hab, prod_insert right_not_mem_Ico, mul_comm]
  -- 🎉 no goals
#align finset.prod_Ico_succ_top Finset.prod_Ico_succ_top
#align finset.sum_Ico_succ_top Finset.sum_Ico_succ_top

@[to_additive]
theorem prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → β) :
    ∏ k in Ico a b, f k = f a * ∏ k in Ico (a + 1) b, f k := by
  have ha : a ∉ Ico (a + 1) b := by simp
  -- ⊢ ∏ k in Ico a b, f k = f a * ∏ k in Ico (a + 1) b, f k
  rw [← prod_insert ha, Nat.Ico_insert_succ_left hab]
  -- 🎉 no goals
#align finset.prod_eq_prod_Ico_succ_bot Finset.prod_eq_prod_Ico_succ_bot
#align finset.sum_eq_sum_Ico_succ_bot Finset.sum_eq_sum_Ico_succ_bot

@[to_additive]
theorem prod_Ico_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i in Ico m n, f i) * ∏ i in Ico n k, f i) = ∏ i in Ico m k, f i :=
  Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm (prod_union (Ico_disjoint_Ico_consecutive m n k))
#align finset.prod_Ico_consecutive Finset.prod_Ico_consecutive
#align finset.sum_Ico_consecutive Finset.sum_Ico_consecutive

@[to_additive]
theorem prod_Ioc_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((∏ i in Ioc m n, f i) * ∏ i in Ioc n k, f i) = ∏ i in Ioc m k, f i := by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk, prod_union]
  -- ⊢ Disjoint (Ioc m n) (Ioc n k)
  apply disjoint_left.2 fun x hx h'x => _
  -- ⊢ ∀ (x : ℕ), x ∈ Ioc m n → x ∈ Ioc n k → False
  intros x hx h'x
  -- ⊢ False
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)
  -- 🎉 no goals
#align finset.prod_Ioc_consecutive Finset.prod_Ioc_consecutive
#align finset.sum_Ioc_consecutive Finset.sum_Ioc_consecutive

@[to_additive]
theorem prod_Ioc_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
    (∏ k in Ioc a (b + 1), f k) = (∏ k in Ioc a b, f k) * f (b + 1) := by
  rw [← prod_Ioc_consecutive _ hab (Nat.le_succ b), Nat.Ioc_succ_singleton, prod_singleton]
  -- 🎉 no goals
#align finset.prod_Ioc_succ_top Finset.prod_Ioc_succ_top
#align finset.sum_Ioc_succ_top Finset.sum_Ioc_succ_top

@[to_additive]
theorem prod_range_mul_prod_Ico (f : ℕ → β) {m n : ℕ} (h : m ≤ n) :
    ((∏ k in range m, f k) * ∏ k in Ico m n, f k) = ∏ k in range n, f k :=
  Nat.Ico_zero_eq_range ▸ Nat.Ico_zero_eq_range ▸ prod_Ico_consecutive f m.zero_le h
#align finset.prod_range_mul_prod_Ico Finset.prod_range_mul_prod_Ico
#align finset.sum_range_add_sum_Ico Finset.sum_range_add_sum_Ico

@[to_additive]
theorem prod_Ico_eq_mul_inv {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k in Ico m n, f k = (∏ k in range n, f k) * (∏ k in range m, f k)⁻¹ :=
  eq_mul_inv_iff_mul_eq.2 <| by (rw [mul_comm]; exact prod_range_mul_prod_Ico f h)
                                 -- ⊢ (∏ k in range m, f k) * ∏ k in Ico m n, f k = ∏ k in range n, f k
                                                -- 🎉 no goals
#align finset.prod_Ico_eq_mul_inv Finset.prod_Ico_eq_mul_inv
#align finset.sum_Ico_eq_add_neg Finset.sum_Ico_eq_add_neg

@[to_additive]
theorem prod_Ico_eq_div {δ : Type*} [CommGroup δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
    ∏ k in Ico m n, f k = (∏ k in range n, f k) / ∏ k in range m, f k := by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h
  -- 🎉 no goals
#align finset.prod_Ico_eq_div Finset.prod_Ico_eq_div
#align finset.sum_Ico_eq_sub Finset.sum_Ico_eq_sub

@[to_additive]
theorem prod_range_div_prod_range {α : Type*} [CommGroup α] {f : ℕ → α} {n m : ℕ} (hnm : n ≤ m) :
    ((∏ k in range m, f k) / ∏ k in range n, f k) =
    ∏ k in (range m).filter fun k => n ≤ k, f k := by
  rw [← prod_Ico_eq_div f hnm]
  -- ⊢ ∏ k in Ico n m, f k = ∏ k in filter (fun k => n ≤ k) (range m), f k
  congr
  -- ⊢ Ico n m = filter (fun k => n ≤ k) (range m)
  apply Finset.ext
  -- ⊢ ∀ (a : ℕ), a ∈ Ico n m ↔ a ∈ filter (fun k => n ≤ k) (range m)
  simp only [mem_Ico, mem_filter, mem_range, *]
  -- ⊢ ∀ (a : ℕ), n ≤ a ∧ a < m ↔ a < m ∧ n ≤ a
  tauto
  -- 🎉 no goals
#align finset.prod_range_sub_prod_range Finset.prod_range_div_prod_range
#align finset.sum_range_sub_sum_range Finset.sum_range_sub_sum_range

/-- The two ways of summing over `(i,j)` in the range `a<=i<=j<b` are equal. -/
theorem sum_Ico_Ico_comm {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i in Finset.Ico a b, ∑ j in Finset.Ico i b, f i j) =
      ∑ j in Finset.Ico a b, ∑ i in Finset.Ico a (j + 1), f i j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  -- ⊢ ∑ x in Finset.sigma (Ico a b) fun i => Ico i b, f x.fst x.snd = ∑ x in Finse …
  refine'
    Finset.sum_bij' (fun (x : Σ _ : ℕ, ℕ) _ => (⟨x.2, x.1⟩ : Σ _ : ℕ, ℕ)) _ (fun _ _ => rfl)
      (fun (x : Σ _ : ℕ, ℕ) _ => (⟨x.2, x.1⟩ : Σ _ : ℕ, ℕ)) _ (by (rintro ⟨⟩ _; rfl))
      (by (rintro ⟨⟩ _; rfl)) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  -- ⊢ ∀ (a_1 b_1 : ℕ), (a ≤ a_1 ∧ a_1 < b) ∧ a_1 ≤ b_1 ∧ b_1 < b → (a ≤ b_1 ∧ b_1  …
  -- ⊢ ∀ (a_1 b_1 : ℕ), (a ≤ a_1 ∧ a_1 < b) ∧ a ≤ b_1 ∧ b_1 < a_1 + 1 → (a ≤ b_1 ∧  …
  rintro a b ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
  -- ⊢ (a✝ ≤ b ∧ b < b✝) ∧ a✝ ≤ a ∧ a < b + 1
  -- ⊢ (a✝ ≤ b ∧ b < b✝) ∧ b ≤ a ∧ a < b✝
  refine' ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;>
  linarith
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
#align finset.sum_Ico_Ico_comm Finset.sum_Ico_Ico_comm

@[to_additive]
theorem prod_Ico_eq_prod_range (f : ℕ → β) (m n : ℕ) :
    ∏ k in Ico m n, f k = ∏ k in range (n - m), f (m + k) := by
  by_cases h : m ≤ n
  -- ⊢ ∏ k in Ico m n, f k = ∏ k in range (n - m), f (m + k)
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
    -- 🎉 no goals
  · replace h : n ≤ m := le_of_not_ge h
    -- ⊢ ∏ k in Ico m n, f k = ∏ k in range (n - m), f (m + k)
    rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty]
    -- 🎉 no goals
#align finset.prod_Ico_eq_prod_range Finset.prod_Ico_eq_prod_range
#align finset.sum_Ico_eq_sum_range Finset.sum_Ico_eq_sum_range

theorem prod_Ico_reflect (f : ℕ → β) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
    (∏ j in Ico k m, f (n - j)) = ∏ j in Ico (n + 1 - m) (n + 1 - k), f j := by
  have : ∀ i < m, i ≤ n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  cases' lt_or_le k m with hkm hkm
  -- ⊢ ∏ j in Ico k m, f (n - j) = ∏ j in Ico (n + 1 - m) (n + 1 - k), f j
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    -- ⊢ ∏ j in Ico k m, f (n - j) = ∏ j in image (fun x => n - x) (Ico k m), f j
    refine' (prod_image _).symm
    -- ⊢ ∀ (x : ℕ), x ∈ Ico k m → ∀ (y : ℕ), y ∈ Ico k m → n - x = n - y → x = y
    simp only [mem_Ico]
    -- ⊢ ∀ (x : ℕ), k ≤ x ∧ x < m → ∀ (y : ℕ), k ≤ y ∧ y < m → n - x = n - y → x = y
    rintro i ⟨_, im⟩ j ⟨_, jm⟩ Hij
    -- ⊢ i = j
    rw [← tsub_tsub_cancel_of_le (this _ im), Hij, tsub_tsub_cancel_of_le (this _ jm)]
    -- 🎉 no goals
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

theorem prod_range_reflect (f : ℕ → β) (n : ℕ) :
    (∏ j in range n, f (n - 1 - j)) = ∏ j in range n, f j := by
  cases n
  -- ⊢ ∏ j in range zero, f (zero - 1 - j) = ∏ j in range zero, f j
  · simp
    -- 🎉 no goals
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    -- ⊢ ∏ x in Ico 0 (succ n✝), f (n✝ - x) = ∏ x in Ico 0 (succ n✝), f x
    rw [prod_Ico_reflect _ _ le_rfl]
    -- ⊢ ∏ j in Ico (n✝ + 1 - (n✝ + 1)) (n✝ + 1 - 0), f j = ∏ x in Ico 0 (succ n✝), f x
    simp
    -- 🎉 no goals
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
  | n + 1 => by simp [Finset.range_succ, prod_range_add_one_eq_factorial n]
                -- 🎉 no goals
#align finset.prod_range_add_one_eq_factorial Finset.prod_range_add_one_eq_factorial

section GaussSum

/-- Gauss' summation formula -/
theorem sum_range_id_mul_two (n : ℕ) : (∑ i in range n, i) * 2 = n * (n - 1) :=
  calc
    (∑ i in range n, i) * 2 = (∑ i in range n, i) + ∑ i in range n, (n - 1 - i) :=
    by rw [sum_range_reflect (fun i => i) n, mul_two]
       -- 🎉 no goals
    _ = ∑ i in range n, (i + (n - 1 - i)) := sum_add_distrib.symm
    _ = ∑ i in range n, (n - 1) :=
      sum_congr rfl fun i hi => add_tsub_cancel_of_le <| Nat.le_pred_of_lt <| mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]
                          -- 🎉 no goals
#align finset.sum_range_id_mul_two Finset.sum_range_id_mul_two

/-- Gauss' summation formula -/
theorem sum_range_id (n : ℕ) : ∑ i in range n, i = n * (n - 1) / 2 := by
  rw [← sum_range_id_mul_two n, Nat.mul_div_cancel _ zero_lt_two]
  -- 🎉 no goals
#align finset.sum_range_id Finset.sum_range_id

end GaussSum

end Generic

section Nat

variable {β : Type*}

variable (f g : ℕ → β) {m n : ℕ}

section Group

variable [CommGroup β]

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

end Group

end Nat

section Module

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (f : ℕ → R) (g : ℕ → M) {m n : ℕ}

open Finset

-- The partial sum of `g`, starting from zero
local notation "G " n:80 => ∑ i in range n, g i

/-- **Summation by parts**, also known as **Abel's lemma** or an **Abel transformation** -/
theorem sum_Ico_by_parts (hmn : m < n) :
    ∑ i in Ico m n, f i • g i =
      f (n - 1) • G n - f m • G m - ∑ i in Ico m (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  have h₁ : (∑ i in Ico (m + 1) n, f i • G i) = ∑ i in Ico m (n - 1), f (i + 1) • G (i + 1) := by
    rw [← Nat.sub_add_cancel (Nat.one_le_of_lt hmn), ← sum_Ico_add']
    simp only [ge_iff_le, tsub_le_iff_right, add_le_iff_nonpos_left, nonpos_iff_eq_zero,
      tsub_eq_zero_iff_le, add_tsub_cancel_right]
  have h₂ :
    (∑ i in Ico (m + 1) n, f i • G (i + 1)) =
      (∑ i in Ico m (n - 1), f i • G (i + 1)) + f (n - 1) • G n - f m • G (m + 1) := by
    rw [← sum_Ico_sub_bot _ hmn, ← sum_Ico_succ_sub_top _ (Nat.le_pred_of_lt hmn),
      Nat.sub_add_cancel (pos_of_gt hmn), sub_add_cancel]
  rw [sum_eq_sum_Ico_succ_bot hmn]
  -- ⊢ f m • g m + ∑ k in Ico (m + 1) n, f k • g k = f (n - 1) • ∑ i in range n, g  …
  -- porting note: the following used to be done with `conv`
  have h₃: (Finset.sum (Ico (m + 1) n) fun i => f i • g i) =
             (Finset.sum (Ico (m + 1) n) fun i =>
                f i • ((Finset.sum (Finset.range (i + 1)) g) -
                        (Finset.sum (Finset.range i) g))) := by
    congr; funext; rw [← sum_range_succ_sub_sum g]
  rw [h₃]
  -- ⊢ f m • g m + ∑ i in Ico (m + 1) n, f i • (Finset.sum (range (i + 1)) g - Fins …
  simp_rw [smul_sub, sum_sub_distrib, h₂, h₁]
  -- ⊢ f m • g m + (∑ i in Ico m (n - 1), f i • ∑ i in range (i + 1), g i + f (n -  …
  -- porting note: the following used to be done with `conv`
  have h₄ : ((((Finset.sum (Ico m (n - 1)) fun i => f i • Finset.sum (range (i + 1)) fun i => g i) +
      f (n - 1) • Finset.sum (range n) fun i => g i) -
      f m • Finset.sum (range (m + 1)) fun i => g i) -
      Finset.sum (Ico m (n - 1)) fun i => f (i + 1) • Finset.sum (range (i + 1)) fun i => g i) =
      f (n - 1) • (range n).sum g - f m • (range (m + 1)).sum g +
      Finset.sum (Ico m (n - 1)) (fun i => f i • (range (i + 1)).sum g -
      f (i + 1) • (range (i + 1)).sum g) := by
    rw [← add_sub, add_comm, ←add_sub, ← sum_sub_distrib]
  rw [h₄]
  -- ⊢ f m • g m + (f (n - 1) • Finset.sum (range n) g - f m • Finset.sum (range (m …
  have : ∀ i, f i • G (i + 1) - f (i + 1) • G (i + 1) = -((f (i + 1) - f i) • G (i + 1)) := by
    intro i
    rw [sub_smul]
    abel
  simp_rw [this, sum_neg_distrib, sum_range_succ, smul_add]
  -- ⊢ f m • g m + (f (n - 1) • Finset.sum (range n) g - (f m • ∑ x in range m, g x …
  abel
  -- 🎉 no goals
  -- 🎉 no goals
#align finset.sum_Ico_by_parts Finset.sum_Ico_by_parts

variable (n)

/-- **Summation by parts** for ranges -/
theorem sum_range_by_parts :
    ∑ i in range n, f i • g i =
      f (n - 1) • G n - ∑ i in range (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  by_cases hn : n = 0
  -- ⊢ ∑ i in range n, f i • g i = f (n - 1) • ∑ i in range n, g i - ∑ i in range ( …
  · simp [hn]
    -- 🎉 no goals
  · rw [range_eq_Ico, sum_Ico_by_parts f g (Nat.pos_of_ne_zero hn), sum_range_zero, smul_zero,
      sub_zero, range_eq_Ico]
#align finset.sum_range_by_parts Finset.sum_range_by_parts

end Module

end Finset

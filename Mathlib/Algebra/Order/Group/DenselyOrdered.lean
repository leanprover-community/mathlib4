/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Lemmas about densely linearly ordered groups.
-/

variable {α : Type*}

section DenselyOrdered

variable [Group α] [LinearOrder α]
variable [MulLeftMono α]
variable [DenselyOrdered α] {a b : α}

@[to_additive]
theorem le_of_forall_lt_one_mul_le (h : ∀ ε < 1, a * ε ≤ b) : a ≤ b :=
  le_of_forall_one_lt_le_mul (α := αᵒᵈ) h

@[to_additive]
theorem le_of_forall_one_lt_div_le (h : ∀ ε : α, 1 < ε → a / ε ≤ b) : a ≤ b :=
  le_of_forall_lt_one_mul_le fun ε ε1 => by
    simpa only [div_eq_mul_inv, inv_inv] using h ε⁻¹ (Left.one_lt_inv_iff.2 ε1)

@[to_additive]
theorem le_iff_forall_lt_one_mul_le : a ≤ b ↔ ∀ ε < 1, a * ε ≤ b :=
  le_iff_forall_one_lt_le_mul (α := αᵒᵈ)

end DenselyOrdered

section DenselyOrdered

@[to_additive]
private lemma exists_lt_mul_left [Group α] [LT α] [DenselyOrdered α]
    [MulRightStrictMono α] {a b c : α} (hc : c < a * b) :
    ∃ a' < a, c < a' * b := by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul.1 hc'⟩

@[to_additive]
private lemma exists_lt_mul_right [CommGroup α] [LT α] [DenselyOrdered α]
    [MulLeftStrictMono α] {a b c : α} (hc : c < a * b) :
    ∃ b' < b, c < a * b' := by
  obtain ⟨a', hc', ha'⟩ := exists_between (div_lt_iff_lt_mul'.2 hc)
  exact ⟨a', ha', div_lt_iff_lt_mul'.1 hc'⟩

@[to_additive]
private lemma exists_mul_left_lt [Group α] [LT α] [DenselyOrdered α]
    [MulRightStrictMono α] {a b c : α} (hc : a * b < c) :
    ∃ a' > a, a' * b < c := by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt.1 hc'⟩

@[to_additive]
private lemma exists_mul_right_lt [CommGroup α] [LT α] [DenselyOrdered α]
    [MulLeftStrictMono α] {a b c : α} (hc : a * b < c) :
    ∃ b' > b, a * b' < c := by
  obtain ⟨a', ha', hc'⟩ := exists_between (lt_div_iff_mul_lt'.2 hc)
  exact ⟨a', ha', lt_div_iff_mul_lt'.1 hc'⟩

@[to_additive]
lemma le_mul_of_forall_lt [CommGroup α] [LinearOrder α] [MulLeftMono α]
    [DenselyOrdered α] {a b c : α} (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') :
    c ≤ a * b := by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_mul_left_lt hd
  obtain ⟨b', hb', hd⟩ := exists_mul_right_lt hd
  exact (h a' ha' b' hb').trans hd.le

@[to_additive]
lemma mul_le_of_forall_lt [CommGroup α] [LinearOrder α] [MulLeftMono α]
    [DenselyOrdered α] {a b c : α} (h : ∀ a' < a, ∀ b' < b, a' * b' ≤ c) :
    a * b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
  exact hd.le.trans (h a' ha' b' hb')

end DenselyOrdered

variable {M : Type*} [LinearOrder M] [DenselyOrdered M] {x : M}

section Monoid
variable [CommMonoid M] [ExistsMulOfLE M] [IsOrderedCancelMonoid M]

@[to_additive]
private theorem exists_pow_two_le_of_one_lt (hx : 1 < x) : ∃ y : M, 1 < y ∧ y ^ 2 ≤ x := by
  obtain ⟨y, hy, hyx⟩ := exists_between hx
  obtain hyx | hxy := le_total (y ^ 2) x
  · exact ⟨y, hy, hyx⟩
  obtain ⟨z, hz, rfl⟩ := exists_one_lt_mul_of_lt' hyx
  exact ⟨z, hz, by simpa [pow_succ] using hxy⟩

@[to_additive]
theorem exists_pow_lt_of_one_lt (hx : 1 < x) : ∀ n : ℕ, ∃ y : M, 1 < y ∧ y ^ n < x
  | 0 => ⟨x, by simpa⟩
  | 1 => by simpa using exists_between hx
  | n + 2 => by
    obtain ⟨y, hy, hyx⟩ := exists_pow_lt_of_one_lt hx (n + 1)
    obtain ⟨z, hz, hzy⟩ := exists_pow_two_le_of_one_lt hy
    refine ⟨z, hz, hyx.trans_le' ?_⟩
    calc z ^ (n + 2)
      _ ≤ z ^ (2 * (n + 1)) := pow_right_monotone hz.le (by omega)
      _ = (z ^ 2) ^ (n + 1) := by rw [pow_mul]
      _ ≤ y ^ (n + 1) := pow_le_pow_left' hzy (n + 1)

end Monoid

section Group
variable [CommGroup M] [IsOrderedCancelMonoid M]

@[to_additive]
theorem exists_lt_pow_of_lt_one (hx : x < 1) (n : ℕ) : ∃ y : M, y < 1 ∧ x < y ^ n := by
  obtain ⟨y, hy, hy'⟩ := exists_pow_lt_of_one_lt (one_lt_inv_of_inv hx) n
  use y⁻¹, inv_lt_one_of_one_lt hy
  simpa [lt_inv'] using hy'

end Group

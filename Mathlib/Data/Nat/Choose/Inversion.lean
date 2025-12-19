/-
Copyright (c) 2025 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Nat.Choose.Sum

/-! # Binomial inversion

This file includes two versions of binomial inversion and a simple application thereof.

-/

@[expose] public section

open Finset

namespace Int

variable {G : Type*} [AddCommGroup G]

theorem alternating_sum_choose_mul_of_alternating_sum_choose_mul {f g : ℕ → G} (m : ℕ)
    (h : ∀ n, ∑ k ∈ Finset.range (n + 1), (((-1) ^ k * ↑(n.choose k) : ℤ)) • f k = g n) :
    ∑ k ∈ Finset.range (m + 1), ((-1) ^ k * (↑(m.choose k) : ℤ)) • g k = f m :=
  calc
    _ = ∑ k ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (k + 1),
          ((-1) ^ k * (↑(m.choose k) : ℤ)) • ((-1) ^ i * (↑(k.choose i) : ℤ)) • f i := by
      congr!
      rw [← h, sum_zsmul]
    _ = ∑ i ∈ Finset.range (m + 1), ∑ k ∈ Ico i (m + 1),
          ((-1) ^ k * (↑(m.choose k) : ℤ)) • ((-1) ^ i * (↑(k.choose i) : ℤ)) • f i := by
        rw [range_eq_Ico, sum_Ico_Ico_comm]
    _ = ∑ i ∈ Finset.range (m + 1), ∑ k ∈ Ico i (m + 1), ((-1) ^ k *
          ((↑(Nat.choose m i) : ℤ) * ((-1) ^ i * ↑(Nat.choose (m - i) (k - i) : ℤ)))) • f i := by
      congr! 2 with a _ b h'
      rw [← mul_zsmul, mul_assoc, ← mul_assoc, mul_assoc ((-1) ^ _), mul_left_comm _ ((-1) ^ a),
        ← Nat.cast_mul, Nat.choose_mul (List.left_le_of_mem_range' h'), Nat.cast_mul,
        mul_left_comm (↑(m.choose a) : ℤ)]
    _ = ∑ i ∈ Finset.range (m + 1), (Nat.choose m i *
          if i = m then (1 : ℤ) else 0) • f i := by
      congr! 1 with n hn
      have : (if n = m then (1 : ℤ) else (0 : ℤ)) = if m - n = 0 then 1 else 0 := by
        refine ite_cond_congr ?_
        simp only [Nat.sub_eq_zero_iff_le, eq_iff_iff]
        constructor <;> intro h
        · rw [h]
        · exact le_antisymm (mem_range_succ_iff.mp hn) h
      rw [this, ← alternating_sum_range_choose, mul_sum, sum_smul]
      nth_rw 1 [← zero_add n]
      rw [← Nat.sub_add_cancel (mem_range_le hn), Nat.sub_add_comm (mem_range_succ_iff.mp hn),
        ← Finset.sum_Ico_add, Nat.Ico_zero_eq_range]
      congr! 1
      nth_rw 2 [add_comm n]
      rw [Nat.add_sub_cancel]
      ring_nf
      rw [mul_comm n 2, Even.neg_one_pow (even_two_mul n), mul_one]
    _ = f m := by simp

/-- **Binomial inversion**, symmetric version. -/
theorem alternating_sum_choose_mul_eq_iff (f g : ℕ → G) :
    (∀ n, ∑ k ∈ Finset.range (n + 1), ((-1) ^ k * (↑(n.choose k) : ℤ)) • f k = g n) ↔
    ∀ n, ∑ k ∈ Finset.range (n + 1), ((-1) ^ k * (↑(n.choose k) : ℤ)) • g k = f n :=
  ⟨fun h _ ↦ alternating_sum_choose_mul_of_alternating_sum_choose_mul _ h,
  fun h _ ↦ alternating_sum_choose_mul_of_alternating_sum_choose_mul _ h⟩

/-- **Binomial inversion**, asymmetric version. -/
theorem alternating_sum_choose_mul_eq_iff' (f g : ℕ → G) :
    (∀ n, ∑ k ∈ Finset.range (n + 1), (n.choose k) • f k = g n) ↔
    ∀ n, ∑ k ∈ Finset.range (n + 1), ((- 1) ^ (n + k) * (↑(n.choose k) : ℤ)) • g k = f n := by
  apply Iff.trans (b := ∀ (n : ℕ),
    ∑ k ∈ Finset.range (n + 1), ((-1) ^ k *(↑(n.choose k) : ℤ)) • (-1) ^ k • f k = g n)
  · refine forall_congr' ?_
    intro
    refine Eq.congr ?_ rfl
    congr! 1
    rw [smul_smul, ← Lean.Grind.IntModule.zsmul_natCast_eq_nsmul]
    ring_nf
    simp
  · rw [alternating_sum_choose_mul_eq_iff (fun n ↦ (-1) ^ n • f n) g]
    refine forall_congr' ?_
    intro n
    rw [← IsUnit.smul_left_cancel (y := f n) (isUnit_neg_one_pow (R := ℤ) n)]
    refine Eq.congr ?_ rfl
    rw [smul_sum]
    congr! 1
    rw [smul_smul, ← mul_assoc, ← pow_add, ← add_assoc, ← Nat.two_mul n, pow_add]
    simp

theorem alternating_sum_choose_mul_choose (n m : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (↑(n.choose k) : ℤ) * (k.choose m)
    = (-1) ^ m * if n = m then 1 else 0 := by
  apply alternating_sum_choose_mul_of_alternating_sum_choose_mul
  intro k
  by_cases h : m < k + 1 <;> simp only [reduceNeg, mul_ite, mul_one, mul_zero, Int.zsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_range, h, ↓reduceIte]
  · rw [mul_right_comm, ← pow_add, ← Nat.two_mul m, Even.neg_one_pow (even_two_mul m), one_mul]
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_succ_le (Nat.le_of_not_lt h)), Int.natCast_zero]

theorem alternating_sum_id_mul_choose (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1) ^ k * ((n.choose k) : ℤ) * k = - if n = 1 then 1 else 0 := by
  rw [← neg_one_mul (if n = 1 then 1 else 0), ← pow_one (-1),
    ← alternating_sum_choose_mul_choose n 1]
  congr! 1
  simp

end Int

/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Peel
import Mathlib.Tactic.Recall

/-!
# IMO 2024 Q1

Determine all real numbers $\alpha$ such that, for every positive integer $n$, the integer
\[
\lfloor \alpha \rfloor + \lfloor 2\alpha \rfloor + \cdots + \lfloor n\alpha \rfloor
\]
is a multiple of~$n$.

We follow Solution 3 from the
[official solutions](https://www.imo2024.uk/s/IMO-2024-Paper-1-Solutions.pdf).
First reducing modulo 2, any answer that is not a multiple of 2 is inductively shown to be
contained in a decreasing sequence of intervals, with empty intersection.
-/

open Finset

namespace Imo2024Q1

/-- The condition of the problem. -/
def Condition (α : ℝ) : Prop := (∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, ⌊i * α⌋)

/-- This is to be determined by the solver of the original problem. -/
def solutionSet : Set ℝ := {α : ℝ | ∃ m : ℤ, α = 2 * m}

lemma condition_two_mul_int (m : ℤ) : Condition (2 * m) := by
  rintro n -
  suffices (n : ℤ) ∣ ∑ i ∈ Finset.Icc 0 n, ⌊((i * (2 * m) : ℤ) : ℝ)⌋ by
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert_zero (by norm_num)] at this
    exact_mod_cast this
  simp_rw [Int.floor_intCast, ← sum_mul, ← Ico_succ_right_eq_Icc, ← range_eq_Ico, ← mul_assoc]
  apply dvd_mul_of_dvd_left
  rw [← Nat.cast_sum, ← Nat.cast_ofNat (n := 2), ← Nat.cast_mul, Finset.sum_range_id_mul_two]
  simp

lemma condition_sub_two_mul_int_iff {α : ℝ} (m : ℤ) : Condition (α - 2 * m) ↔ Condition α := by
  peel with n hn
  apply dvd_iff_dvd_of_dvd_sub
  simp_rw [← Finset.sum_sub_distrib, mul_sub]
  norm_cast
  simp_rw [Int.floor_sub_intCast, sub_sub_cancel_left]
  convert condition_two_mul_int (-m) n hn
  norm_cast
  rw [Int.floor_intCast]
  simp

lemma condition_toIcoMod_iff {α : ℝ} :
    Condition (toIcoMod (by norm_num : (0 : ℝ) < 2) 0 α) ↔ Condition α := by
  rw [toIcoMod, zsmul_eq_mul, mul_comm, condition_sub_two_mul_int_iff]

namespace Condition

variable {α : ℝ} (hc : Condition α)
include hc

lemma mem_Ico_one_of_mem_Ioo (h : α ∈ Set.Ioo 0 2) : α ∈ Set.Ico 1 2 := by
  rcases h with ⟨h0, h2⟩
  refine ⟨?_, h2⟩
  by_contra! hn
  have hr : 1 < ⌈α⁻¹⌉₊ := by
    rw [Nat.lt_ceil]
    exact_mod_cast (one_lt_inv₀ h0).2 hn
  apply hr.ne'
  suffices ⌈α⁻¹⌉₊ = (1 : ℤ) from mod_cast this
  apply Int.eq_one_of_dvd_one (Int.zero_le_ofNat _)
  convert hc ⌈α⁻¹⌉₊ (zero_lt_one.trans hr)
  rw [← Finset.add_sum_Ico_eq_sum_Icc hr.le]
  convert (add_zero _).symm
  · rw [Int.floor_eq_iff]
    constructor
    · rw [Int.cast_one]
      calc 1 ≤ α⁻¹ * α := by simp [h0.ne']
        _ ≤ ⌈α⁻¹⌉₊ * α := by gcongr; exact Nat.le_ceil α⁻¹
    · calc ⌈α⁻¹⌉₊ * α
        _ < (α⁻¹ + 1) * α := by gcongr; exact Nat.ceil_lt_add_one (inv_nonneg.2 h0.le)
        _ = 1 + α := by field_simp [h0.ne']
        _ ≤ (1 : ℕ) + 1 := by gcongr; norm_cast
  · apply Finset.sum_eq_zero
    intro x hx
    rw [Int.floor_eq_zero_iff]
    refine ⟨by positivity, ?_⟩
    rw [Finset.mem_Ico, Nat.lt_ceil] at hx
    calc x * α < α⁻¹ * α := by gcongr; exact hx.2
      _ = 1 := by simp [h0.ne']

lemma mem_Ico_n_of_mem_Ioo (h : α ∈ Set.Ioo 0 2) {n : ℕ} (hn : 0 < n) :
    α ∈ Set.Ico ((2 * n - 1) / n : ℝ) 2 := by
  suffices ∑ i ∈ Finset.Icc 1 n, ⌊i * α⌋ = n ^ 2 ∧ α ∈ Set.Ico ((2 * n - 1) / n : ℝ) 2 from this.2
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨h1, h2⟩ := hc.mem_Ico_one_of_mem_Ioo h
    simp only [zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_mul, one_pow,
               Int.floor_eq_iff, Int.cast_one, mul_one, div_one, Set.mem_Ico, tsub_le_iff_right]
    exact ⟨⟨h1, by linarith⟩, by linarith, h2⟩
  | succ k kpos hk =>
    rcases hk with ⟨hks, hkl, hk2⟩
    have hs : (∑ i ∈ Finset.Icc 1 (k + 1), ⌊i * α⌋) =
         ⌊(k + 1 : ℕ) * α⌋ + ((k : ℕ) : ℤ) ^ 2 := by
      have hn11 : k + 1 ∉ Finset.Icc 1 k := by
        rw [Finset.mem_Icc]
        omega
      rw [← insert_Icc_right_eq_Icc_add_one (Nat.le_add_left 1 k), sum_insert hn11, hks]
    specialize hc (k + 1) k.succ_pos
    rw [hs] at hc ⊢
    have hkl' : 2 * k ≤ ⌊(k + 1 : ℕ) * α⌋ := by
      rw [Int.le_floor]
      calc ((2 * k : ℤ) : ℝ) = ((2 * k : ℤ) : ℝ) + 0 := (add_zero _).symm
        _ ≤ ((2 * k : ℤ) : ℝ) + (k - 1) / k := by gcongr; norm_cast; positivity
        _ = (k + 1 : ℕ) * ((2 * (k : ℕ) - 1) / ((k : ℕ) : ℝ)) := by field_simp; ring
        _ ≤ (k + 1 : ℕ) * α := by gcongr
    have hk2' : ⌊(k + 1 : ℕ) * α⌋ < (k + 1 : ℕ) * 2 := by
      rw [Int.floor_lt]
      push_cast
      gcongr
    have hk' : ⌊(k + 1 : ℕ) * α⌋ = 2 * k + 1 := by
      by_contra
      rw [show ⌊(k + 1 : ℕ) * α⌋ = 2 * k by omega] at hc
      have hc' : ((k + 1 : ℕ) : ℤ) ∣ ((k + 1 : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ) - 1 := by
        convert hc using 1
        push_cast
        ring
      rw [dvd_sub_right (dvd_mul_right _ _), ← isUnit_iff_dvd_one, Int.isUnit_iff] at hc'
      omega
    rw [hk']
    refine ⟨?_, ?_, h.2⟩
    · push_cast
      ring
    · rw [Int.floor_eq_iff] at hk'
      rw [div_le_iff₀ (by norm_cast; omega), mul_comm α]
      convert hk'.1
      push_cast
      ring

end Condition

lemma not_condition_of_mem_Ioo {α : ℝ} (h : α ∈ Set.Ioo 0 2) : ¬Condition α := by
  intro hc
  let n : ℕ := ⌊(2 - α)⁻¹⌋₊ + 1
  have hn : 0 < n := by omega
  have hna := (hc.mem_Ico_n_of_mem_Ioo h hn).1
  rcases h with ⟨-, h2⟩
  have hna' : 2 - (n : ℝ)⁻¹ ≤ α := by
    convert hna using 1
    field_simp
  rw [sub_eq_add_neg, ← le_sub_iff_add_le', neg_le, neg_sub] at hna'
  rw [le_inv_comm₀ (by linarith) (mod_cast hn), ← not_lt] at hna'
  apply hna'
  exact_mod_cast Nat.lt_floor_add_one (_ : ℝ)

lemma condition_iff_of_mem_Ico {α : ℝ} (h : α ∈ Set.Ico 0 2) : Condition α ↔ α = 0 := by
  constructor
  · intro hc
    cases Set.eq_left_or_mem_Ioo_of_mem_Ico h with
    | inl h => exact h
    | inr ho => exact False.elim (not_condition_of_mem_Ioo ho hc)
  · rintro rfl
    convert condition_two_mul_int 0
    norm_num

recall Imo2024Q1.Condition (α : ℝ) := (∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, ⌊i * α⌋)
recall Imo2024Q1.solutionSet := {α : ℝ | ∃ m : ℤ, α = 2 * m}

theorem result (α : ℝ) : Condition α ↔ α ∈ solutionSet := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← condition_toIcoMod_iff, condition_iff_of_mem_Ico (toIcoMod_mem_Ico' _ _),
        ← AddCommGroup.modEq_iff_toIcoMod_eq_left, AddCommGroup.ModEq] at h
    simp_rw [sub_zero] at h
    rcases h with ⟨m, rfl⟩
    rw [zsmul_eq_mul, mul_comm]
    simp [solutionSet]
  · rintro ⟨m, rfl⟩
    exact condition_two_mul_int m

end Imo2024Q1

/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Wieser
-/
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Algebra.Order.Module.Pointwise
import Mathlib.Data.Real.Archimedean

/-!
# Pointwise operations on sets of reals

This file relates `sInf (a • s)`/`sSup (a • s)` with `a • sInf s`/`a • sSup s` for `s : Set ℝ`.

From these, it relates `⨅ i, a • f i` / `⨆ i, a • f i` with `a • (⨅ i, f i)` / `a • (⨆ i, f i)`,
and provides lemmas about distributing `*` over `⨅` and `⨆`.

## TODO

This is true more generally for conditionally complete linear order whose default value is `0`. We
don't have those yet.
-/

assert_not_exists Finset

open Set

open Pointwise

variable {ι : Sort*} {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

section MulActionWithZero

variable [MulActionWithZero α ℝ] [OrderedSMul α ℝ] {a : α}

theorem Real.sInf_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : sInf (a • s) = a • sInf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRight ha').map_csInf' hs h).symm
  · rw [Real.sInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_pos ha').1 h),
        Real.sInf_of_not_bddBelow h, smul_zero]

theorem Real.smul_iInf_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨅ i, a • f i :=
  (Real.sInf_smul_of_nonneg ha _).symm.trans <| congr_arg sInf <| (range_comp _ _).symm

theorem Real.sSup_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : sSup (a • s) = a • sSup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRight ha').map_csSup' hs h).symm
  · rw [Real.sSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_pos ha').1 h),
        Real.sSup_of_not_bddAbove h, smul_zero]

theorem Real.smul_iSup_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨆ i, a • f i :=
  (Real.sSup_smul_of_nonneg ha _).symm.trans <| congr_arg sSup <| (range_comp _ _).symm

end MulActionWithZero

section Module

variable [Module α ℝ] [OrderedSMul α ℝ] {a : α}

theorem Real.sInf_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : sInf (a • s) = a • sSup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRightDual ℝ ha').map_csSup' hs h).symm
  · rw [Real.sInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_neg ha').1 h),
        Real.sSup_of_not_bddAbove h, smul_zero]

theorem Real.smul_iSup_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨅ i, a • f i :=
  (Real.sInf_smul_of_nonpos ha _).symm.trans <| congr_arg sInf <| (range_comp _ _).symm

theorem Real.sSup_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : sSup (a • s) = a • sInf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRightDual ℝ ha').map_csInf' hs h).symm
  · rw [Real.sSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_neg ha').1 h),
        Real.sInf_of_not_bddBelow h, smul_zero]

theorem Real.smul_iInf_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨆ i, a • f i :=
  (Real.sSup_smul_of_nonpos ha _).symm.trans <| congr_arg sSup <| (range_comp _ _).symm

end Module

/-! ## Special cases for real multiplication -/


section Mul

variable {r : ℝ}

theorem Real.mul_iInf_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨅ i, r * f i :=
  Real.smul_iInf_of_nonneg ha f

theorem Real.mul_iSup_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨆ i, r * f i :=
  Real.smul_iSup_of_nonneg ha f

theorem Real.mul_iInf_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨆ i, r * f i :=
  Real.smul_iInf_of_nonpos ha f

theorem Real.mul_iSup_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨅ i, r * f i :=
  Real.smul_iSup_of_nonpos ha f

theorem Real.iInf_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨅ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_iInf_of_nonneg ha, mul_comm]

theorem Real.iSup_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨆ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_iSup_of_nonneg ha, mul_comm]

theorem Real.iInf_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨅ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_iInf_of_nonpos ha, mul_comm]

theorem Real.iSup_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨆ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_iSup_of_nonpos ha, mul_comm]

end Mul

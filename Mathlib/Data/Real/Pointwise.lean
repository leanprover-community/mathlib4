/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Wieser
-/
import Mathlib.Algebra.Order.Module
import Mathlib.Data.Real.Basic

#align_import data.real.pointwise from "leanprover-community/mathlib"@"dde670c9a3f503647fd5bfdf1037bad526d3397a"

/-!
# Pointwise operations on sets of reals

This file relates `sInf (a • s)`/`sSup (a • s)` with `a • sInf s`/`a • sSup s` for `s : Set ℝ`.

From these, it relates `⨅ i, a • f i` / `⨆ i, a • f i` with `a • (⨅ i, f i)` / `a • (⨆ i, f i)`,
and provides lemmas about distributing `*` over `⨅` and `⨆`.

# TODO

This is true more generally for conditionally complete linear order whose default value is `0`. We
don't have those yet.
-/


open Set

open Pointwise

variable {ι : Sort*} {α : Type*} [LinearOrderedField α]

section MulActionWithZero

variable [MulActionWithZero α ℝ] [OrderedSMul α ℝ] {a : α}

theorem Real.sInf_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : sInf (a • s) = a • sInf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  -- ⊢ sInf (a • ∅) = a • sInf ∅
  · rw [smul_set_empty, Real.sInf_empty, smul_zero]
    -- 🎉 no goals
  obtain rfl | ha' := ha.eq_or_lt
  -- ⊢ sInf (0 • s) = 0 • sInf s
  · rw [zero_smul_set hs, zero_smul]
    -- ⊢ sInf 0 = 0
    exact csInf_singleton 0
    -- 🎉 no goals
  by_cases h : BddBelow s
  -- ⊢ sInf (a • s) = a • sInf s
  · exact ((OrderIso.smulLeft ℝ ha').map_csInf' hs h).symm
    -- 🎉 no goals
  · rw [Real.sInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_pos ha').1 h),
        Real.sInf_of_not_bddBelow h, smul_zero]
#align real.Inf_smul_of_nonneg Real.sInf_smul_of_nonneg

theorem Real.smul_iInf_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨅ i, a • f i :=
  (Real.sInf_smul_of_nonneg ha _).symm.trans <| congr_arg sInf <| (range_comp _ _).symm
#align real.smul_infi_of_nonneg Real.smul_iInf_of_nonneg

theorem Real.sSup_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : sSup (a • s) = a • sSup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  -- ⊢ sSup (a • ∅) = a • sSup ∅
  · rw [smul_set_empty, Real.sSup_empty, smul_zero]
    -- 🎉 no goals
  obtain rfl | ha' := ha.eq_or_lt
  -- ⊢ sSup (0 • s) = 0 • sSup s
  · rw [zero_smul_set hs, zero_smul]
    -- ⊢ sSup 0 = 0
    exact csSup_singleton 0
    -- 🎉 no goals
  by_cases h : BddAbove s
  -- ⊢ sSup (a • s) = a • sSup s
  · exact ((OrderIso.smulLeft ℝ ha').map_csSup' hs h).symm
    -- 🎉 no goals
  · rw [Real.sSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_pos ha').1 h),
        Real.sSup_of_not_bddAbove h, smul_zero]
#align real.Sup_smul_of_nonneg Real.sSup_smul_of_nonneg

theorem Real.smul_iSup_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨆ i, a • f i :=
  (Real.sSup_smul_of_nonneg ha _).symm.trans <| congr_arg sSup <| (range_comp _ _).symm
#align real.smul_supr_of_nonneg Real.smul_iSup_of_nonneg

end MulActionWithZero

section Module

variable [Module α ℝ] [OrderedSMul α ℝ] {a : α}

theorem Real.sInf_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : sInf (a • s) = a • sSup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  -- ⊢ sInf (a • ∅) = a • sSup ∅
  · rw [smul_set_empty, Real.sInf_empty, Real.sSup_empty, smul_zero]
    -- 🎉 no goals
  obtain rfl | ha' := ha.eq_or_lt
  -- ⊢ sInf (0 • s) = 0 • sSup s
  · rw [zero_smul_set hs, zero_smul]
    -- ⊢ sInf 0 = 0
    exact csInf_singleton 0
    -- 🎉 no goals
  by_cases h : BddAbove s
  -- ⊢ sInf (a • s) = a • sSup s
  · exact ((OrderIso.smulLeftDual ℝ ha').map_csSup' hs h).symm
    -- 🎉 no goals
  · rw [Real.sInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_neg ha').1 h),
        Real.sSup_of_not_bddAbove h, smul_zero]
#align real.Inf_smul_of_nonpos Real.sInf_smul_of_nonpos

theorem Real.smul_iSup_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨅ i, a • f i :=
  (Real.sInf_smul_of_nonpos ha _).symm.trans <| congr_arg sInf <| (range_comp _ _).symm
#align real.smul_supr_of_nonpos Real.smul_iSup_of_nonpos

theorem Real.sSup_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : sSup (a • s) = a • sInf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  -- ⊢ sSup (a • ∅) = a • sInf ∅
  · rw [smul_set_empty, Real.sSup_empty, Real.sInf_empty, smul_zero]
    -- 🎉 no goals
  obtain rfl | ha' := ha.eq_or_lt
  -- ⊢ sSup (0 • s) = 0 • sInf s
  · rw [zero_smul_set hs, zero_smul]
    -- ⊢ sSup 0 = 0
    exact csSup_singleton 0
    -- 🎉 no goals
  by_cases h : BddBelow s
  -- ⊢ sSup (a • s) = a • sInf s
  · exact ((OrderIso.smulLeftDual ℝ ha').map_csInf' hs h).symm
    -- 🎉 no goals
  · rw [Real.sSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_neg ha').1 h),
        Real.sInf_of_not_bddBelow h, smul_zero]
#align real.Sup_smul_of_nonpos Real.sSup_smul_of_nonpos

theorem Real.smul_iInf_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨆ i, a • f i :=
  (Real.sSup_smul_of_nonpos ha _).symm.trans <| congr_arg sSup <| (range_comp _ _).symm
#align real.smul_infi_of_nonpos Real.smul_iInf_of_nonpos

end Module

/-! ## Special cases for real multiplication -/


section Mul

variable {r : ℝ}

theorem Real.mul_iInf_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨅ i, r * f i :=
  Real.smul_iInf_of_nonneg ha f
#align real.mul_infi_of_nonneg Real.mul_iInf_of_nonneg

theorem Real.mul_iSup_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨆ i, r * f i :=
  Real.smul_iSup_of_nonneg ha f
#align real.mul_supr_of_nonneg Real.mul_iSup_of_nonneg

theorem Real.mul_iInf_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨆ i, r * f i :=
  Real.smul_iInf_of_nonpos ha f
#align real.mul_infi_of_nonpos Real.mul_iInf_of_nonpos

theorem Real.mul_iSup_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨅ i, r * f i :=
  Real.smul_iSup_of_nonpos ha f
#align real.mul_supr_of_nonpos Real.mul_iSup_of_nonpos

theorem Real.iInf_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨅ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_iInf_of_nonneg ha, mul_comm]
  -- 🎉 no goals
#align real.infi_mul_of_nonneg Real.iInf_mul_of_nonneg

theorem Real.iSup_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨆ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_iSup_of_nonneg ha, mul_comm]
  -- 🎉 no goals
#align real.supr_mul_of_nonneg Real.iSup_mul_of_nonneg

theorem Real.iInf_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨅ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_iInf_of_nonpos ha, mul_comm]
  -- 🎉 no goals
#align real.infi_mul_of_nonpos Real.iInf_mul_of_nonpos

theorem Real.iSup_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨆ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_iSup_of_nonpos ha, mul_comm]
  -- 🎉 no goals
#align real.supr_mul_of_nonpos Real.iSup_mul_of_nonpos

end Mul

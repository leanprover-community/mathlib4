/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Wieser

! This file was ported from Lean 3 source module data.real.pointwise
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Module
import Mathlib.Data.Real.Basic

/-!
# Pointwise operations on sets of reals

This file relates `infₛ (a • s)`/`supₛ (a • s)` with `a • infₛ s`/`a • supₛ s` for `s : Set ℝ`.

From these, it relates `⨅ i, a • f i` / `⨆ i, a • f i` with `a • (⨅ i, f i)` / `a • (⨆ i, f i)`,
and provides lemmas about distributing `*` over `⨅` and `⨆`.

# TODO

This is true more generally for conditionally complete linear order whose default value is `0`. We
don't have those yet.
-/


open Set

open Pointwise

variable {ι : Sort _} {α : Type _} [LinearOrderedField α]

section MulActionWithZero

variable [MulActionWithZero α ℝ] [OrderedSMul α ℝ] {a : α}

theorem Real.infₛ_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : infₛ (a • s) = a • infₛ s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.infₛ_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact cinfₛ_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulLeft ℝ ha').map_cinfₛ' hs h).symm
  · rw [Real.infₛ_of_not_bddBelow (mt (bddBelow_smul_iff_of_pos ha').1 h),
        Real.infₛ_of_not_bddBelow h, smul_zero]
#align real.Inf_smul_of_nonneg Real.infₛ_smul_of_nonneg

theorem Real.smul_infᵢ_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨅ i, a • f i :=
  (Real.infₛ_smul_of_nonneg ha _).symm.trans <| congr_arg infₛ <| (range_comp _ _).symm
#align real.smul_infi_of_nonneg Real.smul_infᵢ_of_nonneg

theorem Real.supₛ_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : supₛ (a • s) = a • supₛ s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.supₛ_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csupₛ_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulLeft ℝ ha').map_csupₛ' hs h).symm
  · rw [Real.supₛ_of_not_bddAbove (mt (bddAbove_smul_iff_of_pos ha').1 h),
        Real.supₛ_of_not_bddAbove h, smul_zero]
#align real.Sup_smul_of_nonneg Real.supₛ_smul_of_nonneg

theorem Real.smul_supᵢ_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨆ i, a • f i :=
  (Real.supₛ_smul_of_nonneg ha _).symm.trans <| congr_arg supₛ <| (range_comp _ _).symm
#align real.smul_supr_of_nonneg Real.smul_supᵢ_of_nonneg

end MulActionWithZero

section Module

variable [Module α ℝ] [OrderedSMul α ℝ] {a : α}

theorem Real.infₛ_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : infₛ (a • s) = a • supₛ s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.infₛ_empty, Real.supₛ_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact cinfₛ_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulLeftDual ℝ ha').map_csupₛ' hs h).symm
  · rw [Real.infₛ_of_not_bddBelow (mt (bddBelow_smul_iff_of_neg ha').1 h),
        Real.supₛ_of_not_bddAbove h, smul_zero]
#align real.Inf_smul_of_nonpos Real.infₛ_smul_of_nonpos

theorem Real.smul_supᵢ_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨅ i, a • f i :=
  (Real.infₛ_smul_of_nonpos ha _).symm.trans <| congr_arg infₛ <| (range_comp _ _).symm
#align real.smul_supr_of_nonpos Real.smul_supᵢ_of_nonpos

theorem Real.supₛ_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : supₛ (a • s) = a • infₛ s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.supₛ_empty, Real.infₛ_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csupₛ_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulLeftDual ℝ ha').map_cinfₛ' hs h).symm
  · rw [Real.supₛ_of_not_bddAbove (mt (bddAbove_smul_iff_of_neg ha').1 h),
        Real.infₛ_of_not_bddBelow h, smul_zero]
#align real.Sup_smul_of_nonpos Real.supₛ_smul_of_nonpos

theorem Real.smul_infᵢ_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨆ i, a • f i :=
  (Real.supₛ_smul_of_nonpos ha _).symm.trans <| congr_arg supₛ <| (range_comp _ _).symm
#align real.smul_infi_of_nonpos Real.smul_infᵢ_of_nonpos

end Module

/-! ## Special cases for real multiplication -/


section Mul

variable {r : ℝ}

theorem Real.mul_infᵢ_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨅ i, r * f i :=
  Real.smul_infᵢ_of_nonneg ha f
#align real.mul_infi_of_nonneg Real.mul_infᵢ_of_nonneg

theorem Real.mul_supᵢ_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨆ i, r * f i :=
  Real.smul_supᵢ_of_nonneg ha f
#align real.mul_supr_of_nonneg Real.mul_supᵢ_of_nonneg

theorem Real.mul_infᵢ_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨆ i, r * f i :=
  Real.smul_infᵢ_of_nonpos ha f
#align real.mul_infi_of_nonpos Real.mul_infᵢ_of_nonpos

theorem Real.mul_supᵢ_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨅ i, r * f i :=
  Real.smul_supᵢ_of_nonpos ha f
#align real.mul_supr_of_nonpos Real.mul_supᵢ_of_nonpos

theorem Real.infᵢ_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨅ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_infᵢ_of_nonneg ha, mul_comm]
#align real.infi_mul_of_nonneg Real.infᵢ_mul_of_nonneg

theorem Real.supᵢ_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨆ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_supᵢ_of_nonneg ha, mul_comm]
#align real.supr_mul_of_nonneg Real.supᵢ_mul_of_nonneg

theorem Real.infᵢ_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨅ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_infᵢ_of_nonpos ha, mul_comm]
#align real.infi_mul_of_nonpos Real.infᵢ_mul_of_nonpos

theorem Real.supᵢ_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨆ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_supᵢ_of_nonpos ha, mul_comm]
#align real.supr_mul_of_nonpos Real.supᵢ_mul_of_nonpos

end Mul

/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Canonial inner product space from Preinner product space

This file defines the inner product space from a preinner product space (the inner product
can be degenerate) by quotienting the null space.

## Main results

-/

noncomputable section

open RCLike Submodule Quotient LinearMap InnerProductSpace InnerProductSpace.Core

variable (𝕜 E : Type*) [k: RCLike 𝕜]

section Nullspace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

def nullSpace : Submodule 𝕜 E where
  carrier := {x : E | ‖x‖ = 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq] at hy
    simp only [Set.mem_setOf_eq]
    apply le_antisymm _ (norm_nonneg (x+y))
    apply le_trans (norm_add_le x y)
    rw [hx, hy]
    linarith
  zero_mem' := norm_zero
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq]
    rw [norm_smul, hx, mul_zero]

lemma mem_nullSpace_iff_norm_eq_zero {x : E} : x ∈ nullSpace 𝕜 E ↔ ‖x‖ = 0 := Eq.to_iff rfl

abbrev Q := (mk : E → (E ⧸ (nullSpace 𝕜 E)))

lemma inner_nullSpace_left_eq_zero (x y : E) (h : x ∈ nullSpace 𝕜 E): ⟪x, y⟫_𝕜 = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff]
  apply le_antisymm _ (sq_nonneg _)
  rw [sq]
  nth_rw 2 [← RCLike.norm_conj]
  rw [_root_.inner_conj_symm]
  calc ‖⟪x, y⟫_𝕜‖ * ‖⟪y, x⟫_𝕜‖ ≤ re ⟪x, x⟫_𝕜 * re ⟪y, y⟫_𝕜 := inner_mul_inner_self_le _ _
  _ = (‖x‖ * ‖x‖) * re ⟪y, y⟫_𝕜 := by rw [inner_self_eq_norm_mul_norm x]
  _ = (0 * 0) * re ⟪y, y⟫_𝕜 := by rw [(mem_nullSpace_iff_norm_eq_zero 𝕜 E).mp h]
  _ = 0 := by ring

lemma inner_nullSpace_right_eq_zero (x y : E) (h : y ∈ nullSpace 𝕜 E): ⟪x, y⟫_𝕜 = 0 := by
  rw [inner_eq_zero_symm]
  exact inner_nullSpace_left_eq_zero 𝕜 E y x h

lemma nullSpace_le_ker_toDualMap (x : E) : (nullSpace 𝕜 E) ≤ ker (toDualMap 𝕜 E x) := by
  intro y hy
  refine LinearMap.mem_ker.mpr ?_
  simp only [toDualMap_apply]
  exact inner_nullSpace_right_eq_zero 𝕜 E x y hy

lemma nullSpace_le_ker_toDualMap' : (nullSpace 𝕜 E) ≤ ker (toDualMap 𝕜 E) := by
  intro x hx
  refine LinearMap.mem_ker.mpr ?_
  ext y
  simp only [toDualMap_apply, ContinuousLinearMap.zero_apply]
  exact inner_nullSpace_left_eq_zero 𝕜 E x y hx

def preInnerQ : E ⧸ (nullSpace 𝕜 E) →ₗ⋆[𝕜] (NormedSpace.Dual 𝕜 E) :=
  liftQ (nullSpace 𝕜 E) (toDualMap 𝕜 E).toLinearMap (nullSpace_le_ker_toDualMap' 𝕜 E)

lemma nullSpace_le_ker_preInnerQ (x : E ⧸ (nullSpace 𝕜 E)) : (nullSpace 𝕜 E) ≤
    ker (preInnerQ 𝕜 E x) := by
  intro y hy
  simp only [LinearMap.mem_ker]
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (nullSpace 𝕜 E) x
  rw [preInnerQ]
  rw [← hz, mkQ_apply, Submodule.liftQ_apply]
  simp only [LinearIsometry.coe_toLinearMap, toDualMap_apply]
  exact inner_nullSpace_right_eq_zero 𝕜 E z y hy

def innerQ : E ⧸ (nullSpace 𝕜 E) → E ⧸ (nullSpace 𝕜 E) → 𝕜 :=
  fun x => liftQ (nullSpace 𝕜 E) (preInnerQ 𝕜 E x).toLinearMap (nullSpace_le_ker_preInnerQ 𝕜 E x)

end Nullspace

section InnerProductSpace.Core

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

instance : InnerProductSpace.Core 𝕜 (E ⧸ (nullSpace 𝕜 E)) where
  inner := innerQ 𝕜 E
  conj_symm := sorry
  nonneg_re := sorry
  add_left := sorry
  smul_left := sorry
  definite := sorry

end InnerProductSpace.Core

end

#min_imports

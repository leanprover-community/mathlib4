/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Group.SeparationQuotient

/-!
# Canonial inner product space from Preinner product space

This file defines the inner product space on the separation quotient of a preinner product space
(the inner product can be degenerate), that is, by quotienting the null submodule.

## Main results

It is shown that ` ⟪x, y⟫_𝕜 = 0` for all `y : E` using the Cauchy-Schwarz inequality.
-/

noncomputable section

open RCLike Submodule Quotient LinearMap InnerProductSpace InnerProductSpace.Core

variable (𝕜 E : Type*) [k: RCLike 𝕜]

section NullSubmodule

open SeparationQuotientAddGroup

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The null space with respect to the norm. -/
def nullSubmodule : Submodule 𝕜 E :=
  { nullSubgroup with
    smul_mem' := by
      intro c x hx
      simp only [Set.mem_setOf_eq] at hx
      simp only [Set.mem_setOf_eq]
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        AddSubgroup.mem_toAddSubmonoid]
      have : ‖c • x‖ = 0 := by
        rw [norm_smul, hx, mul_zero]
      exact this }

@[simp]
lemma mem_nullSubmodule_iff {x : E} : x ∈ nullSubmodule 𝕜 E ↔ ‖x‖ = 0 := Iff.rfl

lemma inner_eq_zero_of_left_mem_nullSubmodule (x y : E) (h : x ∈ nullSubmodule 𝕜 E) :
    ⟪x, y⟫_𝕜 = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff]
  apply le_antisymm _ (sq_nonneg _)
  rw [sq]
  nth_rw 2 [← RCLike.norm_conj]
  rw [_root_.inner_conj_symm]
  calc ‖⟪x, y⟫_𝕜‖ * ‖⟪y, x⟫_𝕜‖ ≤ re ⟪x, x⟫_𝕜 * re ⟪y, y⟫_𝕜 := inner_mul_inner_self_le _ _
  _ = (‖x‖ * ‖x‖) * re ⟪y, y⟫_𝕜 := by rw [inner_self_eq_norm_mul_norm x]
  _ = (0 * 0) * re ⟪y, y⟫_𝕜 := by rw [(mem_nullSubmodule_iff 𝕜 E).mp h]
  _ = 0 := by ring

lemma inner_nullSubmodule_right_eq_zero (x y : E) (h : y ∈ nullSubmodule 𝕜 E) : ⟪x, y⟫_𝕜 = 0 := by
  rw [inner_eq_zero_symm]
  exact inner_eq_zero_of_left_mem_nullSubmodule 𝕜 E y x h

lemma inn_nullSubmodule_right_eq_zero (x y : E) (h : y ∈ (nullSubmodule 𝕜 E)) : ‖x - y‖ = ‖x‖ := by
  rw [← sq_eq_sq (norm_nonneg _) (norm_nonneg _), sq, sq,
    ← @inner_self_eq_norm_mul_norm 𝕜 E _ _ _ x, ← @inner_self_eq_norm_mul_norm 𝕜 E _ _ _ (x-y),
    inner_sub_sub_self, inner_nullSubmodule_right_eq_zero 𝕜 E x y h,
    inner_eq_zero_of_left_mem_nullSubmodule 𝕜 E y x h,
      inner_eq_zero_of_left_mem_nullSubmodule 𝕜 E y y h]
  simp only [sub_zero, add_zero]

/-- For each `x : E`, the kernel of `⟪x, ⬝⟫` includes the null space. -/
lemma nullSubmodule_le_ker_toDualMap (x : E) : nullSubmodule 𝕜 E ≤ ker (toDualMap 𝕜 E x) := by
  intro y hy
  refine LinearMap.mem_ker.mpr ?_
  simp only [toDualMap_apply]
  exact inner_nullSubmodule_right_eq_zero 𝕜 E x y hy

/-- The kernel of the map `x ↦ ⟪x, ⬝⟫` includes the null space. -/
lemma nullSubmodule_le_ker_toDualMap' : nullSubmodule 𝕜 E ≤ ker (toDualMap 𝕜 E) := by
  intro x hx
  refine LinearMap.mem_ker.mpr ?_
  ext y
  simp only [toDualMap_apply, ContinuousLinearMap.zero_apply]
  exact inner_eq_zero_of_left_mem_nullSubmodule 𝕜 E x y hx

instance : IsClosed ((nullSubmodule 𝕜 E) : Set E) := by
  rw [← isOpen_compl_iff, isOpen_iff_nhds]
  intro x hx
  refine Filter.le_principal_iff.mpr ?_
  rw [mem_nhds_iff]
  use Metric.ball x (‖x‖/2)
  have normxnezero : 0 < ‖x‖ := (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx))
  refine ⟨?_, Metric.isOpen_ball, Metric.mem_ball_self <| half_pos normxnezero⟩
  intro y hy
  have normy : ‖x‖ / 2 ≤ ‖y‖ := by
    rw [mem_ball_iff_norm, ← norm_neg] at hy
    simp only [neg_sub] at hy
    rw [← sub_half]
    have hy' : ‖x‖ - ‖y‖ < ‖x‖ / 2 := lt_of_le_of_lt (norm_sub_norm_le _ _) hy
    linarith
  exact Ne.symm (ne_of_lt (lt_of_lt_of_le (half_pos normxnezero) normy))

end NullSubmodule

end

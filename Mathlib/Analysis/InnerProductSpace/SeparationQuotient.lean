/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Group.SeparationQuotient

/-!
# Canonial inner product space from Preinner product space

This file defines the inner product space from a preinner product space (the inner product
can be degenerate) by quotienting the null space.

## Main results

It is shown that ` ⟪x, y⟫_𝕜 = 0` for all `y : E` using the Cauchy-Schwarz inequality.
-/

noncomputable section

open RCLike Submodule Quotient LinearMap InnerProductSpace InnerProductSpace.Core

variable (𝕜 E : Type*) [k: RCLike 𝕜]

section NullSubmodule

open SeparationQuotient

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The null space with respect to the norm. -/
def nullSubmodule : Submodule 𝕜 E :=
  { nullSpace with
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

lemma inner_nullSubmodule_right_eq_zero (x y : E) (h : y ∈ nullSpace) : ⟪x, y⟫_𝕜 = 0 := by
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

/-- An auxiliary map to define the inner product on the quotient. Only the first entry is
quotiented. -/
def preInnerQ : SeparationQuotient E →ₗ⋆[𝕜] (NormedSpace.Dual 𝕜 E) :=
  (SeparationQuotient.liftCLM (toDualMap 𝕜 E).toContinuousLinearMap
  (by
  intro x y h
  rw [inseparable_iff_norm_zero] at h
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  ext z
  simp only [toDualMap_apply]
  rw [← sub_eq_zero, Eq.symm (_root_.inner_sub_left x y z)]
  exact inner_eq_zero_of_left_mem_nullSubmodule 𝕜 E (x - y) z h
  ))

lemma nullSubmodule_le_ker_preInnerQ (x : SeparationQuotient E) : nullSubmodule 𝕜 E ≤
    ker (preInnerQ 𝕜 E x) := by
  intro y hy
  simp only [LinearMap.mem_ker]
  obtain ⟨z, hz⟩ := surjective_mk x
  rw [preInnerQ, ← hz]
  simp only [ContinuousLinearMap.coe_coe, SeparationQuotient.CLM_lift_apply,
    LinearIsometry.coe_toContinuousLinearMap, toDualMap_apply]
  exact inner_nullSubmodule_right_eq_zero 𝕜 E z y hy

lemma eq_of_inseparable (x : SeparationQuotient E) :
    ∀ (y z : E), Inseparable y z → ((preInnerQ 𝕜 E) x) y = ((preInnerQ 𝕜 E) x) z := by
  intro y z h
  rw [inseparable_iff_norm_zero] at h
  obtain ⟨x', hx'⟩ := surjective_mk x
  rw [preInnerQ, ← hx']
  simp only [ContinuousLinearMap.coe_coe, SeparationQuotient.CLM_lift_apply,
    LinearIsometry.coe_toContinuousLinearMap, toDualMap_apply]
  rw [← sub_eq_zero, Eq.symm (_root_.inner_sub_right x' y z)]
  exact inner_nullSubmodule_right_eq_zero 𝕜 E x' (y - z) h


/-- The inner product on the quotient, composed as the composition of two lifts to the quotients. -/
def innerQ : SeparationQuotient E → SeparationQuotient E → 𝕜 :=
  fun x => SeparationQuotient.liftCLM (preInnerQ 𝕜 E x) (eq_of_inseparable 𝕜 E x)

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

section InnerProductSpace

open SeparationQuotient

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

instance : InnerProductSpace 𝕜 (SeparationQuotient E) where
  inner := innerQ 𝕜 E
  conj_symm x y:= by
    rw [inner]
    simp only
    rw [innerQ, innerQ]
    obtain ⟨z, hz⟩ := surjective_mk x
    obtain ⟨w, hw⟩ := surjective_mk y
    rw [← hz, ← hw]
    simp only [SeparationQuotient.CLM_lift_apply]
    rw [preInnerQ]
    simp only [ContinuousLinearMap.coe_coe, CLM_lift_apply,
      LinearIsometry.coe_toContinuousLinearMap, toDualMap_apply, _root_.inner_conj_symm]
  norm_sq_eq_inner x := by
    obtain ⟨z, hz⟩ := surjective_mk x
    rw [← hz]
    simp only [quotient_norm_mk_eq]
    rw [innerQ]
    simp only [CLM_lift_apply]
    rw [preInnerQ]
    simp only [ContinuousLinearMap.coe_coe, CLM_lift_apply,
      LinearIsometry.coe_toContinuousLinearMap, toDualMap_apply]
    rw [inner_self_eq_norm_sq_to_K, sq (ofReal ‖z‖)]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    rw [← sq]
  add_left x y z:= by
    rw [inner]
    simp only
    rw [innerQ, innerQ, innerQ]
    obtain ⟨a, ha⟩ := surjective_mk x
    obtain ⟨b, hb⟩ := surjective_mk y
    obtain ⟨c, hc⟩ := surjective_mk z
    rw [← ha, ← hb, ← hc]
    simp only [map_add, CLM_lift_apply, ContinuousLinearMap.add_apply]
  smul_left x y r := by
    rw [inner]
    simp only
    rw [innerQ, innerQ]
    obtain ⟨a, ha⟩ := surjective_mk x
    obtain ⟨b, hb⟩ := surjective_mk y
    rw [← ha, ← hb]
    simp only [LinearMap.map_smulₛₗ, CLM_lift_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul]

end InnerProductSpace

end

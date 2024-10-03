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
instance nullSubmodule : Submodule 𝕜 E :=
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


-- TOD lift as linearmap
-- /-- An auxiliary map to define the inner product on the quotient. Only the first entry is
-- quotiented. -/
-- def preInnerQ : SeparationQuotient E →ₗ⋆[𝕜] (NormedSpace.Dual 𝕜 E) :=
--   lift (toDualMap 𝕜 E).toLinearMap
--   (by
--   intro x y
--   sorry)

-- lemma nullSubmodule_le_ker_preInnerQ (x : E ⧸ (nullSubmodule 𝕜 E)) : nullSubmodule 𝕜 E ≤
--     ker (preInnerQ 𝕜 E x) := by
--   intro y hy
--   simp only [LinearMap.mem_ker]
--   obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (nullSubmodule 𝕜 E) x
--   rw [preInnerQ, ← hz, mkQ_apply, Submodule.liftQ_apply]
--   simp only [LinearIsometry.coe_toLinearMap, toDualMap_apply]
--   exact inner_nullSubmodule_right_eq_zero 𝕜 E z y hy

-- /-- The inner product on the quotient, composed as the composition of two lifts to the quotients. -/
-- def innerQ : E ⧸ (nullSubmodule 𝕜 E) → E ⧸ (nullSubmodule 𝕜 E) → 𝕜 :=
--   fun x => liftQ (nullSubmodule 𝕜 E) (preInnerQ 𝕜 E x).toLinearMap (nullSubmodule_le_ker_preInnerQ 𝕜 E x)

-- instance : IsClosed ((nullSubmodule 𝕜 E) : Set E) := by
--   rw [← isOpen_compl_iff, isOpen_iff_nhds]
--   intro x hx
--   refine Filter.le_principal_iff.mpr ?_
--   rw [mem_nhds_iff]
--   use Metric.ball x (‖x‖/2)
--   have normxnezero : 0 < ‖x‖ := (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx))
--   refine ⟨?_, Metric.isOpen_ball, Metric.mem_ball_self <| half_pos normxnezero⟩
--   intro y hy
--   have normy : ‖x‖ / 2 ≤ ‖y‖ := by
--     rw [mem_ball_iff_norm, ← norm_neg] at hy
--     simp only [neg_sub] at hy
--     rw [← sub_half]
--     have hy' : ‖x‖ - ‖y‖ < ‖x‖ / 2 := lt_of_le_of_lt (norm_sub_norm_le _ _) hy
--     linarith
--   exact Ne.symm (ne_of_lt (lt_of_lt_of_le (half_pos normxnezero) normy))

-- end NullSubmodule

-- section InnerProductSpace

-- variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- instance : InnerProductSpace 𝕜 (E ⧸ (nullSubmodule 𝕜 E)) where
--   inner := innerQ 𝕜 E
--   conj_symm x y:= by
--     rw [inner]
--     simp only
--     rw [innerQ, innerQ]
--     obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (nullSubmodule 𝕜 E) x
--     obtain ⟨w, hw⟩ := Submodule.mkQ_surjective (nullSubmodule 𝕜 E) y
--     rw [← hz, ← hw]
--     simp only [mkQ_apply, liftQ_apply, ContinuousLinearMap.coe_coe]
--     rw [preInnerQ, Submodule.liftQ_apply, Submodule.liftQ_apply]
--     simp only [LinearIsometry.coe_toLinearMap, toDualMap_apply]
--     exact conj_symm z w
--   norm_sq_eq_inner x := by
--     rw [AddSubgroup.quotient_norm_eq]
--     obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (nullSubmodule 𝕜 E) x
--     rw [← hz]
--     simp only [mkQ_apply]
--     rw [innerQ]
--     simp only [liftQ_apply, ContinuousLinearMap.coe_coe]
--     rw [preInnerQ]
--     simp only [liftQ_apply, LinearIsometry.coe_toLinearMap, toDualMap_apply]
--     rw [inner_self_eq_norm_sq_to_K, sq (ofReal ‖z‖)]
--     simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
--     rw [← sq]
--     have : norm '' {m : E | (QuotientAddGroup.mk m) = (mk z : E ⧸ (nullSubmodule 𝕜 E))}
--         = norm '' {z} := by
--       ext x
--       constructor
--       · intro hx
--         obtain ⟨m, hm⟩ := hx
--         simp only [Set.image_singleton, Set.mem_singleton_iff]
--         simp only [Set.mem_setOf_eq] at hm
--         have hm' : (QuotientAddGroup.mk m) = (mk m : E ⧸ (nullSubmodule 𝕜 E)) := rfl
--         rw [hm', Submodule.Quotient.eq] at hm
--         have : ‖m‖ = ‖z‖ := by
--           rw [← inn_nullSubmodule_right_eq_zero 𝕜 E m (m-z) hm.1]
--           simp only [sub_sub_cancel]
--         rw [← this]
--         exact Eq.symm hm.2
--       · intro hx
--         rw [Set.image_singleton, Set.mem_singleton_iff] at hx
--         simp only [Set.mem_image, Set.mem_setOf_eq]
--         use z
--         refine ⟨rfl, (Eq.symm hx)⟩
--     simp_rw [this]
--     simp only [Set.image_singleton, csInf_singleton]
--   add_left x y z:= by
--     rw [inner]
--     simp only
--     rw [innerQ, innerQ, innerQ]
--     obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (nullSubmodule 𝕜 E) x
--     obtain ⟨b, hb⟩ := Submodule.mkQ_surjective (nullSubmodule 𝕜 E) y
--     obtain ⟨c, hc⟩ := Submodule.mkQ_surjective (nullSubmodule 𝕜 E) z
--     rw [← ha, ← hb, ← hc]
--     simp only [mkQ_apply, liftQ_apply, ContinuousLinearMap.coe_coe]
--     rw [preInnerQ, Submodule.liftQ_apply, Submodule.liftQ_apply, map_add, Submodule.liftQ_apply]
--     simp only [LinearIsometry.coe_toLinearMap, liftQ_apply, ContinuousLinearMap.add_apply,
--       toDualMap_apply]
--   smul_left x y r := by
--     rw [inner]
--     simp only
--     rw [innerQ, innerQ]
--     obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (nullSubmodule 𝕜 E) x
--     obtain ⟨b, hb⟩ := Submodule.mkQ_surjective (nullSubmodule 𝕜 E) y
--     rw [← ha, ← hb]
--     simp only [mkQ_apply, liftQ_apply, ContinuousLinearMap.coe_coe]
--     rw [preInnerQ, Submodule.liftQ_apply]
--     simp only [LinearMap.map_smulₛₗ, liftQ_apply, LinearIsometry.coe_toLinearMap,
--       ContinuousLinearMap.coe_smul', Pi.smul_apply, toDualMap_apply, smul_eq_mul]

-- end InnerProductSpace

-- end

/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.Star

/-!
# `ℝ` is an `RCLike` field

This contains the instance of `RCLike ℝ` as well as some convenience lemmas about `RCLike` specific
to the case `K := ℝ`.
-/

open scoped ComplexConjugate

variable {K : Type*} [RCLike K]

namespace RCLike

section Instances

-- should we move this elsewhere, especially since we have reduced the imports of
-- `CStarAlgebra.Basic`?
instance (priority := 100) : CStarRing K where
  norm_mul_self_le x := le_of_eq <| ((norm_mul _ _).trans <| congr_arg (· * ‖x‖) (norm_conj _)).symm

instance : StarModule ℝ K where
  star_smul r a := by
    apply RCLike.ext <;> simp [RCLike.smul_re, RCLike.smul_im]

noncomputable instance Real.instRCLike : RCLike ℝ where
  re := AddMonoidHom.id ℝ
  im := 0
  I := 0
  I_re_ax := by simp only [AddMonoidHom.map_zero]
  I_mul_I_ax := Or.intro_left _ rfl
  re_add_im_ax z := by
    simp only [add_zero, mul_zero, Algebra.algebraMap_self, RingHom.id_apply, AddMonoidHom.id_apply]
  ofReal_re_ax _ := rfl
  ofReal_im_ax _ := rfl
  mul_re_ax z w := by simp only [sub_zero, mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
  mul_im_ax z w := by simp only [add_zero, zero_mul, mul_zero, AddMonoidHom.zero_apply]
  conj_re_ax z := by simp only [starRingEnd_apply, star_id_of_comm]
  conj_im_ax _ := by simp only [neg_zero, AddMonoidHom.zero_apply]
  conj_I_ax := by simp only [RingHom.map_zero, neg_zero]
  norm_sq_eq_def_ax z := by simp only [sq, Real.norm_eq_abs, ← abs_mul, abs_mul_self z, add_zero,
    mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
  mul_im_I_ax _ := by simp only [mul_zero, AddMonoidHom.zero_apply]
  le_iff_re_im := (and_iff_left rfl).symm

end Instances


section CleanupLemmas

local notation "reR" => @RCLike.re ℝ _
local notation "imR" => @RCLike.im ℝ _
local notation "IR" => @RCLike.I ℝ _
local notation "normSqR" => @RCLike.normSq ℝ _

@[simp, rclike_simps]
theorem re_to_real {x : ℝ} : reR x = x :=
  rfl

@[simp, rclike_simps]
theorem im_to_real {x : ℝ} : imR x = 0 :=
  rfl

@[rclike_simps]
theorem conj_to_real {x : ℝ} : conj x = x :=
  rfl

@[simp, rclike_simps]
theorem I_to_real : IR = 0 :=
  rfl

@[simp, rclike_simps]
theorem normSq_to_real {x : ℝ} : normSq x = x * x := by simp [RCLike.normSq]

@[simp]
theorem ofReal_real_eq_id : @ofReal ℝ _ = id :=
  rfl

end CleanupLemmas


/-!
### ℝ-dependent results

Here we gather results that depend on whether `K` is `ℝ`.
-/
section CaseSpecific

lemma im_eq_zero (h : I = (0 : K)) (z : K) : im z = 0 := by
  rw [← re_add_im z, h]
  simp

/-- The natural isomorphism between `𝕜` satisfying `RCLike 𝕜` and `ℝ` when `RCLike.I = 0`. -/
@[simps]
def realRingEquiv (h : I = (0 : K)) : K ≃+* ℝ where
  toFun := re
  invFun := (↑)
  left_inv x := by nth_rw 2 [← re_add_im x]; simp [h]
  right_inv := ofReal_re
  map_add' := map_add re
  map_mul' := by simp [im_eq_zero h]

end CaseSpecific

end RCLike

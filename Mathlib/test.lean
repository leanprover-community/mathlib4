/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-!
# Empty header

To appease the linter
-/

lemma glou {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : E ≃L[ℝ] E, A x = y := by
  obtain ⟨G, Gx, Gy⟩ : ∃ G : E →L[ℝ] ℝ, G x = 1 ∧ G y ≠ 0 := exists_dual_vector_pair hx hy
  let L : E ≃L[ℝ] E :=
  { toFun := fun z ↦ z + G z • (y - x)
    invFun := fun z ↦ z + ((G y) ⁻¹ * G z) • (x - y)
    map_add' := fun a b ↦ by simp [add_smul]; abel
    map_smul' := by simp [smul_smul]
    left_inv := fun z ↦ by
      simp only [id_eq, eq_mpr_eq_cast, smul_eq_mul, AddHom.toFun_eq_coe, AddHom.coe_mk, map_add,
        SMulHomClass.map_smul, map_sub, Gx, mul_sub, mul_one, add_sub_cancel'_right]
      rw [mul_comm (G z), ← mul_assoc, inv_mul_cancel Gy]
      simp only [smul_sub, one_mul]
      abel
    right_inv := fun z ↦ by
      simp only [map_add, SMulHomClass.map_smul, map_sub, Gx, smul_eq_mul, mul_sub, mul_one]
      rw [mul_comm _ (G y), ← mul_assoc, mul_inv_cancel Gy]
      simp only [smul_sub, one_mul, add_sub_cancel'_right]
      abel
    continuous_toFun := continuous_id.add (G.continuous.smul continuous_const)
    continuous_invFun :=
      continuous_id.add ((continuous_const.mul G.continuous).smul continuous_const) }
  refine ⟨L, ?_⟩
  show x + G x • (y - x) = y
  simp [Gx]

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

universe u

open Submodule FiniteDimensional

open scoped Topology




lemma foo
    {E : Type _} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    (x : E) (h : Module.rank ℝ E = 0) (hx : x ≠ 0) : False := by
  have : Subsingleton E := (rank_zero_iff (R := ℝ)).1 h
  exact hx (Subsingleton.elim x 0)

lemma bar {E : Type _} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    (x y : E) (h : Module.rank ℝ E = 1) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : E ≃L[ℝ] E, A x = y := by
  obtain ⟨c, hc⟩ : ∃ (c : ℝ), c • x = y :=
    exists_smul_eq_of_finrank_eq_one (rank_eq_one_iff_finrank_eq_one.1 h) hx y
  have h'c : c ≠ 0 := by
    rintro rfl
    simp at hc
    exact hy hc.symm
  let L : E ≃L[ℝ] E :=
  { toFun := fun z ↦ c • z
    invFun := fun z ↦ c⁻¹ • z
    map_add' := by simp
    map_smul' := by simp [smul_smul, mul_comm]
    left_inv := fun z ↦ by simp [smul_smul, inv_mul_cancel h'c]
    right_inv := fun z ↦ by simp [smul_smul, mul_inv_cancel h'c]
    continuous_toFun := continuous_const_smul _
    continuous_invFun := continuous_const_smul _ }
  exact ⟨L, hc⟩

open Filter

lemma glou {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, ∃ A : E ≃L[ℝ] E, A x = y := by
  obtain ⟨G, Gx⟩ : ∃ G : E →L[ℝ] ℝ, G x = 1 := by
    rcases exists_dual_vector ℝ x hx with ⟨g, -, gx⟩
    refine ⟨‖x‖⁻¹ • g, ?_⟩
    simp [gx, inv_mul_cancel (norm_ne_zero_iff.2 hx)]
  have : {y | G y ≠ 0} ∈ 𝓝 x := by
    apply (isOpen_ne_fun G.continuous continuous_const).mem_nhds
    simp [Gx]
  filter_upwards [this] with y (Gy : G y ≠ 0)
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



lemma glouglou {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : E ≃L[ℝ] E, A x = y := by
  have h : 1 < Module.rank ℝ E := sorry
  have Z : IsConnected ({0}ᶜ : Set E) := isConnected_compl_singleton_of_one_lt_rank h 0
  apply Z.isPreconnected.induction₂ (fun a b ↦ ∃ A : E ≃L[ℝ] E, A a = b) _ _ _ hx hy
  · intro x hx
    apply eventually_nhdsWithin_of_eventually_nhds
    exact glou hx
  · rintro a b c ha hb hc ⟨A, rfl⟩ ⟨B, rfl⟩
    exact ⟨B * A, rfl⟩
  · rintro a ha b hb ⟨A, rfl⟩
    exact ⟨A.symm, A.symm_apply_apply a⟩

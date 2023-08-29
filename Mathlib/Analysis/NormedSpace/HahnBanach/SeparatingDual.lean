/-
Copyright (c) 2023 Sébastien Gouëzel All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-!
# Spaces with separating dual

We introduce a typeclass `SeparatingDual R V`, registering that the points of the topological
module `V` over `R` can be separated by continuous linear forms.

This property is satisfied for normed spaces over `ℝ` or `ℂ` (by the analytic Hahn-Banach theorem)
and for locally convex topological spaces over `ℝ` (by the geometric Hahn-Banach theorem).

Under the assumption `SeparatingDual R V`, we show in
`SeparatingDual.exists_continuousLinearMap_apply_eq` that the group of continuous linear
equivalences acts transitively on the set of nonzero vectors.
-/

/-- When `E` is a topological module over a topological ring `R`, the class `SeparatingDual R E`
registers that continuous linear forms on `E` separate points of `E`. -/
class SeparatingDual (R V : Type*) [Ring R] [AddCommGroup V] [TopologicalSpace V]
    [TopologicalSpace R] [Module R V] : Prop :=
  /-- Any nonzero vector can be mapped by a continuous linear map to a nonzero scalar. -/
  exists_ne_zero' : ∀ (x : V), x ≠ 0 → ∃ f : V →L[R] R, f x ≠ 0

instance {E : Type*} [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T1Space E] : SeparatingDual ℝ E :=
  ⟨fun x hx ↦ by
    rcases geometric_hahn_banach_point_point hx.symm with ⟨f, hf⟩
    -- ⊢ ∃ f, ↑f x ≠ 0
    simp only [map_zero] at hf
    -- ⊢ ∃ f, ↑f x ≠ 0
    exact ⟨f, hf.ne'⟩ ⟩
    -- 🎉 no goals

instance {E 𝕜 : Type*} [IsROrC 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] : SeparatingDual 𝕜 E :=
  ⟨fun x hx ↦ by
    rcases exists_dual_vector 𝕜 x hx with ⟨f, -, hf⟩
    -- ⊢ ∃ f, ↑f x ≠ 0
    refine ⟨f, ?_⟩
    -- ⊢ ↑f x ≠ 0
    simpa [hf] using hx⟩
    -- 🎉 no goals

namespace SeparatingDual

section Ring

variable {R V : Type*} [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [TopologicalSpace R] [Module R V] [SeparatingDual R V]

lemma exists_ne_zero {x : V} (hx : x ≠ 0) :
    ∃ f : V →L[R] R, f x ≠ 0 :=
  exists_ne_zero' x hx

theorem exists_separating_of_ne {x y : V} (h : x ≠ y) :
    ∃ f : V →L[R] R, f x ≠ f y := by
  rcases exists_ne_zero (R := R) (sub_ne_zero_of_ne h) with ⟨f, hf⟩
  -- ⊢ ∃ f, ↑f x ≠ ↑f y
  exact ⟨f, by simpa [sub_ne_zero] using hf⟩
  -- 🎉 no goals

protected theorem t1Space [T1Space R] : T1Space V := by
  apply t1Space_iff_exists_open.2 (fun x y hxy ↦ ?_)
  -- ⊢ ∃ U, IsOpen U ∧ x ∈ U ∧ ¬y ∈ U
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  -- ⊢ ∃ U, IsOpen U ∧ x ∈ U ∧ ¬y ∈ U
  exact ⟨f ⁻¹' {f y}ᶜ, isOpen_compl_singleton.preimage f.continuous, hf, by simp⟩
  -- 🎉 no goals

protected theorem t2Space [T2Space R] : T2Space V := by
  apply (t2Space_iff _).2 (fun {x} {y} hxy ↦ ?_)
  -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v
  exact separated_by_continuous f.continuous hf
  -- 🎉 no goals

end Ring

section Field

variable {R V : Type*} [Field R] [AddCommGroup V] [TopologicalSpace R] [TopologicalSpace V]
  [TopologicalRing R] [TopologicalAddGroup V] [Module R V] [SeparatingDual R V]

lemma exists_eq_one {x : V} (hx : x ≠ 0) :
    ∃ f : V →L[R] R, f x = 1 := by
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  -- ⊢ ∃ f, ↑f x = 1
  exact ⟨(f x)⁻¹ • f, inv_mul_cancel hf⟩
  -- 🎉 no goals

theorem exists_eq_one_ne_zero_of_ne_zero_pair {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ f : V →L[R] R, f x = 1 ∧ f y ≠ 0 := by
  obtain ⟨u, ux⟩ : ∃ u : V →L[R] R, u x = 1 := exists_eq_one hx
  -- ⊢ ∃ f, ↑f x = 1 ∧ ↑f y ≠ 0
  rcases ne_or_eq (u y) 0 with uy|uy
  -- ⊢ ∃ f, ↑f x = 1 ∧ ↑f y ≠ 0
  · exact ⟨u, ux, uy⟩
    -- 🎉 no goals
  obtain ⟨v, vy⟩ : ∃ v : V →L[R] R, v y = 1 := exists_eq_one hy
  -- ⊢ ∃ f, ↑f x = 1 ∧ ↑f y ≠ 0
  rcases ne_or_eq (v x) 0 with vx|vx
  -- ⊢ ∃ f, ↑f x = 1 ∧ ↑f y ≠ 0
  · exact ⟨(v x)⁻¹ • v, inv_mul_cancel vx, show (v x)⁻¹ * v y ≠ 0 by simp [vx, vy]⟩
    -- 🎉 no goals
  · exact ⟨u + v, by simp [ux, vx], by simp [uy, vy]⟩
    -- 🎉 no goals

/-- In a topological vector space with separating dual, the group of continuous linear equivalences
acts transitively on the set of nonzero vectors: given two nonzero vectors `x` and `y`, there
exists `A : V ≃L[R] V` mapping `x` to `y`. -/
theorem exists_continuousLinearEquiv_apply_eq [ContinuousSMul R V]
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : V ≃L[R] V, A x = y := by
  obtain ⟨G, Gx, Gy⟩ : ∃ G : V →L[R] R, G x = 1 ∧ G y ≠ 0 :=
    exists_eq_one_ne_zero_of_ne_zero_pair hx hy
  let A : V ≃L[R] V :=
  { toFun := fun z ↦ z + G z • (y - x)
    invFun := fun z ↦ z + ((G y) ⁻¹ * G z) • (x - y)
    map_add' := fun a b ↦ by simp [add_smul]; abel
    map_smul' := by simp [smul_smul]
    left_inv := fun z ↦ by
      simp only [id_eq, eq_mpr_eq_cast, RingHom.id_apply, smul_eq_mul, AddHom.toFun_eq_coe,
        AddHom.coe_mk, map_add, map_smulₛₗ, map_sub, Gx, mul_sub, mul_one, add_sub_cancel'_right]
      rw [mul_comm (G z), ← mul_assoc, inv_mul_cancel Gy]
      simp only [smul_sub, one_mul]
      abel
    right_inv := fun z ↦ by
      simp only [map_add, map_smulₛₗ, map_mul, map_inv₀, RingHom.id_apply, map_sub, Gx,
        smul_eq_mul, mul_sub, mul_one]
      rw [mul_comm _ (G y), ← mul_assoc, mul_inv_cancel Gy]
      simp only [smul_sub, one_mul, add_sub_cancel'_right]
      abel
    continuous_toFun := continuous_id.add (G.continuous.smul continuous_const)
    continuous_invFun :=
      continuous_id.add ((continuous_const.mul G.continuous).smul continuous_const) }
  exact ⟨A, show x + G x • (y - x) = y by simp [Gx]⟩
  -- 🎉 no goals

end Field

end SeparatingDual

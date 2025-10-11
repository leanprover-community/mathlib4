/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Sesquilinear forms over a star ring

This file provides some properties about sesquilinear forms `M →ₗ⋆[R] M →ₗ[R] R` when `R` is a
`StarRing`.
-/

open Module LinearMap

variable {R M n : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M] [Module R M]
  [Fintype n] [DecidableEq n]
  {B : M →ₗ⋆[R] M →ₗ[R] R} (b : Basis n R M)

lemma LinearMap.isSymm_iff_basis {ι : Type*} (b : Basis ι R M) :
    IsSymm B ↔ ∀ i j, star (B (b i) (b j)) = B (b j) (b i) where
  mp h i j := h.eq _ _
  mpr := by
    refine fun h ↦ ⟨fun x y ↦ ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x ∈ Submodule.span R (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : y ∈ Submodule.span R (Set.range b))
    rw [← hx, ← hy]
    simp only [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, map_smul, coeFn_sum,
      Finset.sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum, map_mul, star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b₁ h₁ ↦ Finset.sum_congr rfl fun b₂ h₂ ↦ ?_)
    rw [mul_left_comm]
    obtain ⟨i, rfl⟩ := ix h₁
    obtain ⟨j, rfl⟩ := iy h₂
    rw [h]

lemma LinearMap.isSymm_iff_isHermitian_toMatrix : B.IsSymm ↔ (toMatrix₂ b b B).IsHermitian := by
  rw [isSymm_iff_basis b, Matrix.IsHermitian.ext_iff, forall_comm]
  simp [Eq.comm]

lemma star_dotProduct_toMatrix₂_mulVec (x y : n → R) :
    star x ⬝ᵥ (toMatrix₂ b b B).mulVec y = B (b.equivFun.symm x) (b.equivFun.symm y) :=
  dotProduct_toMatrix₂_mulVec b b B x y

lemma apply_eq_star_dotProduct_toMatrix₂_mulVec (x y : M) :
    B x y = star (b.repr x) ⬝ᵥ (toMatrix₂ b b B).mulVec (b.repr y) :=
  apply_eq_dotProduct_toMatrix₂_mulVec b b B x y

variable {R : Type*} [CommRing R] [StarRing R] [PartialOrder R] [Module R M]
  {B : M →ₗ⋆[R] M →ₗ[R] R} (b : Basis n R M)

lemma LinearMap.isPosSemidef_iff_posSemidef_toMatrix :
    B.IsPosSemidef ↔ (toMatrix₂ b b B).PosSemidef := by
  rw [isPosSemidef_def, Matrix.PosSemidef]
  apply and_congr (B.isSymm_iff_isHermitian_toMatrix b)
  rw [isNonneg_def]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · rw [star_dotProduct_toMatrix₂_mulVec]
    exact h _
  · rw [apply_eq_star_dotProduct_toMatrix₂_mulVec b]
    exact h _

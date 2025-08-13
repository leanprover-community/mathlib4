/-
Copyright (c) 2025 Iván Renison, Jam Khan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Jam Khan
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
This file defines the outer product of two vectors as a linear map,
and proves basic properties of the outer product.
-/

namespace ContinuousLinearMap

section seminormed

variable {𝕜 V W : Type*} [RCLike 𝕜]
variable [SeminormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable [SeminormedAddCommGroup W] [InnerProductSpace 𝕜 W]

variable (𝕜) in
/-- A rank-one operator on an inner product space is given by `x ↦ y ↦ z ↦ ⟪y, z⟫ • x`. -/
noncomputable def rankOne : V →L[𝕜] W →L⋆[𝕜] W →L[𝕜] V :=
  LinearMap.mkContinuous₂
  ({toFun := fun x =>
    { toFun := fun y => (lsmul 𝕜 𝕜).flip x ∘L innerSL 𝕜 y
      map_add' := fun _ _ => by rw [map_add, comp_add]
      map_smul' := fun _ _ => by rw [map_smulₛₗ, comp_smulₛₗ]; rfl }
    map_add' := fun _ _ => by ext; simp
    map_smul' := fun _ _ => by ext; simp })
  1 (fun x y => calc _ ≤ _ := opNorm_comp_le _ _
      _ ≤ ‖x‖ * ‖y‖ := mul_le_mul (opNorm_le_bound _ (norm_nonneg x)
          (by simp [norm_smul, mul_comm]))
        (innerSL_apply_norm 𝕜 y ▸ le_refl _) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by rw [one_mul])

lemma rankOne_def (x : V) (y : W) :
    rankOne 𝕜 x y = (lsmul 𝕜 𝕜).flip x ∘L innerSL 𝕜 y :=
  rfl

lemma rankOne_def' (x : V) (y : W) :
    rankOne 𝕜 x y = (innerSL 𝕜 y).smulRight x :=
  rfl

@[simp]
lemma rankOne_apply (x : V) (y z : W) :
    rankOne 𝕜 x y z = inner 𝕜 y z • x :=
  rfl

lemma inner_left_rankOne_apply (x : V) (y z : W) (w : V) :
    inner 𝕜 (rankOne 𝕜 x y z) w = inner 𝕜 z y * inner 𝕜 x w := by
  simp [inner_smul_left, inner_conj_symm]

lemma inner_right_rankOne_apply (x y : V) (z w : W) :
    inner 𝕜 x (rankOne 𝕜 y z w) = inner 𝕜 x y * inner 𝕜 z w := by
  simp [inner_smul_right, mul_comm]

lemma rankOne_comp_rankOne (x : V) (y z : W) (w : V) :
    rankOne 𝕜 x y ∘L rankOne 𝕜 z w = inner 𝕜 y z • rankOne 𝕜 x w := by
  ext v
  simp only [comp_apply, rankOne_apply, map_smul, smul_apply]
  rw [smul_algebra_smul_comm]

lemma isIdempotentElem_rankOne_self {x : V} (h : ‖x‖ = 1) :
    IsIdempotentElem (rankOne 𝕜 x x) := by
  simp [IsIdempotentElem, mul_def, rankOne_comp_rankOne, inner_self_eq_norm_sq_to_K, h]

end seminormed

section normed

variable {𝕜 V W : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup V] [NormedAddCommGroup W]
variable [InnerProductSpace 𝕜 V] [InnerProductSpace 𝕜 W]

section complete

variable [CompleteSpace V] [CompleteSpace W]

lemma adjoint_rankOne (x : V) (y : W) :
    (rankOne 𝕜 x y).adjoint = rankOne 𝕜 y x := by
  simp [rankOne_def, adjoint_comp, ← adjoint_innerSL_apply]

lemma isSelfAdjoint_rankOne_self (x : V) :
    IsSelfAdjoint (rankOne 𝕜 x x) :=
  adjoint_rankOne x x

lemma isPositive_rankOne_self (x : V) :
    (rankOne 𝕜 x x).IsPositive := by
  rw [rankOne_def, ← id_comp (innerSL 𝕜 x), ← adjoint_innerSL_apply]
  exact IsPositive.adjoint_conj isPositive_one _

lemma isStarProjection_rankOne_self {x : V} (h : ‖x‖ = 1) :
    IsStarProjection (rankOne 𝕜 x x) :=
  ⟨isIdempotentElem_rankOne_self h, isSelfAdjoint_rankOne_self x⟩

lemma isSelfAdjoint_rankOne_add (x y : V) :
    IsSelfAdjoint (rankOne 𝕜 x y + rankOne 𝕜 y x) :=
  (adjoint_rankOne (𝕜 := 𝕜) y x) ▸ IsSelfAdjoint.star_add_self _

omit [CompleteSpace V] in
lemma rankOne_comp (x : V) (y : W) (f : W →L[𝕜] W) :
    rankOne 𝕜 x y ∘L f = rankOne 𝕜 x (adjoint f y) := by
  simp_rw [rankOne_def, comp_assoc, innerSL_apply_comp]

end complete

lemma comp_rankOne (x : V) (y : W) (f : V →L[𝕜] V) :
    f ∘L rankOne 𝕜 x y = rankOne 𝕜 (f x) y := by
  simp_rw [rankOne_def, ← comp_assoc, comp_lsmul_flip_apply]

variable {ι : Type*} [Fintype ι]

lemma sum_rankOne_OrthonormalBasis (b : OrthonormalBasis ι 𝕜 V) :
    ∑ i, rankOne 𝕜 (b i) (b i) = 1 := by
  ext x
  simp only [sum_apply, rankOne_apply, one_apply, b.sum_repr' x]

lemma trace_toLinearMap_rankOne (x y : V) (b : Module.Basis ι 𝕜 V) :
    (rankOne 𝕜 x y).trace 𝕜 V = inner 𝕜 y x := by
  have : Module.Finite 𝕜 V := Module.Finite.of_basis b
  rw [rankOne_def, coe_comp, LinearMap.trace_comp_comm', ← coe_comp, comp_lsmul_flip_apply]
  simp [LinearMap.trace_eq_sum_inner _ ((Module.Basis.singleton Unit 𝕜).toOrthonormalBasis
    (by simp [orthonormal_iff_ite]))]

end normed

end ContinuousLinearMap

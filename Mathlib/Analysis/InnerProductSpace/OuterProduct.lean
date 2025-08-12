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

lemma rankOne_add_left (x : V) (y : V) (z : W) :
    rankOne 𝕜 (x + y) z = rankOne 𝕜 x z + rankOne 𝕜 y z := by
  ext
  simp [add_apply]

lemma rankOne_add_right (x : V) (y : W) (z : W) :
    rankOne 𝕜 x (y + z) = rankOne 𝕜 x y + rankOne 𝕜 x z := by
  ext
  simp [add_apply]

lemma rankOne_sub_left (x : W) (y : W) (z : V) :
    rankOne 𝕜 (x - y) z = rankOne 𝕜 x z - rankOne 𝕜 y z := by
  ext
  simp [sub_apply]

lemma rankOne_sub_right (x : V) (y : W) (z : W) :
    rankOne 𝕜 x (y - z) = rankOne 𝕜 x y - rankOne 𝕜 x z := by
  ext
  simp [sub_apply]

lemma rankOne_smul_left (c : 𝕜) (x : V) (y : W) :
    rankOne 𝕜 (c • x) y = (c : 𝕜) • rankOne 𝕜 x y := by
  ext
  simp only [smul_apply, rankOne_apply]
  rw [smul_algebra_smul_comm]

lemma rankOne_smul_right (c : 𝕜) (x : V) (y : W) :
    rankOne 𝕜 x (c • y) = starRingEnd 𝕜 c • rankOne 𝕜 x y := by
  ext
  simp only [smul_apply, rankOne_apply]
  rw [starRingEnd_apply, smul_algebra_smul_comm, inner_smul_left, starRingEnd_apply, mul_smul]
  simp only [RCLike.star_def]
  rw [smul_algebra_smul_comm]

lemma inner_rankOne_eq_inner_mul_inner (x : V) (y z : W) (w : V) :
    inner 𝕜 (rankOne 𝕜 x y z) w = inner 𝕜 z y * inner 𝕜 x w := by
  simp [inner_smul_left, inner_conj_symm]

lemma rankOne_comp_rankOne_eq_inner_smul_rankOne (x : V) (y z : W) (w : V) :
    rankOne 𝕜 x y ∘L rankOne 𝕜 z w = inner 𝕜 y z • rankOne 𝕜 x w := by
  ext v
  simp only [comp_apply, rankOne_apply, map_smul, smul_apply]
  rw [smul_algebra_smul_comm]

lemma rankOne_mul_rankOne_eq_inner_smul_rankOne (x y z w : V) :
    rankOne 𝕜 x y * rankOne 𝕜 z w = inner 𝕜 y z • rankOne 𝕜 x w := by
  rw [mul_def]
  exact rankOne_comp_rankOne_eq_inner_smul_rankOne x y z w

lemma isIdempotentElem_rankOne_self_of_norm_eq_one {x : V} (h : ‖x‖ = 1) :
    IsIdempotentElem (rankOne 𝕜 x x) := by
  ext y
  rw [mul_def]
  simp [Function.comp_apply, rankOne_def, inner_smul_right, inner_self_eq_norm_sq_to_K, h]

end seminormed

section normed

variable {𝕜 V W : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup V] [NormedAddCommGroup W]
variable [InnerProductSpace 𝕜 V] [InnerProductSpace 𝕜 W] [CompleteSpace V] [CompleteSpace W]

lemma adjoint_rankOne (x : V) (y : W) :
    (rankOne 𝕜 x y).adjoint = rankOne 𝕜 y x := by
  symm
  rw [eq_adjoint_iff]
  intro v w
  repeat rw [rankOne_apply]
  rw [inner_smul_left, inner_conj_symm, inner_smul_right]
  exact mul_comm _ _

lemma star_rankOne (x y : V) :
    star (rankOne 𝕜 x y) = rankOne 𝕜 y x := by
  rw [star_eq_adjoint, adjoint_rankOne]

lemma isSelfAdjoint_rankOne_self (x : V) :
    IsSelfAdjoint (rankOne 𝕜 x x) := by
  rw [IsSelfAdjoint, star_eq_adjoint, adjoint_rankOne]

lemma isPositive_rankOne_self (x : V) :
    (rankOne 𝕜 x x).IsPositive := by
  apply And.intro (isSelfAdjoint_rankOne_self x)
  intro y
  simp only [reApplyInnerSelf, rankOne_apply]
  rw [inner_smul_left, InnerProductSpace.conj_inner_symm, inner_mul_symm_re_eq_norm]
  exact norm_nonneg (inner 𝕜 y x * inner 𝕜 x y)

lemma isStarProjection_rankOne_self_of_norm_eq_one {x : V} (h : ‖x‖ = 1) :
    IsStarProjection (rankOne 𝕜 x x) :=
  ⟨isIdempotentElem_rankOne_self_of_norm_eq_one h, isSelfAdjoint_rankOne_self x⟩

lemma isSelfAdjoint_rankOne_add (x y : V) :
    IsSelfAdjoint (rankOne 𝕜 x y + rankOne 𝕜 y x) := by
  rw [isSelfAdjoint_iff', map_add]
  repeat rw [adjoint_rankOne]
  abel

omit [CompleteSpace V] [CompleteSpace W]
variable {ι : Type*} [Fintype ι]

lemma sum_rankOne_OrthonormalBasis (b : OrthonormalBasis ι 𝕜 V) :
    ∑i, rankOne 𝕜 (b i) (b i) = 1 := by
  ext x
  rw [← LinearIsometryEquiv.map_eq_iff b.repr]
  simp only [sum_apply, rankOne_apply, one_apply]
  congr
  exact b.sum_repr' x

end normed

end ContinuousLinearMap

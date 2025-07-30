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

namespace LinearMap

variable (𝕜 : Type*) {E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The outer product of two vectors -/
def outerProduct (x : E) (y : F) : F →ₗ[𝕜] E where
  toFun := fun z => inner 𝕜 y z • x
  map_add' z w := by
    rw [← Module.add_smul, inner_add_right y z w]
  map_smul' m z := by
    rw [RingHom.id_apply, inner_smul_right_eq_smul y z m]
    exact IsScalarTower.smul_assoc m (inner 𝕜 y z) x

lemma outerProduct_def (x : E) (y : F) (z : F) :
    outerProduct 𝕜 x y z = inner 𝕜 y z • x := rfl

lemma outerProduct_add_left (x : E) (y : E) (z : F) :
    outerProduct 𝕜 (x + y) z = outerProduct 𝕜 x z + outerProduct 𝕜 y z := by
  ext
  simp [add_apply, outerProduct_def, smul_add]

lemma outerProduct_add_right (x : E) (y : F) (z : F) :
    outerProduct 𝕜 x (y + z) = outerProduct 𝕜 x y + outerProduct 𝕜 x z := by
  ext
  simp [add_apply, outerProduct_def, inner_add_left, add_smul]

lemma outerProduct_sub_left (x : F) (y : F) (z : E) :
    outerProduct 𝕜 (x - y) z = outerProduct 𝕜 x z - outerProduct 𝕜 y z := by
  ext
  simp [sub_apply, outerProduct_def, smul_sub]

lemma outerProduct_sub_right (x : E) (y : F) (z : F) :
    outerProduct 𝕜 x (y - z) = outerProduct 𝕜 x y - outerProduct 𝕜 x z := by
  ext
  simp [sub_apply, outerProduct_def, inner_sub_left, sub_smul]

lemma outerProduct_assoc_right (x : E) (y : F) (z : F) :
    (outerProduct 𝕜 x y) z = inner 𝕜 y z • x := rfl

lemma outerProduct_smul_assoc_left (c : 𝕜) (x : E) (y : F) :
    outerProduct 𝕜 (c • x) y = (c : 𝕜) • outerProduct 𝕜 x y := by
  ext
  simp only [smul_apply, outerProduct_def]
  rw [smul_algebra_smul_comm]

lemma outerProduct_smul_assoc_right (c : 𝕜) (x : E) (y : F) :
    outerProduct 𝕜 x (c • y) = starRingEnd 𝕜 c • outerProduct 𝕜 x y := by
  ext
  simp only [smul_apply, outerProduct_def]
  rw [starRingEnd_apply, smul_algebra_smul_comm, inner_smul_left, starRingEnd_apply, mul_smul]
  simp only [RCLike.star_def]
  rw [smul_algebra_smul_comm]

lemma inner_outerProduct_eq_inner_mul_inner (x : E) (y z : F) (w : E) :
    inner 𝕜 (outerProduct 𝕜 x y z) w = inner 𝕜 z y * inner 𝕜 x w := by
  simp [outerProduct_def, inner_smul_left, inner_conj_symm]

lemma outerProduct_comp_outerProduct_eq_inner_smul_outerProduct (x : E) (y z : F) (w : E) :
    outerProduct 𝕜 x y ∘ₗ outerProduct 𝕜 z w = inner 𝕜 y z • outerProduct 𝕜 x w := by
  ext v
  simp only [comp_apply, outerProduct_def, map_smul, smul_apply]
  rw [smul_algebra_smul_comm]

lemma outerProduct_mul_outerProduct_eq_inner_smul_outerProduct (x y z w : E) :
    outerProduct 𝕜 x y * outerProduct 𝕜 z w = inner 𝕜 y z • outerProduct 𝕜 x w := by
  rw [Module.End.mul_eq_comp]
  exact outerProduct_comp_outerProduct_eq_inner_smul_outerProduct 𝕜 x y z w

lemma isIdempotentElem_outerProduct_self_of_norm_eq_one {x : E} (h : ‖x‖ = 1) :
    IsIdempotentElem (outerProduct 𝕜 x x) := by
  ext y
  rw [Module.End.mul_eq_comp]
  simp [coe_comp, Function.comp_apply, outerProduct_def, inner_self_eq_norm_sq_to_K, h]

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

lemma adjoint_outerProduct (x : E) (y : F) :
    (outerProduct 𝕜 x y).adjoint = outerProduct 𝕜 y x := by
  symm
  rw [eq_adjoint_iff]
  intro v w
  repeat rw [outerProduct_def]
  rw [inner_smul_left, inner_conj_symm, inner_smul_right]
  exact mul_comm _ _

lemma star_outerProduct (x y : E) :
    star (outerProduct 𝕜 x y) = outerProduct 𝕜 y x := by
  rw [star_eq_adjoint, adjoint_outerProduct]

lemma isSelfAdjoint_outerProduct_self (x : E) :
    IsSelfAdjoint (outerProduct 𝕜 x x) := by
  rw [IsSelfAdjoint, star_eq_adjoint, adjoint_outerProduct]

lemma isSymmetric_outerProduct_self (x : E) : (outerProduct 𝕜 x x).IsSymmetric :=
  (outerProduct 𝕜 x x).isSymmetric_iff_isSelfAdjoint.mpr (isSelfAdjoint_outerProduct_self 𝕜 x)

lemma isPositive_outerProduct_self (x : E) :
    (outerProduct 𝕜 x x).IsPositive := by
  apply And.intro (isSymmetric_outerProduct_self 𝕜 x)
  intro y
  simp only [outerProduct_def]
  rw [inner_smul_left, InnerProductSpace.conj_inner_symm, inner_mul_symm_re_eq_norm]
  exact norm_nonneg (inner 𝕜 y x * inner 𝕜 x y)

lemma isStarProjection_outerProduct_self_of_norm_eq_one {x : E} (h : ‖x‖ = 1) :
    IsStarProjection (outerProduct 𝕜 x x) :=
  ⟨isIdempotentElem_outerProduct_self_of_norm_eq_one 𝕜 h, isSelfAdjoint_outerProduct_self 𝕜 x⟩

lemma isSelfAdjoint_outerProduct_add (x y : E) :
    IsSelfAdjoint (outerProduct 𝕜 x y + outerProduct 𝕜 y x) := by
  rw [isSelfAdjoint_iff', map_add]
  repeat rw [adjoint_outerProduct]
  abel

lemma isSymmetric_outerProduct_add (x y : E) :
    (outerProduct 𝕜 x y + outerProduct 𝕜 y x).IsSymmetric :=
  (outerProduct 𝕜 x y + outerProduct 𝕜 y x).isSymmetric_iff_isSelfAdjoint.mpr
    (isSelfAdjoint_outerProduct_add 𝕜 x y)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
variable {ι : Type*} [Fintype ι]

lemma sum_outerProduct (f g : ι → E) (x : E) :
    (∑ i, outerProduct 𝕜 (f i) (g i)) x = ∑ i, outerProduct 𝕜 (f i) (g i) x := by
  simp only [sum_apply]

variable {𝕜}

lemma sum_outerProduct_OrthonormalBasis (b : OrthonormalBasis ι 𝕜 E) :
    ∑i, outerProduct 𝕜 (b i) (b i) = 1 := by
  ext x
  rw [← LinearIsometryEquiv.map_eq_iff b.repr]
  simp only [coeFn_sum, Finset.sum_apply, Module.End.one_apply, outerProduct_def]
  congr
  exact b.sum_repr' x

variable [DecidableEq ι]

lemma trace_outerProduct (x y : E) (b : OrthonormalBasis ι 𝕜 E) :
    trace 𝕜 E (outerProduct 𝕜 x y) = inner 𝕜 y x := by
  rw [(outerProduct 𝕜 x y).trace_eq_sum_inner b]
  simp +contextual [outerProduct_def, inner_smul_right]
  have : ∀i, inner 𝕜 y (b i) * inner 𝕜 (b i) x = inner 𝕜 (b i) x * inner 𝕜 y (b i) := by
    intro i
    apply mul_comm
  simp +contextual [this, ← inner_smul_right, ← outerProduct_def]
  rw [← inner_sum, ← sum_outerProduct, sum_outerProduct_OrthonormalBasis b, Module.End.one_apply]

end LinearMap

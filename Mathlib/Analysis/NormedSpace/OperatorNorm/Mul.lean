/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/

import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace

/-!
# Results about operator norms in normed algebras

This file (split off from `OperatorNorm.lean`) contains results about the operator norm
of multiplication and scalar-multiplication operations in normed algebras and normed modules.
-/

suppress_compilation

-- make instances connecting normed things and algebra have higher priority
open scoped AlgebraNormedInstances

set_option linter.uppercaseLean3 false

open Metric
open scoped Classical NNReal Topology Uniformity

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]

section SemiNormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace ContinuousLinearMap

section MultiplicationLinear

section NonUnital

variable (𝕜) (𝕜' : Type*) [NonUnitalSeminormedRing 𝕜']
variable [NormedSpace 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜'] [SMulCommClass 𝕜 𝕜' 𝕜']

/-- Multiplication in a non-unital normed algebra as a continuous bilinear map. -/
def mul : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  (LinearMap.mul 𝕜 𝕜').mkContinuous₂ 1 fun x y => by simpa using norm_mul_le x y
#align continuous_linear_map.mul ContinuousLinearMap.mul

@[simp]
theorem mul_apply' (x y : 𝕜') : mul 𝕜 𝕜' x y = x * y :=
  rfl
#align continuous_linear_map.mul_apply' ContinuousLinearMap.mul_apply'

@[simp]
theorem opNorm_mul_apply_le (x : 𝕜') : ‖mul 𝕜 𝕜' x‖ ≤ ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (norm_mul_le x)
#align continuous_linear_map.op_norm_mul_apply_le ContinuousLinearMap.opNorm_mul_apply_le

@[deprecated] alias op_norm_mul_apply_le := opNorm_mul_apply_le -- deprecated on 2024-02-02

theorem opNorm_mul_le : ‖mul 𝕜 𝕜'‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _
#align continuous_linear_map.op_norm_mul_le ContinuousLinearMap.opNorm_mul_le

@[deprecated] alias op_norm_mul_le := opNorm_mul_le -- deprecated on 2024-02-02

/-- Multiplication on the left in a non-unital normed algebra `𝕜'` as a non-unital algebra
homomorphism into the algebra of *continuous* linear maps. This is the left regular representation
of `A` acting on itself.

This has more algebraic structure than `ContinuousLinearMap.mul`, but there is no longer continuity
bundled in the first coordinate.  An alternative viewpoint is that this upgrades
`NonUnitalAlgHom.lmul` from a homomorphism into linear maps to a homomorphism into *continuous*
linear maps. -/
def _root_.NonUnitalAlgHom.Lmul : 𝕜' →ₙₐ[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  { mul 𝕜 𝕜' with
    map_mul' := fun _ _ ↦ ext fun _ ↦ mul_assoc _ _ _
    map_zero' := ext fun _ ↦ zero_mul _ }

variable {𝕜 𝕜'} in
@[simp]
theorem _root_.NonUnitalAlgHom.coe_Lmul : ⇑(NonUnitalAlgHom.Lmul 𝕜 𝕜') = mul 𝕜 𝕜' :=
  rfl

/-- Simultaneous left- and right-multiplication in a non-unital normed algebra, considered as a
continuous trilinear map. This is akin to its non-continuous version `LinearMap.mulLeftRight`,
but there is a minor difference: `LinearMap.mulLeftRight` is uncurried. -/
def mulLeftRight : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  ((compL 𝕜 𝕜' 𝕜' 𝕜').comp (mul 𝕜 𝕜').flip).flip.comp (mul 𝕜 𝕜')
#align continuous_linear_map.mul_left_right ContinuousLinearMap.mulLeftRight

@[simp]
theorem mulLeftRight_apply (x y z : 𝕜') : mulLeftRight 𝕜 𝕜' x y z = x * z * y :=
  rfl
#align continuous_linear_map.mul_left_right_apply ContinuousLinearMap.mulLeftRight_apply

theorem opNorm_mulLeftRight_apply_apply_le (x y : 𝕜') : ‖mulLeftRight 𝕜 𝕜' x y‖ ≤ ‖x‖ * ‖y‖ :=
  (opNorm_comp_le _ _).trans <|
    (mul_comm _ _).trans_le <|
      mul_le_mul (opNorm_mul_apply_le _ _ _)
        (opNorm_le_bound _ (norm_nonneg _) fun _ => (norm_mul_le _ _).trans_eq (mul_comm _ _))
        (norm_nonneg _) (norm_nonneg _)
#align continuous_linear_map.op_norm_mul_left_right_apply_apply_le ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le

@[deprecated] -- deprecated on 2024-02-02
alias op_norm_mulLeftRight_apply_apply_le :=
  opNorm_mulLeftRight_apply_apply_le

theorem opNorm_mulLeftRight_apply_le (x : 𝕜') : ‖mulLeftRight 𝕜 𝕜' x‖ ≤ ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (opNorm_mulLeftRight_apply_apply_le 𝕜 𝕜' x)
#align continuous_linear_map.op_norm_mul_left_right_apply_le ContinuousLinearMap.opNorm_mulLeftRight_apply_le

@[deprecated] alias op_norm_mulLeftRight_apply_le := opNorm_mulLeftRight_apply_le -- 2024-02-02

theorem opNorm_mulLeftRight_le :
    -- Currently, this cannot be synthesized because it violated `synthPendingDepth` restrictions
    -- see leanprover/lean4#3927
    letI : Norm (𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜') := hasOpNorm (E := 𝕜') (F := 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜')
    ‖mulLeftRight 𝕜 𝕜'‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => (one_mul ‖x‖).symm ▸ opNorm_mulLeftRight_apply_le 𝕜 𝕜' x
#align continuous_linear_map.op_norm_mul_left_right_le ContinuousLinearMap.opNorm_mulLeftRight_le

@[deprecated] alias op_norm_mulLeftRight_le := opNorm_mulLeftRight_le -- deprecated on 2024-02-02

/-- This is a mixin class for non-unital normed algebras which states that the left-regular
representation of the algebra on itself is isometric. Every unital normed algebra with `‖1‖ = 1` is
a regular normed algebra (see `NormedAlgebra.instRegularNormedAlgebra`). In addition, so is every
C⋆-algebra, non-unital included (see `CstarRing.instRegularNormedAlgebra`), but there are yet other
examples. Any algebra with an approximate identity (e.g., $$L^1$$) is also regular.

This is a useful class because it gives rise to a nice norm on the unitization; in particular it is
a C⋆-norm when the norm on `A` is a C⋆-norm. -/
class _root_.RegularNormedAlgebra : Prop :=
  /-- The left regular representation of the algebra on itself is an isometry. -/
  isometry_mul' : Isometry (mul 𝕜 𝕜')

/-- Every (unital) normed algebra such that `‖1‖ = 1` is a `RegularNormedAlgebra`. -/
instance _root_.NormedAlgebra.instRegularNormedAlgebra {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormOneClass 𝕜'] : RegularNormedAlgebra 𝕜 𝕜' where
  isometry_mul' := AddMonoidHomClass.isometry_of_norm (mul 𝕜 𝕜') <|
    fun x => le_antisymm (opNorm_mul_apply_le _ _ _) <| by
      convert ratio_le_opNorm ((mul 𝕜 𝕜') x) (1 : 𝕜')
      simp [norm_one]

variable [RegularNormedAlgebra 𝕜 𝕜']

lemma isometry_mul : Isometry (mul 𝕜 𝕜') :=
  RegularNormedAlgebra.isometry_mul'

@[simp]
lemma opNorm_mul_apply (x : 𝕜') : ‖mul 𝕜 𝕜' x‖ = ‖x‖ :=
  (AddMonoidHomClass.isometry_iff_norm (mul 𝕜 𝕜')).mp (isometry_mul 𝕜 𝕜') x
#align continuous_linear_map.op_norm_mul_apply ContinuousLinearMap.opNorm_mul_applyₓ

@[deprecated] alias op_norm_mul_apply := opNorm_mul_apply -- deprecated on 2024-02-02

@[simp]
lemma opNNNorm_mul_apply (x : 𝕜') : ‖mul 𝕜 𝕜' x‖₊ = ‖x‖₊ :=
  Subtype.ext <| opNorm_mul_apply 𝕜 𝕜' x

@[deprecated] alias op_nnnorm_mul_apply := opNNNorm_mul_apply -- deprecated on 2024-02-02

/-- Multiplication in a normed algebra as a linear isometry to the space of
continuous linear maps. -/
def mulₗᵢ : 𝕜' →ₗᵢ[𝕜] 𝕜' →L[𝕜] 𝕜' where
  toLinearMap := mul 𝕜 𝕜'
  norm_map' x := opNorm_mul_apply 𝕜 𝕜' x
#align continuous_linear_map.mulₗᵢ ContinuousLinearMap.mulₗᵢₓ

@[simp]
theorem coe_mulₗᵢ : ⇑(mulₗᵢ 𝕜 𝕜') = mul 𝕜 𝕜' :=
  rfl
#align continuous_linear_map.coe_mulₗᵢ ContinuousLinearMap.coe_mulₗᵢₓ

end NonUnital

section RingEquiv

variable (𝕜 E)

/-- If `M` is a normed space over `𝕜`, then the space of maps `𝕜 →L[𝕜] M` is linearly equivalent
to `M`. (See `ring_lmap_equiv_self` for a stronger statement.) -/
def ring_lmap_equiv_selfₗ : (𝕜 →L[𝕜] E) ≃ₗ[𝕜] E where
  toFun := fun f ↦ f 1
  invFun := (ContinuousLinearMap.id 𝕜 𝕜).smulRight
  map_smul' := fun a f ↦ by simp only [coe_smul', Pi.smul_apply, RingHom.id_apply]
  map_add' := fun f g ↦ by simp only [add_apply]
  left_inv := fun f ↦ by ext; simp only [smulRight_apply, coe_id', _root_.id, one_smul]
  right_inv := fun m ↦ by simp only [smulRight_apply, id_apply, one_smul]

/-- If `M` is a normed space over `𝕜`, then the space of maps `𝕜 →L[𝕜] M` is linearly isometrically
equivalent to `M`. -/
def ring_lmap_equiv_self : (𝕜 →L[𝕜] E) ≃ₗᵢ[𝕜] E where
  toLinearEquiv := ring_lmap_equiv_selfₗ 𝕜 E
  norm_map' := by
    refine fun f ↦ le_antisymm ?_ ?_
    · simpa only [norm_one, mul_one] using le_opNorm f 1
    · refine opNorm_le_bound' f (norm_nonneg <| f 1) (fun x _ ↦ ?_)
      rw [(by rw [smul_eq_mul, mul_one] : f x = f (x • 1)), ContinuousLinearMap.map_smul,
        norm_smul, mul_comm, (by rfl : ring_lmap_equiv_selfₗ 𝕜 E f = f 1)]

end RingEquiv

end MultiplicationLinear

section SMulLinear

variable (𝕜) (𝕜' : Type*) [NormedField 𝕜']
variable [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

/-- Scalar multiplication as a continuous bilinear map. -/
def lsmul : 𝕜' →L[𝕜] E →L[𝕜] E :=
  ((Algebra.lsmul 𝕜 𝕜 E).toLinearMap : 𝕜' →ₗ[𝕜] E →ₗ[𝕜] E).mkContinuous₂ 1 fun c x => by
    simpa only [one_mul] using norm_smul_le c x
#align continuous_linear_map.lsmul ContinuousLinearMap.lsmul

@[simp]
theorem lsmul_apply (c : 𝕜') (x : E) : lsmul 𝕜 𝕜' c x = c • x :=
  rfl
#align continuous_linear_map.lsmul_apply ContinuousLinearMap.lsmul_apply

variable {𝕜'}

theorem norm_toSpanSingleton (x : E) : ‖toSpanSingleton 𝕜 x‖ = ‖x‖ := by
  refine opNorm_eq_of_bounds (norm_nonneg _) (fun x => ?_) fun N _ h => ?_
  · rw [toSpanSingleton_apply, norm_smul, mul_comm]
  · specialize h 1
    rw [toSpanSingleton_apply, norm_smul, mul_comm] at h
    exact (mul_le_mul_right (by simp)).mp h
#align continuous_linear_map.norm_to_span_singleton ContinuousLinearMap.norm_toSpanSingleton

variable {𝕜}

theorem opNorm_lsmul_apply_le (x : 𝕜') : ‖(lsmul 𝕜 𝕜' x : E →L[𝕜] E)‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y => norm_smul_le x y
#align continuous_linear_map.op_norm_lsmul_apply_le ContinuousLinearMap.opNorm_lsmul_apply_le

@[deprecated] alias op_norm_lsmul_apply_le := opNorm_lsmul_apply_le -- deprecated on 2024-02-02

/-- The norm of `lsmul` is at most 1 in any semi-normed group. -/
theorem opNorm_lsmul_le : ‖(lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp_rw [one_mul]
  exact opNorm_lsmul_apply_le _
#align continuous_linear_map.op_norm_lsmul_le ContinuousLinearMap.opNorm_lsmul_le

@[deprecated] alias op_norm_lsmul_le := opNorm_lsmul_le -- deprecated on 2024-02-02

end SMulLinear

end ContinuousLinearMap

end SemiNormed

section Normed

namespace ContinuousLinearMap

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] (c : 𝕜)
variable (𝕜) (𝕜' : Type*)

section

variable [NonUnitalNormedRing 𝕜'] [NormedSpace 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜']
variable [SMulCommClass 𝕜 𝕜' 𝕜'] [RegularNormedAlgebra 𝕜 𝕜'] [Nontrivial 𝕜']

@[simp]
theorem opNorm_mul : ‖mul 𝕜 𝕜'‖ = 1 :=
  (mulₗᵢ 𝕜 𝕜').norm_toContinuousLinearMap
#align continuous_linear_map.op_norm_mul ContinuousLinearMap.opNorm_mulₓ

@[deprecated] alias op_norm_mul := opNorm_mul -- deprecated on 2024-02-02

@[simp]
theorem opNNNorm_mul : ‖mul 𝕜 𝕜'‖₊ = 1 :=
  Subtype.ext <| opNorm_mul 𝕜 𝕜'
#align continuous_linear_map.op_nnnorm_mul ContinuousLinearMap.opNNNorm_mulₓ

@[deprecated] alias op_nnnorm_mul := opNNNorm_mul -- deprecated on 2024-02-02

end

/-- The norm of `lsmul` equals 1 in any nontrivial normed group.

This is `ContinuousLinearMap.opNorm_lsmul_le` as an equality. -/
@[simp]
theorem opNorm_lsmul [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' E]
    [IsScalarTower 𝕜 𝕜' E] [Nontrivial E] : ‖(lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E)‖ = 1 := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one (fun x => ?_) fun N _ h => ?_
  · rw [one_mul]
    apply opNorm_lsmul_apply_le
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  have := le_of_opNorm_le _ (h 1) y
  simp_rw [lsmul_apply, one_smul, norm_one, mul_one] at this
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hy)
  simp_rw [one_mul, this]
#align continuous_linear_map.op_norm_lsmul ContinuousLinearMap.opNorm_lsmul

@[deprecated] alias op_norm_lsmul := opNorm_lsmul -- deprecated on 2024-02-02

end ContinuousLinearMap

end Normed

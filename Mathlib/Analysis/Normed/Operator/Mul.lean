/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Results about operator norms in normed algebras

This file (split off from `OperatorNorm.lean`) contains results about the operator norm
of multiplication and scalar-multiplication operations in normed algebras and normed modules.
-/

@[expose] public section

suppress_compilation

open Metric
open scoped NNReal Topology Uniformity

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]

section SemiNormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace ContinuousLinearMap

section MultiplicationLinear

section NonUnital

variable (𝕜) (R : Type*) [NonUnitalSeminormedRing R]
variable [NormedSpace 𝕜 R] [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R]

/-- Multiplication in a non-unital normed algebra as a continuous bilinear map. -/
def mul : R →L[𝕜] R →L[𝕜] R :=
  (LinearMap.mul 𝕜 R).mkContinuous₂ 1 fun x y => by simpa using norm_mul_le x y

@[simp]
theorem mul_apply' (x y : R) : mul 𝕜 R x y = x * y :=
  rfl

@[simp]
theorem opNorm_mul_apply_le (x : R) : ‖mul 𝕜 R x‖ ≤ ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (norm_mul_le x)


theorem opNorm_mul_le : ‖mul 𝕜 R‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _


/-- Multiplication on the left in a non-unital normed algebra `R` as a non-unital algebra
homomorphism into the algebra of *continuous* linear maps. This is the left regular representation
of `A` acting on itself.

This has more algebraic structure than `ContinuousLinearMap.mul`, but there is no longer continuity
bundled in the first coordinate.  An alternative viewpoint is that this upgrades
`NonUnitalAlgHom.lmul` from a homomorphism into linear maps to a homomorphism into *continuous*
linear maps. -/
def _root_.NonUnitalAlgHom.Lmul : R →ₙₐ[𝕜] R →L[𝕜] R :=
  { mul 𝕜 R with
    map_mul' := fun _ _ ↦ ext fun _ ↦ mul_assoc _ _ _
    map_zero' := ext fun _ ↦ zero_mul _ }

variable {𝕜 R} in
@[simp]
theorem _root_.NonUnitalAlgHom.coe_Lmul : ⇑(NonUnitalAlgHom.Lmul 𝕜 R) = mul 𝕜 R :=
  rfl

/-- Simultaneous left- and right-multiplication in a non-unital normed algebra, considered as a
continuous trilinear map. This is akin to its non-continuous version `LinearMap.mulLeftRight`,
but there is a minor difference: `LinearMap.mulLeftRight` is uncurried. -/
def mulLeftRight : R →L[𝕜] R →L[𝕜] R →L[𝕜] R :=
  ((compL 𝕜 R R R).comp (mul 𝕜 R).flip).flip.comp (mul 𝕜 R)

@[simp]
theorem mulLeftRight_apply (x y z : R) : mulLeftRight 𝕜 R x y z = x * z * y :=
  rfl

theorem opNorm_mulLeftRight_apply_apply_le (x y : R) : ‖mulLeftRight 𝕜 R x y‖ ≤ ‖x‖ * ‖y‖ :=
  (opNorm_comp_le _ _).trans <|
    (mul_comm _ _).trans_le <|
      mul_le_mul (opNorm_mul_apply_le _ _ _)
        (opNorm_le_bound _ (norm_nonneg _) fun _ => (norm_mul_le _ _).trans_eq (mul_comm _ _))
        (norm_nonneg _) (norm_nonneg _)

theorem opNorm_mulLeftRight_apply_le (x : R) : ‖mulLeftRight 𝕜 R x‖ ≤ ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (opNorm_mulLeftRight_apply_apply_le 𝕜 R x)

theorem opNorm_mulLeftRight_le :
    ‖mulLeftRight 𝕜 R‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => (one_mul ‖x‖).symm ▸ opNorm_mulLeftRight_apply_le 𝕜 R x


/-- This is a mixin class for non-unital normed algebras which states that the left-regular
representation of the algebra on itself is isometric. Every unital normed algebra with `‖1‖ = 1` is
a regular normed algebra (see `NormedAlgebra.instRegularNormedAlgebra`). In addition, so is every
C⋆-algebra, non-unital included (see `CStarRing.instRegularNormedAlgebra`), but there are yet other
examples. Any algebra with an approximate identity (e.g., `L¹`) is also regular.

This is a useful class because it gives rise to a nice norm on the unitization; in particular it is
a C⋆-norm when the norm on `A` is a C⋆-norm. -/
class _root_.RegularNormedAlgebra : Prop where
  /-- The left regular representation of the algebra on itself is an isometry. -/
  isometry_mul' : Isometry (mul 𝕜 R)

/-- Every (unital) normed algebra such that `‖1‖ = 1` is a `RegularNormedAlgebra`. -/
instance _root_.NormedAlgebra.instRegularNormedAlgebra {𝕜 R : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedRing R] [NormedAlgebra 𝕜 R] [NormOneClass R] : RegularNormedAlgebra 𝕜 R where
  isometry_mul' := AddMonoidHomClass.isometry_of_norm (mul 𝕜 R) <|
    fun x => le_antisymm (opNorm_mul_apply_le _ _ _) <| by
      convert ratio_le_opNorm ((mul 𝕜 R) x) (1 : R)
      simp [norm_one]

variable [RegularNormedAlgebra 𝕜 R]

lemma isometry_mul : Isometry (mul 𝕜 R) :=
  RegularNormedAlgebra.isometry_mul'

@[simp]
lemma opNorm_mul_apply (x : R) : ‖mul 𝕜 R x‖ = ‖x‖ :=
  (AddMonoidHomClass.isometry_iff_norm (mul 𝕜 R)).mp (isometry_mul 𝕜 R) x


@[simp]
lemma opNNNorm_mul_apply (x : R) : ‖mul 𝕜 R x‖₊ = ‖x‖₊ :=
  Subtype.ext <| opNorm_mul_apply 𝕜 R x


/-- Multiplication in a normed algebra as a linear isometry to the space of
continuous linear maps. -/
def mulₗᵢ : R →ₗᵢ[𝕜] R →L[𝕜] R where
  toLinearMap := mul 𝕜 R
  norm_map' x := opNorm_mul_apply 𝕜 R x

@[simp]
theorem coe_mulₗᵢ : ⇑(mulₗᵢ 𝕜 R) = mul 𝕜 R :=
  rfl

end NonUnital

section NonUnitalSeminormedCommRing
variable {R : Type*} [NonUnitalSeminormedCommRing R] [NormedSpace 𝕜 R] [IsScalarTower 𝕜 R R]
  [SMulCommClass 𝕜 R R]

@[simp] lemma flip_mul : (ContinuousLinearMap.mul 𝕜 R).flip = .mul 𝕜 R := by ext; simp [mul_comm]

end NonUnitalSeminormedCommRing

section RingEquiv

variable (𝕜 E)

/-- If `M` is a normed space over `𝕜`, then the space of maps `𝕜 →L[𝕜] M` is linearly isometrically
equivalent to `M`. -/
def toSpanSingletonₗᵢ : E ≃ₗᵢ[𝕜] (𝕜 →L[𝕜] E) where
  toLinearEquiv := toSpanSingletonLE 𝕜 𝕜 E
  norm_map' _ := by simp

@[simp]
lemma toSpanSingletonₗᵢ_apply (x : E) : toSpanSingletonₗᵢ 𝕜 E x = toSpanSingleton 𝕜 x := rfl

@[simp] lemma toSpanSingletonₗᵢ_symm_apply (f : 𝕜 →L[𝕜] E) :
    (toSpanSingletonₗᵢ 𝕜 E).symm f = f 1 := rfl

@[simp] lemma toLinearEquiv_toSpanSingletonₗᵢ :
    (toSpanSingletonₗᵢ 𝕜 E).toLinearEquiv = toSpanSingletonLE 𝕜 𝕜 E := rfl
    
@[simp] lemma toContinuousLinearEquiv_toSpanSingletonₗᵢ :
    (toSpanSingletonₗᵢ 𝕜 E).toContinuousLinearEquiv = toSpanSingletonCLE := rfl

@[deprecated (since := "2026-04-23")]
alias ring_lmap_equiv_selfₗ := toSpanSingletonLE

@[deprecated (since := "2026-04-23")]
alias ring_lmap_equiv_self := toSpanSingletonₗᵢ

end RingEquiv

end MultiplicationLinear

section SMulLinear

variable (𝕜) (R : Type*) [SeminormedRing R]
variable [NormedAlgebra 𝕜 R] [Module R E] [IsBoundedSMul R E] [IsScalarTower 𝕜 R E]

/-- Scalar multiplication as a continuous bilinear map. -/
def lsmul : R →L[𝕜] E →L[𝕜] E :=
  ((Algebra.lsmul 𝕜 𝕜 E).toLinearMap : R →ₗ[𝕜] E →ₗ[𝕜] E).mkContinuous₂ 1 fun c x => by
    simpa only [one_mul] using norm_smul_le c x

@[simp]
theorem lsmul_apply (c : R) (x : E) : lsmul 𝕜 R c x = c • x :=
  rfl

variable {𝕜} in
@[simp]
theorem lsmul_flip_apply (x : E) :
    (lsmul 𝕜 𝕜).flip x = toSpanSingleton 𝕜 x :=
  rfl

variable {𝕜} in
theorem lsmul_flip_inj {x y : E} :
    (lsmul 𝕜 R).flip x = (lsmul 𝕜 R).flip y ↔ x = y :=
  ⟨fun h => by simpa using congr($h 1), fun h => h ▸ rfl⟩

variable {R 𝕜}

theorem opNorm_lsmul_apply_le (x : R) : ‖(lsmul 𝕜 R x : E →L[𝕜] E)‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y => norm_smul_le x y

/-- The norm of `lsmul` is at most 1 in any semi-normed group. -/
theorem opNorm_lsmul_le : ‖(lsmul 𝕜 R : R →L[𝕜] E →L[𝕜] E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp_rw [one_mul]
  exact opNorm_lsmul_apply_le _

end SMulLinear

end ContinuousLinearMap

end SemiNormed

section Normed

namespace ContinuousLinearMap

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (𝕜) (R : Type*)

section

variable [NonUnitalNormedRing R] [NormedSpace 𝕜 R] [IsScalarTower 𝕜 R R]
variable [SMulCommClass 𝕜 R R] [RegularNormedAlgebra 𝕜 R] [Nontrivial R]

@[simp]
theorem opNorm_mul : ‖mul 𝕜 R‖ = 1 :=
  (mulₗᵢ 𝕜 R).norm_toContinuousLinearMap


@[simp]
theorem opNNNorm_mul : ‖mul 𝕜 R‖₊ = 1 :=
  Subtype.ext <| opNorm_mul 𝕜 R


end

/-- The norm of `lsmul` equals 1 in any nontrivial normed group.

This is `ContinuousLinearMap.opNorm_lsmul_le` as an equality. -/
@[simp]
theorem opNorm_lsmul [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E]
    [IsScalarTower 𝕜 R E] [Nontrivial E] : ‖(lsmul 𝕜 R : R →L[𝕜] E →L[𝕜] E)‖ = 1 := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one (fun x => ?_) fun N _ h => ?_
  · rw [one_mul]
    apply opNorm_lsmul_apply_le
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hy)
  simpa using le_of_opNorm_le _ (h 1) y

end ContinuousLinearMap

end Normed

/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2

#align_import analysis.inner_product_space.adjoint from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Adjoint of operators on Hilbert spaces

Given an operator `A : E →L[𝕜] F`, where `E` and `F` are Hilbert spaces, its adjoint
`adjoint A : F →L[𝕜] E` is the unique operator such that `⟪x, A y⟫ = ⟪adjoint A x, y⟫` for all
`x` and `y`.

We then use this to put a C⋆-algebra structure on `E →L[𝕜] E` with the adjoint as the star
operation.

This construction is used to define an adjoint for linear maps (i.e. not continuous) between
finite dimensional spaces.

## Main definitions

* `ContinuousLinearMap.adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E)`: the adjoint of a continuous
  linear map, bundled as a conjugate-linear isometric equivalence.
* `LinearMap.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)`: the adjoint of a linear map between
  finite-dimensional spaces, this time only as a conjugate-linear equivalence, since there is no
  norm defined on these maps.

## Implementation notes

* The continuous conjugate-linear version `adjointAux` is only an intermediate
  definition and is not meant to be used outside this file.

## Tags

adjoint

-/

noncomputable section

open RCLike

open scoped ComplexConjugate

variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-! ### Adjoint operator -/


open InnerProductSpace

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace G]

-- Note: made noncomputable to stop excess compilation
-- leanprover-community/mathlib4#7103
/-- The adjoint, as a continuous conjugate-linear map. This is only meant as an auxiliary
definition for the main definition `adjoint`, where this is bundled as a conjugate-linear isometric
equivalence. -/
noncomputable def adjointAux : (E →L[𝕜] F) →L⋆[𝕜] F →L[𝕜] E :=
  (ContinuousLinearMap.compSL _ _ _ _ _ ((toDual 𝕜 E).symm : NormedSpace.Dual 𝕜 E →L⋆[𝕜] E)).comp
    (toSesqForm : (E →L[𝕜] F) →L[𝕜] F →L⋆[𝕜] NormedSpace.Dual 𝕜 E)
#align continuous_linear_map.adjoint_aux ContinuousLinearMap.adjointAux

@[simp]
theorem adjointAux_apply (A : E →L[𝕜] F) (x : F) :
    adjointAux A x = ((toDual 𝕜 E).symm : NormedSpace.Dual 𝕜 E → E) ((toSesqForm A) x) :=
  rfl
#align continuous_linear_map.adjoint_aux_apply ContinuousLinearMap.adjointAux_apply

theorem adjointAux_inner_left (A : E →L[𝕜] F) (x : E) (y : F) : ⟪adjointAux A y, x⟫ = ⟪y, A x⟫ := by
  rw [adjointAux_apply, toDual_symm_apply, toSesqForm_apply_coe, coe_comp', innerSL_apply_coe,
    Function.comp_apply]
#align continuous_linear_map.adjoint_aux_inner_left ContinuousLinearMap.adjointAux_inner_left

theorem adjointAux_inner_right (A : E →L[𝕜] F) (x : E) (y : F) :
    ⟪x, adjointAux A y⟫ = ⟪A x, y⟫ := by
  rw [← inner_conj_symm, adjointAux_inner_left, inner_conj_symm]
#align continuous_linear_map.adjoint_aux_inner_right ContinuousLinearMap.adjointAux_inner_right

variable [CompleteSpace F]

theorem adjointAux_adjointAux (A : E →L[𝕜] F) : adjointAux (adjointAux A) = A := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjointAux_inner_right, adjointAux_inner_left]
#align continuous_linear_map.adjoint_aux_adjoint_aux ContinuousLinearMap.adjointAux_adjointAux

@[simp]
theorem adjointAux_norm (A : E →L[𝕜] F) : ‖adjointAux A‖ = ‖A‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [adjointAux_apply, LinearIsometryEquiv.norm_map]
    exact toSesqForm_apply_norm_le
  · nth_rw 1 [← adjointAux_adjointAux A]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [adjointAux_apply, LinearIsometryEquiv.norm_map]
    exact toSesqForm_apply_norm_le
#align continuous_linear_map.adjoint_aux_norm ContinuousLinearMap.adjointAux_norm

/-- The adjoint of a bounded operator from Hilbert space `E` to Hilbert space `F`. -/
def adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] F →L[𝕜] E :=
  LinearIsometryEquiv.ofSurjective { adjointAux with norm_map' := adjointAux_norm } fun A =>
    ⟨adjointAux A, adjointAux_adjointAux A⟩
#align continuous_linear_map.adjoint ContinuousLinearMap.adjoint

scoped[InnerProduct] postfix:1000 "†" => ContinuousLinearMap.adjoint
open InnerProduct

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_left (A : E →L[𝕜] F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫ :=
  adjointAux_inner_left A x y
#align continuous_linear_map.adjoint_inner_left ContinuousLinearMap.adjoint_inner_left

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_right (A : E →L[𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫ :=
  adjointAux_inner_right A x y
#align continuous_linear_map.adjoint_inner_right ContinuousLinearMap.adjoint_inner_right

/-- The adjoint is involutive. -/
@[simp]
theorem adjoint_adjoint (A : E →L[𝕜] F) : A†† = A :=
  adjointAux_adjointAux A
#align continuous_linear_map.adjoint_adjoint ContinuousLinearMap.adjoint_adjoint

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
theorem adjoint_comp (A : F →L[𝕜] G) (B : E →L[𝕜] F) : (A ∘L B)† = B† ∘L A† := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp only [adjoint_inner_right, ContinuousLinearMap.coe_comp', Function.comp_apply]
#align continuous_linear_map.adjoint_comp ContinuousLinearMap.adjoint_comp

theorem apply_norm_sq_eq_inner_adjoint_left (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ ^ 2 = re ⟪(A† ∘L A) x, x⟫ := by
  have h : ⟪(A† ∘L A) x, x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_left]; rfl
  rw [h, ← inner_self_eq_norm_sq (𝕜 := 𝕜) _]
#align continuous_linear_map.apply_norm_sq_eq_inner_adjoint_left ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left

theorem apply_norm_eq_sqrt_inner_adjoint_left (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ = √(re ⟪(A† ∘L A) x, x⟫) := by
  rw [← apply_norm_sq_eq_inner_adjoint_left, Real.sqrt_sq (norm_nonneg _)]
#align continuous_linear_map.apply_norm_eq_sqrt_inner_adjoint_left ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_left

theorem apply_norm_sq_eq_inner_adjoint_right (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ ^ 2 = re ⟪x, (A† ∘L A) x⟫ := by
  have h : ⟪x, (A† ∘L A) x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_right]; rfl
  rw [h, ← inner_self_eq_norm_sq (𝕜 := 𝕜) _]
#align continuous_linear_map.apply_norm_sq_eq_inner_adjoint_right ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right

theorem apply_norm_eq_sqrt_inner_adjoint_right (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ = √(re ⟪x, (A† ∘L A) x⟫) := by
  rw [← apply_norm_sq_eq_inner_adjoint_right, Real.sqrt_sq (norm_nonneg _)]
#align continuous_linear_map.apply_norm_eq_sqrt_inner_adjoint_right ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_right

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
theorem eq_adjoint_iff (A : E →L[𝕜] F) (B : F →L[𝕜] E) : A = B† ↔ ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]
#align continuous_linear_map.eq_adjoint_iff ContinuousLinearMap.eq_adjoint_iff

@[simp]
theorem adjoint_id :
    ContinuousLinearMap.adjoint (ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 E := by
  refine Eq.symm ?_
  rw [eq_adjoint_iff]
  simp
#align continuous_linear_map.adjoint_id ContinuousLinearMap.adjoint_id

theorem _root_.Submodule.adjoint_subtypeL (U : Submodule 𝕜 E) [CompleteSpace U] :
    U.subtypeL† = orthogonalProjection U := by
  symm
  rw [eq_adjoint_iff]
  intro x u
  rw [U.coe_inner, inner_orthogonalProjection_left_eq_right,
    orthogonalProjection_mem_subspace_eq_self]
  rfl
set_option linter.uppercaseLean3 false in
#align submodule.adjoint_subtypeL Submodule.adjoint_subtypeL

theorem _root_.Submodule.adjoint_orthogonalProjection (U : Submodule 𝕜 E) [CompleteSpace U] :
    (orthogonalProjection U : E →L[𝕜] U)† = U.subtypeL := by
  rw [← U.adjoint_subtypeL, adjoint_adjoint]
#align submodule.adjoint_orthogonal_projection Submodule.adjoint_orthogonalProjection

/-- `E →L[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : Star (E →L[𝕜] E) :=
  ⟨adjoint⟩

instance : InvolutiveStar (E →L[𝕜] E) :=
  ⟨adjoint_adjoint⟩

instance : StarMul (E →L[𝕜] E) :=
  ⟨adjoint_comp⟩

instance : StarRing (E →L[𝕜] E) :=
  ⟨LinearIsometryEquiv.map_add adjoint⟩

instance : StarModule 𝕜 (E →L[𝕜] E) :=
  ⟨LinearIsometryEquiv.map_smulₛₗ adjoint⟩

theorem star_eq_adjoint (A : E →L[𝕜] E) : star A = A† :=
  rfl
#align continuous_linear_map.star_eq_adjoint ContinuousLinearMap.star_eq_adjoint

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
theorem isSelfAdjoint_iff' {A : E →L[𝕜] E} : IsSelfAdjoint A ↔ ContinuousLinearMap.adjoint A = A :=
  Iff.rfl
#align continuous_linear_map.is_self_adjoint_iff' ContinuousLinearMap.isSelfAdjoint_iff'

theorem norm_adjoint_comp_self (A : E →L[𝕜] F) :
    ‖ContinuousLinearMap.adjoint A ∘L A‖ = ‖A‖ * ‖A‖ := by
  refine le_antisymm ?_ ?_
  · calc
      ‖A† ∘L A‖ ≤ ‖A†‖ * ‖A‖ := opNorm_comp_le _ _
      _ = ‖A‖ * ‖A‖ := by rw [LinearIsometryEquiv.norm_map]
  · rw [← sq, ← Real.sqrt_le_sqrt_iff (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    refine opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have :=
      calc
        re ⟪(A† ∘L A) x, x⟫ ≤ ‖(A† ∘L A) x‖ * ‖x‖ := re_inner_le_norm _ _
        _ ≤ ‖A† ∘L A‖ * ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right (le_opNorm _ _) (norm_nonneg _)
    calc
      ‖A x‖ = √(re ⟪(A† ∘L A) x, x⟫) := by rw [apply_norm_eq_sqrt_inner_adjoint_left]
      _ ≤ √(‖A† ∘L A‖ * ‖x‖ * ‖x‖) := Real.sqrt_le_sqrt this
      _ = √‖A† ∘L A‖ * ‖x‖ := by
        simp_rw [mul_assoc, Real.sqrt_mul (norm_nonneg _) (‖x‖ * ‖x‖),
          Real.sqrt_mul_self (norm_nonneg x)]

instance : CstarRing (E →L[𝕜] E) where
  norm_star_mul_self := norm_adjoint_comp_self _

theorem isAdjointPair_inner (A : E →L[𝕜] F) :
    LinearMap.IsAdjointPair (sesqFormOfInner : E →ₗ[𝕜] E →ₗ⋆[𝕜] 𝕜)
      (sesqFormOfInner : F →ₗ[𝕜] F →ₗ⋆[𝕜] 𝕜) A (A†) := by
  intro x y
  simp only [sesqFormOfInner_apply_apply, adjoint_inner_left, coe_coe]
#align continuous_linear_map.is_adjoint_pair_inner ContinuousLinearMap.isAdjointPair_inner

end ContinuousLinearMap

/-! ### Self-adjoint operators -/


namespace IsSelfAdjoint

open ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]

theorem adjoint_eq {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) : ContinuousLinearMap.adjoint A = A :=
  hA
#align is_self_adjoint.adjoint_eq IsSelfAdjoint.adjoint_eq

/-- Every self-adjoint operator on an inner product space is symmetric. -/
theorem isSymmetric {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) : (A : E →ₗ[𝕜] E).IsSymmetric := by
  intro x y
  rw_mod_cast [← A.adjoint_inner_right, hA.adjoint_eq]
#align is_self_adjoint.is_symmetric IsSelfAdjoint.isSymmetric

/-- Conjugating preserves self-adjointness. -/
theorem conj_adjoint {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (S : E →L[𝕜] F) :
    IsSelfAdjoint (S ∘L T ∘L ContinuousLinearMap.adjoint S) := by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _
#align is_self_adjoint.conj_adjoint IsSelfAdjoint.conj_adjoint

/-- Conjugating preserves self-adjointness. -/
theorem adjoint_conj {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (S : F →L[𝕜] E) :
    IsSelfAdjoint (ContinuousLinearMap.adjoint S ∘L T ∘L S) := by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _
#align is_self_adjoint.adjoint_conj IsSelfAdjoint.adjoint_conj

theorem _root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric {A : E →L[𝕜] E} :
    IsSelfAdjoint A ↔ (A : E →ₗ[𝕜] E).IsSymmetric :=
  ⟨fun hA => hA.isSymmetric, fun hA =>
    ext fun x => ext_inner_right 𝕜 fun y => (A.adjoint_inner_left y x).symm ▸ (hA x y).symm⟩
#align continuous_linear_map.is_self_adjoint_iff_is_symmetric ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric

theorem _root_.LinearMap.IsSymmetric.isSelfAdjoint {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) : IsSelfAdjoint A := by
  rwa [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA
#align linear_map.is_symmetric.is_self_adjoint LinearMap.IsSymmetric.isSelfAdjoint

/-- The orthogonal projection is self-adjoint. -/
theorem _root_.orthogonalProjection_isSelfAdjoint (U : Submodule 𝕜 E) [CompleteSpace U] :
    IsSelfAdjoint (U.subtypeL ∘L orthogonalProjection U) :=
  (orthogonalProjection_isSymmetric U).isSelfAdjoint
#align orthogonal_projection_is_self_adjoint orthogonalProjection_isSelfAdjoint

theorem conj_orthogonalProjection {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (U : Submodule 𝕜 E)
    [CompleteSpace U] :
    IsSelfAdjoint
      (U.subtypeL ∘L orthogonalProjection U ∘L T ∘L U.subtypeL ∘L orthogonalProjection U) := by
  rw [← ContinuousLinearMap.comp_assoc]
  nth_rw 1 [← (orthogonalProjection_isSelfAdjoint U).adjoint_eq]
  exact hT.adjoint_conj _
#align is_self_adjoint.conj_orthogonal_projection IsSelfAdjoint.conj_orthogonalProjection

end IsSelfAdjoint

namespace LinearMap

variable [CompleteSpace E]
variable {T : E →ₗ[𝕜] E}

/-- The **Hellinger--Toeplitz theorem**: Construct a self-adjoint operator from an everywhere
  defined symmetric operator. -/
def IsSymmetric.toSelfAdjoint (hT : IsSymmetric T) : selfAdjoint (E →L[𝕜] E) :=
  ⟨⟨T, hT.continuous⟩, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT⟩
#align linear_map.is_symmetric.to_self_adjoint LinearMap.IsSymmetric.toSelfAdjoint

theorem IsSymmetric.coe_toSelfAdjoint (hT : IsSymmetric T) : (hT.toSelfAdjoint : E →ₗ[𝕜] E) = T :=
  rfl
#align linear_map.is_symmetric.coe_to_self_adjoint LinearMap.IsSymmetric.coe_toSelfAdjoint

theorem IsSymmetric.toSelfAdjoint_apply (hT : IsSymmetric T) {x : E} :
    (hT.toSelfAdjoint : E → E) x = T x :=
  rfl
#align linear_map.is_symmetric.to_self_adjoint_apply LinearMap.IsSymmetric.toSelfAdjoint_apply

end LinearMap

namespace LinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]

/- Porting note: Lean can't use `FiniteDimensional.complete` since it was generalized to topological
vector spaces. Use local instances instead. -/

/-- The adjoint of an operator from the finite-dimensional inner product space `E` to the
finite-dimensional inner product space `F`. -/
def adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] F →ₗ[𝕜] E :=
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  /- Note: Instead of the two instances above, the following works:
    ```
      have := FiniteDimensional.complete 𝕜
      have := FiniteDimensional.complete 𝕜
    ```
    But removing one of the `have`s makes it fail. The reason is that `E` and `F` don't live
    in the same universe, so the first `have` can no longer be used for `F` after its universe
    metavariable has been assigned to that of `E`!
  -/
  ((LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] F) ≃ₗ[𝕜] E →L[𝕜] F).trans
      ContinuousLinearMap.adjoint.toLinearEquiv).trans
    LinearMap.toContinuousLinearMap.symm
#align linear_map.adjoint LinearMap.adjoint

theorem adjoint_toContinuousLinearMap (A : E →ₗ[𝕜] F) :
    haveI := FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    LinearMap.toContinuousLinearMap (LinearMap.adjoint A) =
      ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap A) :=
  rfl
#align linear_map.adjoint_to_continuous_linear_map LinearMap.adjoint_toContinuousLinearMap

theorem adjoint_eq_toCLM_adjoint (A : E →ₗ[𝕜] F) :
    haveI := FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    LinearMap.adjoint A = ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap A) :=
  rfl
#align linear_map.adjoint_eq_to_clm_adjoint LinearMap.adjoint_eq_toCLM_adjoint

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_left (A : E →ₗ[𝕜] F) (x : E) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫ := by
  haveI := FiniteDimensional.complete 𝕜 E
  haveI := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A, adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left _ x y
#align linear_map.adjoint_inner_left LinearMap.adjoint_inner_left

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_right (A : E →ₗ[𝕜] F) (x : E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫ := by
  haveI := FiniteDimensional.complete 𝕜 E
  haveI := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A, adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_right _ x y
#align linear_map.adjoint_inner_right LinearMap.adjoint_inner_right

/-- The adjoint is involutive. -/
@[simp]
theorem adjoint_adjoint (A : E →ₗ[𝕜] F) : LinearMap.adjoint (LinearMap.adjoint A) = A := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjoint_inner_right, adjoint_inner_left]
#align linear_map.adjoint_adjoint LinearMap.adjoint_adjoint

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
theorem adjoint_comp (A : F →ₗ[𝕜] G) (B : E →ₗ[𝕜] F) :
    LinearMap.adjoint (A ∘ₗ B) = LinearMap.adjoint B ∘ₗ LinearMap.adjoint A := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp only [adjoint_inner_right, LinearMap.coe_comp, Function.comp_apply]
#align linear_map.adjoint_comp LinearMap.adjoint_comp

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
theorem eq_adjoint_iff (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = LinearMap.adjoint B ↔ ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]
#align linear_map.eq_adjoint_iff LinearMap.eq_adjoint_iff

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all basis vectors `x` and `y`. -/
theorem eq_adjoint_iff_basis {ι₁ : Type*} {ι₂ : Type*} (b₁ : Basis ι₁ 𝕜 E) (b₂ : Basis ι₂ 𝕜 F)
    (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = LinearMap.adjoint B ↔ ∀ (i₁ : ι₁) (i₂ : ι₂), ⟪A (b₁ i₁), b₂ i₂⟫ = ⟪b₁ i₁, B (b₂ i₂)⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  refine Basis.ext b₁ fun i₁ => ?_
  exact ext_inner_right_basis b₂ fun i₂ => by simp only [adjoint_inner_left, h i₁ i₂]
#align linear_map.eq_adjoint_iff_basis LinearMap.eq_adjoint_iff_basis

theorem eq_adjoint_iff_basis_left {ι : Type*} (b : Basis ι 𝕜 E) (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = LinearMap.adjoint B ↔ ∀ i y, ⟪A (b i), y⟫ = ⟪b i, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => Basis.ext b fun i => ?_⟩
  exact ext_inner_right 𝕜 fun y => by simp only [h i, adjoint_inner_left]
#align linear_map.eq_adjoint_iff_basis_left LinearMap.eq_adjoint_iff_basis_left

theorem eq_adjoint_iff_basis_right {ι : Type*} (b : Basis ι 𝕜 F) (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = LinearMap.adjoint B ↔ ∀ i x, ⟪A x, b i⟫ = ⟪x, B (b i)⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right_basis b fun i => by simp only [h i, adjoint_inner_left]
#align linear_map.eq_adjoint_iff_basis_right LinearMap.eq_adjoint_iff_basis_right

/-- `E →ₗ[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : Star (E →ₗ[𝕜] E) :=
  ⟨adjoint⟩

instance : InvolutiveStar (E →ₗ[𝕜] E) :=
  ⟨adjoint_adjoint⟩

instance : StarMul (E →ₗ[𝕜] E) :=
  ⟨adjoint_comp⟩

instance : StarRing (E →ₗ[𝕜] E) :=
  ⟨LinearEquiv.map_add adjoint⟩

instance : StarModule 𝕜 (E →ₗ[𝕜] E) :=
  ⟨LinearEquiv.map_smulₛₗ adjoint⟩

theorem star_eq_adjoint (A : E →ₗ[𝕜] E) : star A = LinearMap.adjoint A :=
  rfl
#align linear_map.star_eq_adjoint LinearMap.star_eq_adjoint

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
theorem isSelfAdjoint_iff' {A : E →ₗ[𝕜] E} : IsSelfAdjoint A ↔ LinearMap.adjoint A = A :=
  Iff.rfl
#align linear_map.is_self_adjoint_iff' LinearMap.isSelfAdjoint_iff'

theorem isSymmetric_iff_isSelfAdjoint (A : E →ₗ[𝕜] E) : IsSymmetric A ↔ IsSelfAdjoint A := by
  rw [isSelfAdjoint_iff', IsSymmetric, ← LinearMap.eq_adjoint_iff]
  exact eq_comm
#align linear_map.is_symmetric_iff_is_self_adjoint LinearMap.isSymmetric_iff_isSelfAdjoint

theorem isAdjointPair_inner (A : E →ₗ[𝕜] F) :
    IsAdjointPair (sesqFormOfInner : E →ₗ[𝕜] E →ₗ⋆[𝕜] 𝕜) (sesqFormOfInner : F →ₗ[𝕜] F →ₗ⋆[𝕜] 𝕜) A
      (LinearMap.adjoint A) := by
  intro x y
  simp only [sesqFormOfInner_apply_apply, adjoint_inner_left]
#align linear_map.is_adjoint_pair_inner LinearMap.isAdjointPair_inner

/-- The Gram operator T†T is symmetric. -/
theorem isSymmetric_adjoint_mul_self (T : E →ₗ[𝕜] E) : IsSymmetric (LinearMap.adjoint T * T) := by
  intro x y
  simp only [mul_apply, adjoint_inner_left, adjoint_inner_right]
#align linear_map.is_symmetric_adjoint_mul_self LinearMap.isSymmetric_adjoint_mul_self

/-- The Gram operator T†T is a positive operator. -/
theorem re_inner_adjoint_mul_self_nonneg (T : E →ₗ[𝕜] E) (x : E) :
    0 ≤ re ⟪x, (LinearMap.adjoint T * T) x⟫ := by
  simp only [mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact sq_nonneg _
#align linear_map.re_inner_adjoint_mul_self_nonneg LinearMap.re_inner_adjoint_mul_self_nonneg

@[simp]
theorem im_inner_adjoint_mul_self_eq_zero (T : E →ₗ[𝕜] E) (x : E) :
    im ⟪x, LinearMap.adjoint T (T x)⟫ = 0 := by
  simp only [mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast
#align linear_map.im_inner_adjoint_mul_self_eq_zero LinearMap.im_inner_adjoint_mul_self_eq_zero

end LinearMap

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

theorem inner_map_map_iff_adjoint_comp_self (u : H →L[𝕜] K) :
    (∀ x y : H, ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜) ↔ adjoint u ∘L u = 1 := by
  refine ⟨fun h ↦ ext fun x ↦ ?_, fun h ↦ ?_⟩
  · refine ext_inner_right 𝕜 fun y ↦ ?_
    simpa [star_eq_adjoint, adjoint_inner_left] using h x y
  · simp [← adjoint_inner_left, ← comp_apply, h]

theorem norm_map_iff_adjoint_comp_self (u : H →L[𝕜] K) :
    (∀ x : H, ‖u x‖ = ‖x‖) ↔ adjoint u ∘L u = 1 := by
  rw [LinearMap.norm_map_iff_inner_map_map u, u.inner_map_map_iff_adjoint_comp_self]

@[simp]
lemma _root_.LinearIsometryEquiv.adjoint_eq_symm (e : H ≃ₗᵢ[𝕜] K) :
    adjoint (e : H →L[𝕜] K) = e.symm :=
  let e' := (e : H →L[𝕜] K)
  calc
    adjoint e' = adjoint e' ∘L (e' ∘L e.symm) := by
      convert (adjoint e').comp_id.symm
      ext
      simp [e']
    _ = e.symm := by
      rw [← comp_assoc, norm_map_iff_adjoint_comp_self e' |>.mp e.norm_map]
      exact (e.symm : K →L[𝕜] H).id_comp

@[simp]
lemma _root_.LinearIsometryEquiv.star_eq_symm (e : H ≃ₗᵢ[𝕜] H) :
    star (e : H →L[𝕜] H) = e.symm :=
  e.adjoint_eq_symm

theorem norm_map_of_mem_unitary {u : H →L[𝕜] H} (hu : u ∈ unitary (H →L[𝕜] H)) (x : H) :
    ‖u x‖ = ‖x‖ :=
  -- Elaborates faster with this broken out #11299
  have := unitary.star_mul_self_of_mem hu
  u.norm_map_iff_adjoint_comp_self.mpr this x

theorem inner_map_map_of_mem_unitary {u : H →L[𝕜] H} (hu : u ∈ unitary (H →L[𝕜] H)) (x y : H) :
    ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  -- Elaborates faster with this broken out #11299
  have := unitary.star_mul_self_of_mem hu
  u.inner_map_map_iff_adjoint_comp_self.mpr this x y

end ContinuousLinearMap

namespace unitary

theorem norm_map (u : unitary (H →L[𝕜] H)) (x : H) : ‖(u : H →L[𝕜] H) x‖ = ‖x‖ :=
  u.val.norm_map_of_mem_unitary u.property x

theorem inner_map_map (u : unitary (H →L[𝕜] H)) (x y : H) :
    ⟪(u : H →L[𝕜] H) x, (u : H →L[𝕜] H) y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  u.val.inner_map_map_of_mem_unitary u.property x y

/-- The unitary elements of continuous linear maps on a Hilbert space coincide with the linear
isometric equivalences on that Hilbert space. -/
noncomputable def linearIsometryEquiv : unitary (H →L[𝕜] H) ≃* (H ≃ₗᵢ[𝕜] H) where
  toFun u :=
    { (u : H →L[𝕜] H) with
      norm_map' := norm_map u
      invFun := ↑(star u)
      left_inv := fun x ↦ congr($(star_mul_self u).val x)
      right_inv := fun x ↦ congr($(mul_star_self u).val x) }
  invFun e :=
    { val := e
      property := by
        let e' : (H →L[𝕜] H)ˣ :=
          { val := (e : H →L[𝕜] H)
            inv := (e.symm : H →L[𝕜] H)
            val_inv := by ext; simp
            inv_val := by ext; simp }
        exact IsUnit.mem_unitary_of_star_mul_self ⟨e', rfl⟩ <|
          (e : H →L[𝕜] H).norm_map_iff_adjoint_comp_self.mp e.norm_map }
  left_inv u := Subtype.ext rfl
  right_inv e := LinearIsometryEquiv.ext fun x ↦ rfl
  map_mul' u v := by ext; rfl

@[simp]
lemma linearIsometryEquiv_coe_apply (u : unitary (H →L[𝕜] H)) :
    linearIsometryEquiv u = (u : H →L[𝕜] H) :=
  rfl

@[simp]
lemma linearIsometryEquiv_coe_symm_apply (e : H ≃ₗᵢ[𝕜] H) :
    linearIsometryEquiv.symm e = (e : H →L[𝕜] H) :=
  rfl

end unitary

end Unitary

section Matrix

open Matrix LinearMap

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
variable (v₁ : OrthonormalBasis n 𝕜 E) (v₂ : OrthonormalBasis m 𝕜 F)

/-- The linear map associated to the conjugate transpose of a matrix corresponding to two
orthonormal bases is the adjoint of the linear map associated to the matrix. -/
lemma Matrix.toLin_conjTranspose (A : Matrix m n 𝕜) :
    toLin v₂.toBasis v₁.toBasis Aᴴ = adjoint (toLin v₁.toBasis v₂.toBasis A) := by
  refine eq_adjoint_iff_basis v₂.toBasis v₁.toBasis _ _ |>.mpr fun i j ↦ ?_
  simp_rw [toLin_self]
  simp [sum_inner, inner_smul_left, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp v₁.orthonormal, orthonormal_iff_ite.mp v₂.orthonormal]

/-- The matrix associated to the adjoint of a linear map corresponding to two orthonormal bases
is the conjugate tranpose of the matrix associated to the linear map. -/
lemma LinearMap.toMatrix_adjoint (f : E →ₗ[𝕜] F) :
    toMatrix v₂.toBasis v₁.toBasis (adjoint f) = (toMatrix v₁.toBasis v₂.toBasis f)ᴴ :=
  toLin v₂.toBasis v₁.toBasis |>.injective <| by simp [toLin_conjTranspose]

/-- The star algebra equivalence between the linear endomorphisms of finite-dimensional inner
product space and square matrices induced by the choice of an orthonormal basis. -/
@[simps]
def LinearMap.toMatrixOrthonormal : (E →ₗ[𝕜] E) ≃⋆ₐ[𝕜] Matrix n n 𝕜 :=
  { LinearMap.toMatrix v₁.toBasis v₁.toBasis with
    map_mul' := LinearMap.toMatrix_mul v₁.toBasis
    map_star' := LinearMap.toMatrix_adjoint v₁ v₁ }

open scoped ComplexConjugate

/-- The adjoint of the linear map associated to a matrix is the linear map associated to the
conjugate transpose of that matrix. -/
theorem Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A : Matrix m n 𝕜) :
    Matrix.toEuclideanLin A.conjTranspose = LinearMap.adjoint (Matrix.toEuclideanLin A) :=
  A.toLin_conjTranspose (EuclideanSpace.basisFun n 𝕜) (EuclideanSpace.basisFun m 𝕜)
#align matrix.to_euclidean_lin_conj_transpose_eq_adjoint Matrix.toEuclideanLin_conjTranspose_eq_adjoint

end Matrix

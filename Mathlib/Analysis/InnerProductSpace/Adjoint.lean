/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike


/-!
# Adjoint of operators on Hilbert spaces

Given an operator `A : E →L[𝕜] F`, where `E` and `F` are Hilbert spaces, its adjoint
`adjoint A : F →L[𝕜] E` is the unique operator such that `⟪x, A y⟫ = ⟪adjoint A x, y⟫` for all
`x` and `y`.

We then use this to put a C⋆-algebra structure on `E →L[𝕜] E` with the adjoint as the star
operation.

This construction is used to define an adjoint for linear maps (i.e. not continuous) between
finite-dimensional spaces.

## Main definitions

* `ContinuousLinearMap.adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E)`: the adjoint of a continuous
  linear map, bundled as a conjugate-linear isometric equivalence.
* `LinearMap.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)`: the adjoint of a linear map between
  finite-dimensional spaces, this time only as a conjugate-linear equivalence, since there is no
  norm defined on these maps.

## Implementation notes

* The continuous conjugate-linear version `adjointAux` is only an intermediate
  definition and is not meant to be used outside this file.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]

## Tags

adjoint

-/

@[expose] public section

noncomputable section

open Module RCLike

open scoped ComplexConjugate

variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Adjoint operator -/


open InnerProductSpace

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace G]

-- Note: made noncomputable to stop excess compilation
-- https://github.com/leanprover-community/mathlib4/issues/7103
/-- The adjoint, as a continuous conjugate-linear map. This is only meant as an auxiliary
definition for the main definition `adjoint`, where this is bundled as a conjugate-linear isometric
equivalence. -/
noncomputable def adjointAux : (E →L[𝕜] F) →L⋆[𝕜] F →L[𝕜] E :=
  (ContinuousLinearMap.compSL _ _ _ _ _ ((toDual 𝕜 E).symm : StrongDual 𝕜 E →L⋆[𝕜] E)).comp
    (toSesqForm : (E →L[𝕜] F) →L[𝕜] F →L⋆[𝕜] StrongDual 𝕜 E)

@[simp]
theorem adjointAux_apply (A : E →L[𝕜] F) (x : F) :
    adjointAux A x = ((toDual 𝕜 E).symm : StrongDual 𝕜 E → E) ((toSesqForm A) x) :=
  rfl

theorem adjointAux_inner_left (A : E →L[𝕜] F) (x : E) (y : F) : ⟪adjointAux A y, x⟫ = ⟪y, A x⟫ := by
  rw [adjointAux_apply, toDual_symm_apply, toSesqForm_apply_coe, coe_comp', coe_innerSL_apply,
    Function.comp_apply]

theorem adjointAux_inner_right (A : E →L[𝕜] F) (x : E) (y : F) :
    ⟪x, adjointAux A y⟫ = ⟪A x, y⟫ := by
  rw [← inner_conj_symm, adjointAux_inner_left, inner_conj_symm]

variable [CompleteSpace F]

theorem adjointAux_adjointAux (A : E →L[𝕜] F) : adjointAux (adjointAux A) = A := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjointAux_inner_right, adjointAux_inner_left]

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

/-- The adjoint of a bounded operator `A` from a Hilbert space `E` to another Hilbert space `F`,
  denoted as `A†`. -/
def adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] F →L[𝕜] E :=
  LinearIsometryEquiv.ofSurjective { adjointAux with norm_map' := adjointAux_norm } fun A =>
    ⟨adjointAux A, adjointAux_adjointAux A⟩

@[inherit_doc]
scoped[InnerProduct] postfix:1000 "†" => ContinuousLinearMap.adjoint
open InnerProduct

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_left (A : E →L[𝕜] F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫ :=
  adjointAux_inner_left A x y

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_right (A : E →L[𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫ :=
  adjointAux_inner_right A x y

/-- The adjoint is involutive. -/
@[simp]
theorem adjoint_adjoint (A : E →L[𝕜] F) : A†† = A :=
  adjointAux_adjointAux A

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
theorem adjoint_comp (A : F →L[𝕜] G) (B : E →L[𝕜] F) : (A ∘L B)† = B† ∘L A† := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp only [adjoint_inner_right, ContinuousLinearMap.coe_comp', Function.comp_apply]

theorem apply_norm_sq_eq_inner_adjoint_left (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ ^ 2 = re ⟪(A† ∘L A) x, x⟫ := by
  have h : ⟪(A† ∘L A) x, x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_left]; rfl
  rw [h, ← inner_self_eq_norm_sq (𝕜 := 𝕜) _]

theorem apply_norm_eq_sqrt_inner_adjoint_left (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ = √(re ⟪(A† ∘L A) x, x⟫) := by
  rw [← apply_norm_sq_eq_inner_adjoint_left, Real.sqrt_sq (norm_nonneg _)]

theorem apply_norm_sq_eq_inner_adjoint_right (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ ^ 2 = re ⟪x, (A† ∘L A) x⟫ := by
  have h : ⟪x, (A† ∘L A) x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_right]; rfl
  rw [h, ← inner_self_eq_norm_sq (𝕜 := 𝕜) _]

theorem apply_norm_eq_sqrt_inner_adjoint_right (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ = √(re ⟪x, (A† ∘L A) x⟫) := by
  rw [← apply_norm_sq_eq_inner_adjoint_right, Real.sqrt_sq (norm_nonneg _)]

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
theorem eq_adjoint_iff (A : E →L[𝕜] F) (B : F →L[𝕜] E) : A = B† ↔ ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]

@[simp]
theorem _root_.LinearMap.IsSymmetric.clm_adjoint_eq {A : E →L[𝕜] E} (hA : A.IsSymmetric) :
    A† = A := by
  rwa [eq_comm, eq_adjoint_iff A A]

lemma adjoint_id : (.id 𝕜 E)† = .id 𝕜 E := by simp
lemma adjoint_one : (1 : E →L[𝕜] E)† = 1 := by simp

theorem _root_.Submodule.adjoint_subtypeL (U : Submodule 𝕜 E) [CompleteSpace U] :
    U.subtypeL† = U.orthogonalProjection := by
  symm
  simp [eq_adjoint_iff]

theorem _root_.Submodule.adjoint_orthogonalProjection (U : Submodule 𝕜 E) [CompleteSpace U] :
    (U.orthogonalProjection : E →L[𝕜] U)† = U.subtypeL := by
  rw [← U.adjoint_subtypeL, adjoint_adjoint]

theorem orthogonal_ker (T : E →L[𝕜] F) :
    T.kerᗮ = T†.range.topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply le_antisymm
  all_goals refine Submodule.orthogonal_le fun x hx ↦ ?_
  · refine ext_inner_left 𝕜 fun y ↦ ?_
    simp [← T.adjoint_inner_left, hx _]
  · rintro _ ⟨y, rfl⟩
    simp_all [T.adjoint_inner_left]

theorem orthogonal_range (T : E →L[𝕜] F) : T.rangeᗮ = T†.ker := by
  rw [← T†.ker.orthogonal_orthogonal, T†.orthogonal_ker]
  simp

omit [CompleteSpace E] in
theorem ker_le_ker_iff_range_le_range [FiniteDimensional 𝕜 E] {T U : E →L[𝕜] E}
    (hT : T.IsSymmetric) (hU : U.IsSymmetric) :
    U.ker ≤ T.ker ↔ T.range ≤ U.range := by
  refine ⟨fun h ↦ ?_, LinearMap.ker_le_ker_of_range hT hU⟩
  have := FiniteDimensional.complete 𝕜 E
  simpa [orthogonal_ker, hT, hU] using Submodule.orthogonal_le h

/-- Infinite-dimensional version of 7.64(b) in [axler2024]. -/
theorem ker_adjoint_comp_self (T : E →L[𝕜] F) : (T† ∘L T).ker = T.ker := by
  refine le_antisymm (fun _ _ ↦ ?_) fun _ _ ↦ by simp_all
  rw [LinearMap.mem_ker, ← inner_self_eq_zero (𝕜 := 𝕜), coe_coe, ← adjoint_inner_left]
  simp_all

theorem ker_self_comp_adjoint (T : E →L[𝕜] F) : (T ∘L T†).ker = T†.ker := by
  simpa using T†.ker_adjoint_comp_self

/--
This lemma uses the simp-normal form `⇑(T†) ∘ ⇑T` instead of `⇑(T† ∘L T)`
(note the difference between `∘` and `∘L`).
You may need to rewrite with `ContinuousLinearMap.coe_comp'` before applying this lemma.
-/
lemma adjoint_comp_self_injective_iff (T : E →L[𝕜] F) :
    Function.Injective (T† ∘ T) ↔ Function.Injective T := by
  rw [← coe_comp', ← coe_coe, ← LinearMap.ker_eq_bot, ← coe_coe, ← LinearMap.ker_eq_bot,
    ker_adjoint_comp_self]

/--
This lemma uses the simp-normal form `⇑T ∘ ⇑(T†)` instead of `⇑(T ∘L T†)`
(note the difference between `∘` and `∘L`).
You may need to rewrite with `ContinuousLinearMap.coe_comp'` before applying this lemma.
-/
lemma self_comp_adjoint_injective_iff (T : E →L[𝕜] F) :
    Function.Injective (T ∘ T†) ↔ Function.Injective (T†) := by
  simpa using T†.adjoint_comp_self_injective_iff

/-- `E →L[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : Star (E →L[𝕜] E) :=
  ⟨adjoint⟩

instance : InvolutiveStar (E →L[𝕜] E) :=
  ⟨adjoint_adjoint⟩

instance : StarMul (E →L[𝕜] E) :=
  ⟨adjoint_comp⟩

instance : StarRing (E →L[𝕜] E) :=
  ⟨map_add adjoint⟩

instance : StarModule 𝕜 (E →L[𝕜] E) :=
  ⟨map_smulₛₗ adjoint⟩

theorem star_eq_adjoint (A : E →L[𝕜] E) : star A = A† :=
  rfl

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
theorem isSelfAdjoint_iff' {A : E →L[𝕜] E} : IsSelfAdjoint A ↔ A† = A :=
  Iff.rfl

@[simp] lemma id_mem_unitary : .id 𝕜 E ∈ unitary (E →L[𝕜] E) := one_mem _

theorem norm_adjoint_comp_self (A : E →L[𝕜] F) :
    ‖A† ∘L A‖ = ‖A‖ * ‖A‖ := by
  refine le_antisymm ?_ ?_
  · calc
      ‖A† ∘L A‖ ≤ ‖A†‖ * ‖A‖ := opNorm_comp_le _ _
      _ = ‖A‖ * ‖A‖ := by rw [LinearIsometryEquiv.norm_map]
  · rw [← sq, ← Real.sqrt_le_sqrt_iff (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    refine opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have :=
      calc
        re ⟪(A† ∘L A) x, x⟫ ≤ ‖(A† ∘L A) x‖ * ‖x‖ := re_inner_le_norm _ _
        _ ≤ ‖A† ∘L A‖ * ‖x‖ * ‖x‖ := by gcongr; exact le_opNorm _ _
    calc
      ‖A x‖ = √(re ⟪(A† ∘L A) x, x⟫) := by rw [apply_norm_eq_sqrt_inner_adjoint_left]
      _ ≤ √(‖A† ∘L A‖ * ‖x‖ * ‖x‖) := Real.sqrt_le_sqrt this
      _ = √‖A† ∘L A‖ * ‖x‖ := by
        simp_rw [mul_assoc, Real.sqrt_mul (norm_nonneg _) (‖x‖ * ‖x‖),
          Real.sqrt_mul_self (norm_nonneg x)]

@[simp] theorem adjoint_comp_self_eq_zero_iff {A : E →L[𝕜] F} :
    adjoint A ∘L A = 0 ↔ A = 0 := by rw [← norm_eq_zero]; simp [norm_adjoint_comp_self]

/-- The C⋆-algebra instance when `𝕜 := ℂ` can be found in
`Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap.lean`. -/
instance : CStarRing (E →L[𝕜] E) where
  norm_mul_self_le x := le_of_eq <| Eq.symm <| norm_adjoint_comp_self x

theorem isAdjointPair_inner (A : E →L[𝕜] F) :
    LinearMap.IsAdjointPair (LinearMap.flip (innerₛₗ 𝕜 (E := E)))
      (innerₛₗ 𝕜 (E := F)).flip A (A†) := by
  intro x y
  simp [adjoint_inner_left]

theorem adjoint_innerSL_apply (x : E) :
    adjoint (innerSL 𝕜 x) = toSpanSingleton 𝕜 x :=
  ext_ring <| ext_inner_left 𝕜 <| fun _ => by simp [adjoint_inner_right]

theorem adjoint_toSpanSingleton (x : E) :
    adjoint (toSpanSingleton 𝕜 x) = innerSL 𝕜 x := by
  simp [← adjoint_innerSL_apply]

theorem innerSL_apply_comp (x : F) (f : E →L[𝕜] F) :
    innerSL 𝕜 x ∘L f = innerSL 𝕜 (adjoint f x) := by
  ext; simp [adjoint_inner_left]

omit [CompleteSpace E] in
theorem innerSL_apply_comp_of_isSymmetric (x : E) {f : E →L[𝕜] E} (hf : f.IsSymmetric) :
    innerSL 𝕜 x ∘L f = innerSL 𝕜 (f x) := by
  ext; simp [hf]

@[simp] lemma _root_.InnerProductSpace.adjoint_rankOne (x : E) (y : F) :
    adjoint (rankOne 𝕜 x y) = rankOne 𝕜 y x := by
  simp [rankOne_def', adjoint_comp, ← adjoint_innerSL_apply]

lemma _root_.InnerProductSpace.rankOne_comp {E G : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (x : E) (y : F) (f : G →L[𝕜] F) :
    rankOne 𝕜 x y ∘L f = rankOne 𝕜 x (adjoint f y) := by
  simp_rw [rankOne_def', comp_assoc, innerSL_apply_comp]

end ContinuousLinearMap

/-! ### Self-adjoint operators -/


namespace IsSelfAdjoint

open ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]

theorem adjoint_eq {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) : A.adjoint = A :=
  hA

/-- Every self-adjoint operator on an inner product space is symmetric. -/
theorem isSymmetric {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) : (A : E →ₗ[𝕜] E).IsSymmetric := by
  intro x y
  rw_mod_cast [← A.adjoint_inner_right, hA.adjoint_eq]

/-- Conjugating preserves self-adjointness. -/
theorem conj_adjoint {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (S : E →L[𝕜] F) :
    IsSelfAdjoint (S ∘L T ∘L S.adjoint) := by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

/-- Conjugating preserves self-adjointness. -/
theorem adjoint_conj {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (S : F →L[𝕜] E) :
    IsSelfAdjoint (S.adjoint ∘L T ∘L S) := by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

theorem _root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric {A : E →L[𝕜] E} :
    IsSelfAdjoint A ↔ (A : E →ₗ[𝕜] E).IsSymmetric :=
  ⟨fun hA => hA.isSymmetric, fun hA =>
    ext fun x => ext_inner_right 𝕜 fun y => (A.adjoint_inner_left y x).symm ▸ (hA x y).symm⟩

theorem _root_.LinearMap.IsSymmetric.isSelfAdjoint {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) : IsSelfAdjoint A := by
  rwa [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA

/-- The orthogonal projection is self-adjoint. -/
@[simp]
theorem _root_.isSelfAdjoint_starProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsSelfAdjoint U.starProjection :=
  U.starProjection_isSymmetric.isSelfAdjoint

theorem conj_starProjection {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsSelfAdjoint (U.starProjection ∘L T ∘L U.starProjection) := by
  rw [← mul_def, ← mul_def, ← mul_assoc]
  exact hT.conjugate_self <| isSelfAdjoint_starProjection U

end IsSelfAdjoint

namespace ContinuousLinearMap

variable {T : E →L[𝕜] E} [CompleteSpace E]

/-- An operator `T` is normal iff `‖T v‖ = ‖(adjoint T) v‖` for all `v`. -/
theorem isStarNormal_iff_norm_eq_adjoint :
    IsStarNormal T ↔ ∀ v : E, ‖T v‖ = ‖adjoint T v‖ := by
  rw [isStarNormal_iff, Commute, SemiconjBy, ← sub_eq_zero]
  simp_rw [ContinuousLinearMap.ext_iff, ← coe_coe, coe_sub, ← LinearMap.ext_iff, coe_zero]
  have := star_eq_adjoint T ▸ coe_sub (star _ * T) _ ▸
    ((IsSelfAdjoint.star_mul_self T).sub (IsSelfAdjoint.mul_star_self T)).isSymmetric
  simp_rw [star_eq_adjoint, ← LinearMap.IsSymmetric.inner_map_self_eq_zero this,
    LinearMap.sub_apply, inner_sub_left, coe_coe, mul_apply, adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, ← adjoint_inner_right T, inner_self_eq_norm_sq_to_K,
    sub_eq_zero, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  norm_cast

lemma IsStarNormal.adjoint_apply_eq_zero_iff (hT : IsStarNormal T) (x : E) :
    adjoint T x = 0 ↔ T x = 0 := by
  simp_rw [← norm_eq_zero (E := E), ← isStarNormal_iff_norm_eq_adjoint.mp hT]

open ContinuousLinearMap

theorem IsStarNormal.ker_adjoint_eq_ker (hT : IsStarNormal T) :
    (adjoint T).ker = T.ker :=
  Submodule.ext hT.adjoint_apply_eq_zero_iff

/-- The range of a normal operator is pairwise orthogonal to its kernel.

This is a weaker version of `LinearMap.IsSymmetric.orthogonal_range`
but with stronger type class assumptions (i.e., `CompleteSpace`). -/
theorem IsStarNormal.orthogonal_range (hT : IsStarNormal T) : T.rangeᗮ = T.ker :=
  T.orthogonal_range ▸ hT.ker_adjoint_eq_ker

/- TODO: As we have a more general result of this for elements in non-unital C⋆-algebras
(see `Mathlib/Analysis/CStarAlgebra/Projection.lean`), we will want to simplify the proof
by using the complexification of an inner product space over `𝕜`. -/
/-- An idempotent operator is self-adjoint iff it is normal. -/
theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal (hT : IsIdempotentElem T) :
    IsSelfAdjoint T ↔ IsStarNormal T := by
  refine ⟨fun h => by rw [isStarNormal_iff, h], fun h => ?_⟩
  suffices T = star T * T from this ▸ IsSelfAdjoint.star_mul_self _
  rw [← sub_eq_zero, ContinuousLinearMap.ext_iff]
  simp_rw [zero_apply, ← norm_eq_zero (E := E)]
  have :=
    calc (∀ x : E, ‖(T - star T * T) x‖ = 0) ↔ ∀ x, ‖(adjoint (1 - T)) (T x)‖ = 0 := by
          simp [star_eq_adjoint, one_def]
      _ ↔ ∀ x, ‖(1 - T) (T x)‖ = 0 := by
          simp only [isStarNormal_iff_norm_eq_adjoint.mp h.one_sub]
      _ ↔ ∀ x, ‖(T - T * T) x‖ = 0 := by simp
      _ ↔ T - T * T = 0 := by simp only [norm_eq_zero, ContinuousLinearMap.ext_iff, zero_apply]
      _ ↔ IsIdempotentElem T := by simp only [sub_eq_zero, IsIdempotentElem, eq_comm]
  exact this.mpr hT

/-- A continuous linear map is a star projection iff it is idempotent and normal. -/
theorem isStarProjection_iff_isIdempotentElem_and_isStarNormal :
    IsStarProjection T ↔ IsIdempotentElem T ∧ IsStarNormal T := by
  rw [isStarProjection_iff, and_congr_right_iff]
  exact fun h => IsIdempotentElem.isSelfAdjoint_iff_isStarNormal h

theorem isStarProjection_iff_isSymmetricProjection :
    IsStarProjection T ↔ T.IsSymmetricProjection := by
  simp [isStarProjection_iff, LinearMap.isSymmetricProjection_iff,
    isSelfAdjoint_iff_isSymmetric, IsIdempotentElem, End.mul_eq_comp, ← coe_comp, mul_def]

alias ⟨IsStarProjection.isSymmetricProjection, LinearMap.IsSymmetricProjection.isStarProjection⟩ :=
  isStarProjection_iff_isSymmetricProjection

/-- Star projection operators are equal iff their range are. -/
theorem IsStarProjection.ext_iff {S : E →L[𝕜] E}
    (hS : IsStarProjection S) (hT : IsStarProjection T) :
    S = T ↔ S.range = T.range := by
  simpa using hS.isSymmetricProjection.ext_iff hT.isSymmetricProjection

alias ⟨_, IsStarProjection.ext⟩ := IsStarProjection.ext_iff

theorem _root_.InnerProductSpace.isStarProjection_rankOne_self {x : E} (hx : ‖x‖ = 1) :
    IsStarProjection (rankOne 𝕜 x x) := (isSymmetricProjection_rankOne_self hx).isStarProjection

open Module End Submodule in
theorem orthogonal_mem_invtSubmodule {T : E →L[𝕜] E} {U : Submodule 𝕜 E}
    (h : U ∈ invtSubmodule T.adjoint.toLinearMap) :
    Uᗮ ∈ invtSubmodule T.toLinearMap := by
  simp only [mem_invtSubmodule_iff_forall_mem_of_mem, coe_coe, mem_orthogonal] at h ⊢
  grind [T.adjoint_inner_left]

open Module End in
theorem mem_invtSubmodule_adjoint_iff {T : E →L[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] :
    U ∈ invtSubmodule T.adjoint.toLinearMap ↔ Uᗮ ∈ invtSubmodule T.toLinearMap where
  mp := orthogonal_mem_invtSubmodule
  mpr := by simpa using orthogonal_mem_invtSubmodule (T := T.adjoint) (U := Uᗮ)

end ContinuousLinearMap

/-- `U.starProjection` is a star projection. -/
@[simp]
theorem isStarProjection_starProjection [CompleteSpace E] {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] : IsStarProjection U.starProjection :=
  ⟨U.isIdempotentElem_starProjection, isSelfAdjoint_starProjection U⟩

open ContinuousLinearMap in
/-- An operator is a star projection if and only if it is an orthogonal projection. -/
theorem isStarProjection_iff_eq_starProjection_range [CompleteSpace E] {p : E →L[𝕜] E} :
    IsStarProjection p ↔ ∃ (_ : p.range.HasOrthogonalProjection),
    p = p.range.starProjection := by
  simp_rw [p.isStarProjection_iff_isSymmetricProjection.eq,
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range, coe_inj]

lemma isStarProjection_iff_eq_starProjection [CompleteSpace E] {p : E →L[𝕜] E} :
    IsStarProjection p
      ↔ ∃ (K : Submodule 𝕜 E) (_ : K.HasOrthogonalProjection), p = K.starProjection :=
  ⟨fun h ↦ ⟨p.range, isStarProjection_iff_eq_starProjection_range.mp h⟩,
    by rintro ⟨_, _, rfl⟩; simp⟩

namespace LinearMap

variable [CompleteSpace E]
variable {T : E →ₗ[𝕜] E}

/-- The **Hellinger--Toeplitz theorem**: Construct a self-adjoint operator from an everywhere
  defined symmetric operator. -/
def IsSymmetric.toSelfAdjoint (hT : IsSymmetric T) : selfAdjoint (E →L[𝕜] E) :=
  ⟨⟨T, hT.continuous⟩, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT⟩

theorem IsSymmetric.coe_toSelfAdjoint (hT : IsSymmetric T) : (hT.toSelfAdjoint : E →ₗ[𝕜] E) = T :=
  rfl

theorem IsSymmetric.toSelfAdjoint_apply (hT : IsSymmetric T) {x : E} :
    (hT.toSelfAdjoint : E → E) x = T x :=
  rfl

end LinearMap

namespace LinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]

/-- The adjoint of an operator from the finite-dimensional inner product space `E` to the
finite-dimensional inner product space `F`. -/
def adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] F →ₗ[𝕜] E :=
  haveI := FiniteDimensional.complete 𝕜 E
  haveI := FiniteDimensional.complete 𝕜 F
  /- Note: Instead of the two instances above, the following works:
    ```
      haveI := FiniteDimensional.complete 𝕜
      haveI := FiniteDimensional.complete 𝕜
    ```
    But removing one of the `have`s makes it fail. The reason is that `E` and `F` don't live
    in the same universe, so the first `have` can no longer be used for `F` after its universe
    metavariable has been assigned to that of `E`!
  -/
  ((LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] F) ≃ₗ[𝕜] E →L[𝕜] F).trans
      ContinuousLinearMap.adjoint.toLinearEquiv).trans
    LinearMap.toContinuousLinearMap.symm

theorem adjoint_toContinuousLinearMap (A : E →ₗ[𝕜] F) :
    haveI := FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.adjoint.toContinuousLinearMap = A.toContinuousLinearMap.adjoint :=
  rfl

theorem adjoint_eq_toCLM_adjoint (A : E →ₗ[𝕜] F) :
    haveI := FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.adjoint = A.toContinuousLinearMap.adjoint :=
  rfl

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_left (A : E →ₗ[𝕜] F) (x : E) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫ := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A, adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left _ x y

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_right (A : E →ₗ[𝕜] F) (x : E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫ := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A, adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_right _ x y

/-- The adjoint is involutive. -/
@[simp]
theorem adjoint_adjoint (A : E →ₗ[𝕜] F) : A.adjoint.adjoint = A := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjoint_inner_right, adjoint_inner_left]

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
theorem adjoint_comp (A : F →ₗ[𝕜] G) (B : E →ₗ[𝕜] F) :
    (A ∘ₗ B).adjoint = B.adjoint ∘ₗ A.adjoint := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp only [adjoint_inner_right, LinearMap.coe_comp, Function.comp_apply]

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
theorem eq_adjoint_iff (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]

@[simp]
theorem IsSymmetric.adjoint_eq {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) :
    A.adjoint = A := by
  rwa [eq_comm, eq_adjoint_iff A A]

lemma adjoint_id : (.id : E →ₗ[𝕜] E).adjoint = .id := by simp
lemma adjoint_one : (1 : E →ₗ[𝕜] E).adjoint = 1 := by simp

/-- 7.6(b) from [axler2024].
See `ContinuousLinearMap.orthogonal_ker` for the infinite-dimensional version. -/
lemma orthogonal_ker (A : E →ₗ[𝕜] F) : A.kerᗮ = A.adjoint.range := by
  haveI := FiniteDimensional.complete 𝕜 E
  haveI := FiniteDimensional.complete 𝕜 F
  simpa using A.toContinuousLinearMap.orthogonal_ker

/-- 7.6(a) from [axler2024].
See `ContinuousLinearMap.orthogonal_range` for the infinite-dimensional version. -/
lemma orthogonal_range (A : E →ₗ[𝕜] F) : A.rangeᗮ = A.adjoint.ker := by
  haveI := FiniteDimensional.complete 𝕜 E
  haveI := FiniteDimensional.complete 𝕜 F
  simpa using A.toContinuousLinearMap.orthogonal_range

/-- 7.64(b) in [axler2024] -/
lemma ker_adjoint_comp_self (A : E →ₗ[𝕜] F) : (A.adjoint ∘ₗ A).ker = A.ker := by
  haveI := FiniteDimensional.complete 𝕜 E
  haveI := FiniteDimensional.complete 𝕜 F
  simpa using A.toContinuousLinearMap.ker_adjoint_comp_self

lemma ker_self_comp_adjoint (A : E →ₗ[𝕜] F) : (A ∘ₗ A.adjoint).ker = A.adjoint.ker := by
  simpa using A.adjoint.ker_adjoint_comp_self

/--
This lemma uses the simp-normal form `⇑(A.adjoint) ∘ ⇑A` instead of `⇑(A.adjoint ∘ₗ A)`
(note the difference between `∘` and `∘ₗ`).
You may need to rewrite with `LinearMap.coe_comp` before applying this lemma.
-/
lemma adjoint_comp_self_injective_iff (A : E →ₗ[𝕜] F) :
    Function.Injective (A.adjoint ∘ A) ↔ Function.Injective A := by
  rw [← coe_comp, ← ker_eq_bot, ← ker_eq_bot, ker_adjoint_comp_self]

/--
This lemma uses the simp-normal form `⇑A ∘ ⇑(A.adjoint)` instead of `⇑(A ∘ₗ A.adjoint)`
(note the difference between `∘` and `∘ₗ`).
You may need to rewrite with `LinearMap.coe_comp` before applying this lemma.
-/
lemma self_comp_adjoint_injective_iff (A : E →ₗ[𝕜] F) :
    Function.Injective (A ∘ A.adjoint) ↔ Function.Injective A.adjoint := by
  simpa using A.adjoint.adjoint_comp_self_injective_iff

/-- 7.64(c) in [axler2024]. -/
lemma range_adjoint_comp_self (A : E →ₗ[𝕜] F) : (A.adjoint ∘ₗ A).range = A.adjoint.range :=
  calc
    (A.adjoint ∘ₗ A).range = (A.adjoint ∘ₗ A).kerᗮ := by simp [orthogonal_ker]
    _ = A.adjoint.range := by rw [ker_adjoint_comp_self, orthogonal_ker]

lemma range_self_comp_adjoint (A : E →ₗ[𝕜] F) : (A ∘ₗ A.adjoint).range = A.range := by
  simpa using A.adjoint.range_adjoint_comp_self

/-- Part of 7.64(d) in [axler2024]. -/
theorem finrank_range_adjoint (A : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 A.adjoint.range = Module.finrank 𝕜 A.range := calc
  _ = Module.finrank 𝕜 F - Module.finrank 𝕜 A.adjoint.ker := by
    simp [← A.adjoint.finrank_range_add_finrank_ker]
  _ = _ := by rw [← A.adjoint.ker.finrank_add_finrank_orthogonal,
    orthogonal_ker, adjoint_adjoint]; simp

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all basis vectors `x` and `y`. -/
theorem eq_adjoint_iff_basis {ι₁ : Type*} {ι₂ : Type*} (b₁ : Basis ι₁ 𝕜 E) (b₂ : Basis ι₂ 𝕜 F)
    (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ (i₁ : ι₁) (i₂ : ι₂), ⟪A (b₁ i₁), b₂ i₂⟫ = ⟪b₁ i₁, B (b₂ i₂)⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  refine Basis.ext b₁ fun i₁ => ?_
  exact ext_inner_right_basis b₂ fun i₂ => by simp only [adjoint_inner_left, h i₁ i₂]

theorem eq_adjoint_iff_basis_left {ι : Type*} (b : Basis ι 𝕜 E) (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ i y, ⟪A (b i), y⟫ = ⟪b i, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => Basis.ext b fun i => ?_⟩
  exact ext_inner_right 𝕜 fun y => by simp only [h i, adjoint_inner_left]

theorem eq_adjoint_iff_basis_right {ι : Type*} (b : Basis ι 𝕜 F) (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ i x, ⟪A x, b i⟫ = ⟪x, B (b i)⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right_basis b fun i => by simp only [h i, adjoint_inner_left]

/-- `E →ₗ[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : Star (E →ₗ[𝕜] E) :=
  ⟨adjoint⟩

instance : InvolutiveStar (E →ₗ[𝕜] E) :=
  ⟨adjoint_adjoint⟩

instance : StarMul (E →ₗ[𝕜] E) :=
  ⟨adjoint_comp⟩

instance : StarRing (E →ₗ[𝕜] E) :=
  ⟨map_add adjoint⟩

instance : StarModule 𝕜 (E →ₗ[𝕜] E) :=
  ⟨map_smulₛₗ adjoint⟩

theorem star_eq_adjoint (A : E →ₗ[𝕜] E) : star A = A.adjoint :=
  rfl

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
theorem isSelfAdjoint_iff' {A : E →ₗ[𝕜] E} : IsSelfAdjoint A ↔ A.adjoint = A :=
  Iff.rfl

theorem isSymmetric_iff_isSelfAdjoint (A : E →ₗ[𝕜] E) : IsSymmetric A ↔ IsSelfAdjoint A := by
  rw [isSelfAdjoint_iff', IsSymmetric, ← LinearMap.eq_adjoint_iff]
  exact eq_comm

@[simp] lemma id_mem_unitary : .id ∈ unitary (E →ₗ[𝕜] E) := one_mem _

theorem isAdjointPair_inner (A : E →ₗ[𝕜] F) :
    IsAdjointPair (innerₛₗ 𝕜 (E := E)).flip
      (innerₛₗ 𝕜 (E := F)).flip A A.adjoint := by
  intro x y
  simp [adjoint_inner_left]

/- This next batch of lemmas is based on theorems like `LinearMap.IsPositive.conj_adjoint`, which
are in a downstream file but historically existed before these lemmas. We can't put them in the file
where `LinearMap.IsSymmetric` is defined because they depend on the adjoint. -/

@[aesop safe apply]
theorem IsSymmetric.conj_adjoint {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (S : E →ₗ[𝕜] F) :
    (S ∘ₗ T ∘ₗ S.adjoint).IsSymmetric := fun _ _ ↦ by simp [← adjoint_inner_right, hT]

theorem isSymmetric_self_comp_adjoint (T : E →ₗ[𝕜] F) : (T ∘ₗ adjoint T).IsSymmetric := by
  simpa using LinearMap.IsSymmetric.id.conj_adjoint T

@[aesop safe apply]
theorem IsSymmetric.adjoint_conj {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (S : F →ₗ[𝕜] E) :
    (S.adjoint ∘ₗ T ∘ₗ S).IsSymmetric := by
  simpa using hT.conj_adjoint S.adjoint

/-- Like `LinearMap.isSymmetric_adjoint_mul_self` but domain and range can be different -/
theorem isSymmetric_adjoint_comp_self (T : E →ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric := by
  simpa using LinearMap.IsSymmetric.id.adjoint_conj T

/-- The Gram operator T†T is symmetric. See `LinearMap.isSymmetric_adjoint_comp_self` for a version
where the domain and codomain are distinct. -/
theorem isSymmetric_adjoint_mul_self (T : E →ₗ[𝕜] E) : IsSymmetric (T.adjoint * T) := by
  intro x y
  simp [adjoint_inner_left, adjoint_inner_right]

/-- The Gram operator T†T is a positive operator. -/
theorem re_inner_adjoint_mul_self_nonneg (T : E →ₗ[𝕜] E) (x : E) :
    0 ≤ re ⟪x, (T.adjoint * T) x⟫ := by
  simp only [Module.End.mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact sq_nonneg _

@[simp]
theorem im_inner_adjoint_mul_self_eq_zero (T : E →ₗ[𝕜] E) (x : E) :
    im ⟪x, T.adjoint (T x)⟫ = 0 := by
  simp only [adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem isSelfAdjoint_toContinuousLinearMap_iff (T : E →ₗ[𝕜] E) :
    have := FiniteDimensional.complete 𝕜 E
    IsSelfAdjoint T.toContinuousLinearMap ↔ IsSelfAdjoint T := by
  simp [IsSelfAdjoint, star, adjoint,
    ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap]

theorem _root_.ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff (T : E →L[𝕜] E) :
    have := FiniteDimensional.complete 𝕜 E
    IsSelfAdjoint T.toLinearMap ↔ IsSelfAdjoint T := by
  simp only [IsSelfAdjoint, star, adjoint, LinearEquiv.trans_apply,
    coe_toContinuousLinearMap_symm,
    ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap]
  rfl

theorem isStarProjection_toContinuousLinearMap_iff {T : E →ₗ[𝕜] E} :
    have := FiniteDimensional.complete 𝕜 E
    IsStarProjection (toContinuousLinearMap T) ↔ IsStarProjection T := by
  simp [isStarProjection_iff, isSelfAdjoint_toContinuousLinearMap_iff,
    ← ContinuousLinearMap.isIdempotentElem_toLinearMap_iff]

theorem isStarProjection_iff_isSymmetricProjection {T : E →ₗ[𝕜] E} :
    IsStarProjection T ↔ T.IsSymmetricProjection := by
  simp [← isStarProjection_toContinuousLinearMap_iff,
    ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]

open LinearMap in
/-- Star projection operators are equal iff their range are. -/
theorem IsStarProjection.ext_iff {S T : E →ₗ[𝕜] E}
    (hS : IsStarProjection S) (hT : IsStarProjection T) :
    S = T ↔ LinearMap.range S = LinearMap.range T := by
  have := FiniteDimensional.complete 𝕜 E
  simpa using ContinuousLinearMap.IsStarProjection.ext_iff
    (S.isStarProjection_toContinuousLinearMap_iff.mpr hS)
    (T.isStarProjection_toContinuousLinearMap_iff.mpr hT)

alias ⟨_, IsStarProjection.ext⟩ := IsStarProjection.ext_iff

theorem adjoint_innerₛₗ_apply (x : E) :
    adjoint (innerₛₗ 𝕜 x) = toSpanSingleton 𝕜 E x :=
  have := FiniteDimensional.complete 𝕜 E
  ext fun _ ↦ congr($(ContinuousLinearMap.adjoint_innerSL_apply x) _)

theorem adjoint_toSpanSingleton (x : E) :
    adjoint (toSpanSingleton 𝕜 E x) = innerₛₗ 𝕜 x := by
  simp [← adjoint_innerₛₗ_apply]

open Module End in
/-- The linear map version of `ContinuousLinearMap.mem_invtSubmodule_adjoint_iff`
in a finite-dimensional space. -/
theorem _root_.Module.End.mem_invtSubmodule_adjoint_iff {T : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} :
    U ∈ invtSubmodule T.adjoint ↔ Uᗮ ∈ invtSubmodule T :=
  have := FiniteDimensional.complete 𝕜 E
  ContinuousLinearMap.mem_invtSubmodule_adjoint_iff

end LinearMap

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

section linearIsometryEquiv
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

namespace ContinuousLinearMap

theorem inner_map_map_iff_adjoint_comp_self (u : H →L[𝕜] K) :
    (∀ x y : H, ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜) ↔ adjoint u ∘L u = 1 := by
  refine ⟨fun h ↦ ext fun x ↦ ?_, fun h ↦ ?_⟩
  · refine ext_inner_right 𝕜 fun y ↦ ?_
    simpa [star_eq_adjoint, adjoint_inner_left] using h x y
  · simp [← adjoint_inner_left, ← comp_apply, h]

theorem norm_map_iff_adjoint_comp_self (u : H →L[𝕜] K) :
    (∀ x : H, ‖u x‖ = ‖x‖) ↔ adjoint u ∘L u = 1 := by
  rw [LinearMap.norm_map_iff_inner_map_map u, u.inner_map_map_iff_adjoint_comp_self]

theorem isometry_iff_adjoint_comp_self (u : H →L[𝕜] K) :
    Isometry u ↔ adjoint u ∘L u = 1 := by
  rw [AddMonoidHomClass.isometry_iff_norm, norm_map_iff_adjoint_comp_self]

@[simp]
lemma _root_.LinearIsometryEquiv.adjoint_eq_symm (e : H ≃ₗᵢ[𝕜] K) :
    adjoint (e : H →L[𝕜] K) = e.symm :=
  calc
    _ = adjoint (e : H →L[𝕜] K) ∘L e ∘L (e.symm : K →L[𝕜] H) := by simp
    _ = e.symm := by
      rw [← comp_assoc, norm_map_iff_adjoint_comp_self _ |>.mp e.norm_map, one_def, id_comp]

omit [CompleteSpace H] [CompleteSpace K] in
theorem _root_.LinearIsometryEquiv.adjoint_toLinearMap_eq_symm
    [FiniteDimensional 𝕜 H] [FiniteDimensional 𝕜 K] (e : H ≃ₗᵢ[𝕜] K) :
    LinearMap.adjoint e.toLinearMap = e.symm.toLinearMap :=
  have := FiniteDimensional.complete 𝕜 H
  have := FiniteDimensional.complete 𝕜 K
  congr($e.adjoint_eq_symm)

@[simp]
lemma _root_.LinearIsometryEquiv.star_eq_symm (e : H ≃ₗᵢ[𝕜] H) :
    star (e : H →L[𝕜] H) = e.symm :=
  e.adjoint_eq_symm

theorem norm_map_of_mem_unitary {u : H →L[𝕜] H} (hu : u ∈ unitary (H →L[𝕜] H)) (x : H) :
    ‖u x‖ = ‖x‖ :=
  -- Elaborates faster with this broken out https://github.com/leanprover-community/mathlib4/issues/11299
  have := Unitary.star_mul_self_of_mem hu
  u.norm_map_iff_adjoint_comp_self.mpr this x

theorem inner_map_map_of_mem_unitary {u : H →L[𝕜] H} (hu : u ∈ unitary (H →L[𝕜] H)) (x y : H) :
    ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  -- Elaborates faster with this broken out https://github.com/leanprover-community/mathlib4/issues/11299
  have := Unitary.star_mul_self_of_mem hu
  u.inner_map_map_iff_adjoint_comp_self.mpr this x y

end ContinuousLinearMap

namespace LinearIsometryEquiv

open ContinuousLinearMap ContinuousLinearEquiv in
/-- An isometric linear equivalence of two Hilbert spaces induces an equivalence of
⋆-algebras of their endomorphisms.

When `H = K`, this is exactly `Unitary.conjStarAlgAut`
(see `Unitary.conjStarAlgEquiv_unitaryLinearIsometryEquiv` and
`Unitary.conjStarAlgAut_symm_unitaryLinearIsometryEquiv`). -/
def conjStarAlgEquiv (e : H ≃ₗᵢ[𝕜] K) : (H →L[𝕜] H) ≃⋆ₐ[𝕜] (K →L[𝕜] K) :=
  .ofAlgEquiv e.toContinuousLinearEquiv.conjContinuousAlgEquiv fun x ↦ by
    simp [star_eq_adjoint, conjContinuousAlgEquiv_apply, ← toContinuousLinearEquiv_symm, comp_assoc]

@[simp] lemma conjStarAlgEquiv_apply_apply (e : H ≃ₗᵢ[𝕜] K) (x : H →L[𝕜] H) (y : K) :
    e.conjStarAlgEquiv x y = e (x (e.symm y)) := rfl

theorem symm_conjStarAlgEquiv_apply_apply (e : H ≃ₗᵢ[𝕜] K) (f : K →L[𝕜] K) (x : H) :
    e.conjStarAlgEquiv.symm f x = e.symm (f (e x)) := rfl

lemma conjStarAlgEquiv_apply (e : H ≃ₗᵢ[𝕜] K) (x : H →L[𝕜] H) :
    e.conjStarAlgEquiv x = e ∘L x ∘L e.symm := rfl

@[simp] lemma symm_conjStarAlgEquiv (e : H ≃ₗᵢ[𝕜] K) :
    e.conjStarAlgEquiv.symm = e.symm.conjStarAlgEquiv := rfl

@[simp] theorem conjStarAlgEquiv_refl : conjStarAlgEquiv (.refl 𝕜 H) = .refl := rfl

theorem conjStarAlgEquiv_trans {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [CompleteSpace G] (e : H ≃ₗᵢ[𝕜] K) (f : K ≃ₗᵢ[𝕜] G) :
    (e.trans f).conjStarAlgEquiv = e.conjStarAlgEquiv.trans f.conjStarAlgEquiv := rfl

open ContinuousLinearEquiv ContinuousLinearMap in
theorem conjStarAlgEquiv_ext_iff (f g : H ≃ₗᵢ[𝕜] K) :
    f.conjStarAlgEquiv = g.conjStarAlgEquiv ↔ ∃ α : unitary 𝕜, f = α • g := by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, LinearIsometryEquiv.ext_iff, conjStarAlgEquiv_apply,
    ← eq_toContinuousLinearMap_symm_comp, ← comp_assoc, toContinuousLinearEquiv_symm,
    eq_comp_toContinuousLinearMap_symm,
    comp_assoc, ← comp_assoc _ (f : H →L[𝕜] K), comp_coe, ← ContinuousLinearMap.mul_def,
    ← Subalgebra.mem_center_iff (R := 𝕜), Algebra.IsCentral.center_eq_bot, ← comp_coe,
    Algebra.mem_bot, Set.mem_range, Algebra.algebraMap_eq_smul_one]
  refine ⟨fun ⟨y, h⟩ ↦ ?_, fun ⟨y, h⟩ ↦ ⟨(y : 𝕜), by ext; simp [h]⟩⟩
  by_cases! hy : y = 0
  · exact ⟨1, fun x ↦ by simp [by simpa [hy] using congr($h x).symm]⟩
  have hfg : (f : H →L[𝕜] K) = y • g := by ext; simpa using congr(g ($h _)).symm
  have hgf : (g : H →L[𝕜] K) = star y • f := by
    ext x
    have := by simpa [map_smulₛₗ, ← ContinuousLinearEquiv.comp_coe, ← toContinuousLinearEquiv_symm,
      ← adjoint_eq_symm, ContinuousLinearMap.one_def] using congr(f (adjoint $h x)).symm
    simpa
  have : (g : H →L[𝕜] K) = (starRingEnd 𝕜 y * y) • g := by
    simp [← smul_smul, ← hfg, ← star_def, ← hgf]
  nth_rw 1 [← one_smul 𝕜 (g : H →L[𝕜] K)] at this
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero, eq_comm] at this
  obtain (this | this) := this
  · exact ⟨⟨y, by simp [Unitary.mem_iff, this, mul_comm y]⟩, fun x ↦ congr($hfg x)⟩
  · exact ⟨1, fun x ↦ by simp [by simpa using congr($this x)]⟩

end LinearIsometryEquiv
end linearIsometryEquiv

namespace Unitary

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
  map_mul' u v := by ext; rfl

@[simp]
lemma coe_linearIsometryEquiv_apply (u : unitary (H →L[𝕜] H)) :
    linearIsometryEquiv u = (u : H →L[𝕜] H) :=
  rfl

@[deprecated (since := "2025-12-16")] alias linearIsometryEquiv_coe_apply :=
  coe_linearIsometryEquiv_apply

@[simp]
lemma coe_symm_linearIsometryEquiv_apply (e : H ≃ₗᵢ[𝕜] H) :
    linearIsometryEquiv.symm e = (e : H →L[𝕜] H) :=
  rfl

@[deprecated (since := "2025-12-16")] alias linearIsometryEquiv_coe_symm_apply :=
  coe_symm_linearIsometryEquiv_apply

theorem conjStarAlgEquiv_unitaryLinearIsometryEquiv (u : unitary (H →L[𝕜] H)) :
    (linearIsometryEquiv u).conjStarAlgEquiv = conjStarAlgAut 𝕜 _ u := rfl

theorem conjStarAlgAut_symm_unitaryLinearIsometryEquiv (u : H ≃ₗᵢ[𝕜] H) :
    conjStarAlgAut 𝕜 (H →L[𝕜] H) (linearIsometryEquiv.symm u) = u.conjStarAlgEquiv := by
  simp [← conjStarAlgEquiv_unitaryLinearIsometryEquiv]

end Unitary

namespace unitary

@[deprecated (since := "2025-10-29")] alias norm_map := Unitary.norm_map
@[deprecated (since := "2025-10-29")] alias inner_map_map := Unitary.inner_map_map
@[deprecated (since := "2025-10-29")] alias linearIsometryEquiv := Unitary.linearIsometryEquiv
@[deprecated (since := "2025-10-29")] alias linearIsometryEquiv_coe_apply :=
  Unitary.linearIsometryEquiv_coe_apply
@[deprecated (since := "2025-10-29")] alias linearIsometryEquiv_coe_symm_apply :=
  Unitary.linearIsometryEquiv_coe_symm_apply

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
is the conjugate transpose of the matrix associated to the linear map. -/
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

lemma LinearMap.toMatrixOrthonormal_apply_apply (f : E →ₗ[𝕜] E) (i j : n) :
    toMatrixOrthonormal v₁ f i j = ⟪v₁ i, f (v₁ j)⟫_𝕜 :=
  calc
    _ = v₁.repr (f (v₁ j)) i := f.toMatrix_apply ..
    _ = ⟪v₁ i, f (v₁ j)⟫_𝕜 := v₁.repr_apply_apply ..

lemma LinearMap.toMatrixOrthonormal_reindex (e : n ≃ m) (f : E →ₗ[𝕜] E) :
    toMatrixOrthonormal (v₁.reindex e) f = (toMatrixOrthonormal v₁ f).reindex e e :=
  Matrix.ext fun i j =>
    calc toMatrixOrthonormal (v₁.reindex e) f i j
      _ = (v₁.reindex e).repr (f (v₁.reindex e j)) i := f.toMatrix_apply ..
      _ = v₁.repr (f (v₁ (e.symm j))) (e.symm i) := by simp
      _ = toMatrixOrthonormal v₁ f (e.symm i) (e.symm j) := Eq.symm (f.toMatrix_apply ..)

open scoped ComplexConjugate

/-- The adjoint of the linear map associated to a matrix is the linear map associated to the
conjugate transpose of that matrix. -/
theorem Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A : Matrix m n 𝕜) :
    A.conjTranspose.toEuclideanLin = A.toEuclideanLin.adjoint :=
  A.toLin_conjTranspose (EuclideanSpace.basisFun n 𝕜) (EuclideanSpace.basisFun m 𝕜)

end Matrix

@[simp]
theorem LinearIsometry.adjoint_comp_self {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E'] (f : E →ₗᵢ[𝕜] E') :
    f.toContinuousLinearMap.adjoint ∘L f.toContinuousLinearMap = 1 :=
  f.toContinuousLinearMap.isometry_iff_adjoint_comp_self.mp f.isometry

/-- A version of `LinearIsometry.adjoint_comp_self` in terms of `LinearMap.adjoint`. -/
@[simp]
theorem LinearIsometry.adjoint_comp_self' {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E'] (f : E →ₗᵢ[𝕜] E') :
    f.adjoint ∘ₗ f.toLinearMap = LinearMap.id := by
  haveI := FiniteDimensional.complete 𝕜 E
  haveI := FiniteDimensional.complete 𝕜 E'
  ext x
  exact congr($(f.adjoint_comp_self) x)

theorem LinearIsometryEquiv.toMatrix_mem_unitaryGroup {ι E E' : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    (f : E ≃ₗᵢ[𝕜] E') (b : OrthonormalBasis ι 𝕜 E) (b' : OrthonormalBasis ι 𝕜 E') :
    f.toMatrix b.toBasis b'.toBasis ∈ Matrix.unitaryGroup ι 𝕜 := by
  have : FiniteDimensional 𝕜 E := Module.Basis.finiteDimensional_of_finite b.toBasis
  have : FiniteDimensional 𝕜 E' := Module.Basis.finiteDimensional_of_finite b'.toBasis
  simp [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← LinearMap.toMatrix_adjoint,
    ← LinearMap.toMatrix_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm,
    -OrthonormalBasis.coe_toBasis]

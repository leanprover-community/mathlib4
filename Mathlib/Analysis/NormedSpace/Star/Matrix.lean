/-
Copyright (c) 2022 Hans Parshall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hans Parshall
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.IsROrC.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.UniformSpace.Matrix

#align_import analysis.normed_space.star.matrix from "leanprover-community/mathlib"@"468b141b14016d54b479eb7a0fff1e360b7e3cf6"

/-!
# Analytic properties of the `star` operation on matrices

## Main definitions

* `Matrix.instNormedRingL2Op`: the (necessarily unique) normed ring structure on `Matrix n n 𝕜`
  which ensure it is a `CstarRing` in `Matrix.instCstarRing`. This is a scoped instance in the
  namespace `Matrix.L2OpNorm` in order to avoid choosing a global norm for `Matrix`.

## Main statements

* `entry_norm_bound_of_unitary`: the entries of a unitary matrix are uniformly boundd by `1`.

## Implementation details

We take care to ensure the topology and uniformity induced by `Matrix.instMetricSpaceL2Op`
coincide with the existing topology and uniformity on matrices.

-/


open scoped BigOperators Matrix

variable {𝕜 m n E : Type*}

section EntrywiseSupNorm

variable [IsROrC 𝕜] [Fintype n] [DecidableEq n]

theorem entry_norm_bound_of_unitary {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (i j : n) : ‖U i j‖ ≤ 1 := by
  -- The norm squared of an entry is at most the L2 norm of its row.
  have norm_sum : ‖U i j‖ ^ 2 ≤ ∑ x, ‖U i x‖ ^ 2 := by
    apply Multiset.single_le_sum
    · intro x h_x
      rw [Multiset.mem_map] at h_x
      cases' h_x with a h_a
      rw [← h_a.2]
      apply sq_nonneg
    · rw [Multiset.mem_map]
      use j
      simp only [eq_self_iff_true, Finset.mem_univ_val, and_self_iff, sq_eq_sq]
  -- The L2 norm of a row is a diagonal entry of U * Uᴴ
  have diag_eq_norm_sum : (U * Uᴴ) i i = (∑ x : n, ‖U i x‖ ^ 2 : ℝ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply, IsROrC.mul_conj,
      IsROrC.normSq_eq_def', IsROrC.ofReal_pow]; norm_cast
  -- The L2 norm of a row is a diagonal entry of U * Uᴴ, real part
  have re_diag_eq_norm_sum : IsROrC.re ((U * Uᴴ) i i) = ∑ x : n, ‖U i x‖ ^ 2 := by
    rw [IsROrC.ext_iff] at diag_eq_norm_sum
    rw [diag_eq_norm_sum.1]
    norm_cast
  -- Since U is unitary, the diagonal entries of U * Uᴴ are all 1
  have mul_eq_one : U * Uᴴ = 1 := unitary.mul_star_self_of_mem hU
  have diag_eq_one : IsROrC.re ((U * Uᴴ) i i) = 1 := by
    simp only [mul_eq_one, eq_self_iff_true, Matrix.one_apply_eq, IsROrC.one_re]
  -- Putting it all together
  rw [← sq_le_one_iff (norm_nonneg (U i j)), ← diag_eq_one, re_diag_eq_norm_sum]
  exact norm_sum
#align entry_norm_bound_of_unitary entry_norm_bound_of_unitary

attribute [local instance] Matrix.normedAddCommGroup

/-- The entrywise sup norm of a unitary matrix is at most 1. -/
theorem entrywise_sup_norm_bound_of_unitary {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    ‖U‖ ≤ 1 := by
  conv => -- Porting note: was `simp_rw [pi_norm_le_iff_of_nonneg zero_le_one]`
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intros
  exact entry_norm_bound_of_unitary hU _ _
#align entrywise_sup_norm_bound_of_unitary entrywise_sup_norm_bound_of_unitary

end EntrywiseSupNorm

noncomputable section L2OpNorm

namespace Matrix
open LinearMap

variable [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [IsROrC 𝕜]

/-- The natural star algebra equivalence between matrices and continuous linear endomoporphisms
of Euclidean space induced by the orthonormal basis `EuclideanSpace.basisFun`. -/
def toEuclideanClm :
    Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) :=
  toMatrixOrthonormal (EuclideanSpace.basisFun n 𝕜) |>.symm.trans <|
    { toContinuousLinearMap with
      map_mul' := fun _ _ ↦ rfl
      map_star' := adjoint_toContinuousLinearMap }

@[simp]
theorem toEuclideanClm_piLp_equiv_symm (A : Matrix n n 𝕜) (x : n → 𝕜) :
    toEuclideanClm (n := n) (𝕜 := 𝕜) A ((WithLp.equiv _ _).symm x) =
      (WithLp.equiv _ _).symm (toLin' A x) :=
  rfl

@[simp]
theorem piLp_equiv_toEuclideanClm (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    WithLp.equiv _ _ (toEuclideanClm (n := n) (𝕜 := 𝕜) A x) =
      toLin' A (WithLp.equiv _ _ x) :=
  rfl

/-- An auxiliary definition used only to construct the true `NormedAddCommGroup` (and `Metric`)
structure provided by `Matrix.instMetricSpaceL2Op` and `Matrix.instNormedAddCommGroupL2Op`.  -/
def normedAddCommGroupAuxL2Op : NormedAddCommGroup (Matrix m n 𝕜) :=
  @NormedAddCommGroup.induced ((Matrix m n 𝕜) ≃ₗ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m))
    _ _ _ ContinuousLinearMap.toNormedAddCommGroup.toNormedAddGroup _ _ <|
    (toEuclideanLin.trans toContinuousLinearMap).injective

/-- An auxiliary definition used only to construct the true `NormedRing` (and `Metric`) structure
provided by `Matrix.instMetricSpaceL2Op` and `Matrix.instNormedRingL2Op`.  -/
def normedRingAuxL2Op : NormedRing (Matrix n n 𝕜) :=
  @NormedRing.induced ((Matrix n n 𝕜) ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n))
    _ _ _ ContinuousLinearMap.toNormedRing _ _ toEuclideanClm.injective

open Bornology Filter
open scoped Topology Uniformity

/-- The metric on `Matrix m n 𝕜` arising from the operator norm given by the identification with
(continuous) linear maps of `EuclideanSpace`. -/
def instMetricSpaceL2Op : MetricSpace (Matrix m n 𝕜) := by
  /- We first replace the topology so that we can automatically replace the uniformity using
  `UniformAddGroup.toUniformSpace_eq`. -/
  letI normed_add_comm_group : NormedAddCommGroup (Matrix m n 𝕜) :=
    { normedAddCommGroupAuxL2Op.replaceTopology <|
        (toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap
        |>.toContinuousLinearEquiv.toHomeomorph.inducing.induced with
      norm := normedAddCommGroupAuxL2Op.norm
      dist_eq := normedAddCommGroupAuxL2Op.dist_eq }
  exact normed_add_comm_group.replaceUniformity <| by
    congr
    rw [← @UniformAddGroup.toUniformSpace_eq _ (instUniformSpaceMatrix m n 𝕜) _ _]
    rw [@UniformAddGroup.toUniformSpace_eq _ PseudoEMetricSpace.toUniformSpace _ _]

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instMetricSpaceL2Op

open scoped Matrix.L2OpNorm

/-- The norm structure on `Matrix m n 𝕜` arising from the operator norm given by the identification
with (continuous) linear maps of `EuclideanSpace`. -/
def instNormedAddCommGroupL2Op : NormedAddCommGroup (Matrix m n 𝕜) where
  norm := normedAddCommGroupAuxL2Op.norm
  dist_eq := normedAddCommGroupAuxL2Op.dist_eq

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instNormedAddCommGroupL2Op

lemma op_norm_def (x : Matrix m n 𝕜) :
    ‖x‖ = ‖(toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap x‖ := rfl

/-- The normed algebra structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endmorphisms of `EuclideanSpace 𝕜 n`. -/
def instNormedSpaceL2Op : NormedSpace 𝕜 (Matrix m n 𝕜) where
  norm_smul_le r x := by
    rw [op_norm_def, LinearEquiv.map_smul]
    exact norm_smul_le r ((toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap x)

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instNormedSpaceL2Op

/-- The normed ring structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endmorphisms of `EuclideanSpace 𝕜 n`. -/
def instNormedRingL2Op : NormedRing (Matrix n n 𝕜) where
  dist_eq := normedRingAuxL2Op.dist_eq
  norm_mul := normedRingAuxL2Op.norm_mul

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instNormedRingL2Op

lemma cstar_norm_def (x : Matrix n n 𝕜) : ‖x‖ = ‖toEuclideanClm (n := n) (𝕜 := 𝕜) x‖ := rfl

/-- The normed algebra structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endmorphisms of `EuclideanSpace 𝕜 n`. -/
def instNormedAlgebraL2Op : NormedAlgebra 𝕜 (Matrix n n 𝕜) where
  norm_smul_le := norm_smul_le

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instNormedAlgebraL2Op

/-- The operator norm on `Matrix n n 𝕜` given by the identification with (continuous) linear
endmorphisms of `EuclideanSpace 𝕜 n` makes it into a `L2OpRing`. -/
lemma instCstarRing : CstarRing (Matrix n n 𝕜) where
  norm_star_mul_self {x} := by
    simp only [cstar_norm_def, _root_.map_mul, map_star,
      CstarRing.norm_star_mul_self (x := toEuclideanClm (n := n) (𝕜 := 𝕜) x)]

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instCstarRing

end Matrix

end L2OpNorm

/-
Copyright (c) 2022 Hans Parshall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hans Parshall
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.UniformSpace.Matrix

/-!
# Analytic properties of the `star` operation on matrices

This transports the operator norm on `EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m` to
`Matrix m n 𝕜`. See the file `Analysis.Matrix` for many other matrix norms.

## Main definitions

* `Matrix.instNormedRingL2Op`: the (necessarily unique) normed ring structure on `Matrix n n 𝕜`
  which ensure it is a `CStarRing` in `Matrix.instCStarRing`. This is a scoped instance in the
  namespace `Matrix.L2OpNorm` in order to avoid choosing a global norm for `Matrix`.

## Main statements

* `entry_norm_bound_of_unitary`: the entries of a unitary matrix are uniformly bound by `1`.

## Implementation details

We take care to ensure the topology and uniformity induced by `Matrix.instMetricSpaceL2Op`
coincide with the existing topology and uniformity on matrices.

## TODO

* Show that `‖diagonal (v : n → 𝕜)‖ = ‖v‖`.

-/

open WithLp
open scoped Matrix

variable {𝕜 m n l E : Type*}

section EntrywiseSupNorm

variable [RCLike 𝕜] [Fintype n] [DecidableEq n]

theorem entry_norm_bound_of_unitary {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (i j : n) : ‖U i j‖ ≤ 1 := by
  -- The norm squared of an entry is at most the L2 norm of its row.
  have norm_sum : ‖U i j‖ ^ 2 ≤ ∑ x, ‖U i x‖ ^ 2 := by
    apply Multiset.single_le_sum
    · intro x h_x
      rw [Multiset.mem_map] at h_x
      obtain ⟨a, h_a⟩ := h_x
      rw [← h_a.2]
      apply sq_nonneg
    · rw [Multiset.mem_map]
      use j
      simp only [eq_self_iff_true, Finset.mem_univ_val, and_self_iff, sq_eq_sq₀]
  -- The L2 norm of a row is a diagonal entry of U * Uᴴ
  have diag_eq_norm_sum : (U * Uᴴ) i i = (∑ x : n, ‖U i x‖ ^ 2 : ℝ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply, RCLike.mul_conj,
      RCLike.normSq_eq_def', RCLike.ofReal_pow]; norm_cast
  -- The L2 norm of a row is a diagonal entry of U * Uᴴ, real part
  have re_diag_eq_norm_sum : RCLike.re ((U * Uᴴ) i i) = ∑ x : n, ‖U i x‖ ^ 2 := by
    rw [RCLike.ext_iff] at diag_eq_norm_sum
    rw [diag_eq_norm_sum.1]
    norm_cast
  -- Since U is unitary, the diagonal entries of U * Uᴴ are all 1
  have mul_eq_one : U * Uᴴ = 1 := unitary.mul_star_self_of_mem hU
  have diag_eq_one : RCLike.re ((U * Uᴴ) i i) = 1 := by
    simp only [mul_eq_one, eq_self_iff_true, Matrix.one_apply_eq, RCLike.one_re]
  -- Putting it all together
  rw [← sq_le_one_iff₀ (norm_nonneg (U i j)), ← diag_eq_one, re_diag_eq_norm_sum]
  exact norm_sum

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

end EntrywiseSupNorm

noncomputable section L2OpNorm

namespace Matrix
open LinearMap

variable [RCLike 𝕜]
variable [Fintype m] [Fintype n] [DecidableEq n] [Fintype l] [DecidableEq l]

/-- The natural star algebra equivalence between matrices and continuous linear endomoporphisms
of Euclidean space induced by the orthonormal basis `EuclideanSpace.basisFun`.

This is a more-bundled version of `Matrix.toEuclideanLin`, for the special case of square matrices,
followed by a more-bundled version of `LinearMap.toContinuousLinearMap`. -/
def toEuclideanCLM :
    Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) :=
  toMatrixOrthonormal (EuclideanSpace.basisFun n 𝕜) |>.symm.trans <|
    { toContinuousLinearMap with
      map_mul' := fun _ _ ↦ rfl
      map_star' := adjoint_toContinuousLinearMap }

lemma coe_toEuclideanCLM_eq_toEuclideanLin (A : Matrix n n 𝕜) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) A : _ →ₗ[𝕜] _) = toEuclideanLin A :=
  rfl

@[simp]
lemma toEuclideanCLM_piLp_equiv_symm (A : Matrix n n 𝕜) (x : n → 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) A (toLp _ x) = toLp _ (toLin' A x) := rfl

@[simp]
lemma piLp_equiv_toEuclideanCLM (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ofLp (toEuclideanCLM (n := n) (𝕜 := 𝕜) A x) = toLin' A (ofLp x) := rfl

/-- An auxiliary definition used only to construct the true `NormedAddCommGroup` (and `Metric`)
structure provided by `Matrix.instMetricSpaceL2Op` and `Matrix.instNormedAddCommGroupL2Op`. -/
def l2OpNormedAddCommGroupAux : NormedAddCommGroup (Matrix m n 𝕜) :=
  @NormedAddCommGroup.induced ((Matrix m n 𝕜) ≃ₗ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m)) _
    _ _ _ ContinuousLinearMap.toNormedAddCommGroup.toNormedAddGroup _ _ <|
    (toEuclideanLin.trans toContinuousLinearMap).injective

/-- An auxiliary definition used only to construct the true `NormedRing` (and `Metric`) structure
provided by `Matrix.instMetricSpaceL2Op` and `Matrix.instNormedRingL2Op`. -/
def l2OpNormedRingAux : NormedRing (Matrix n n 𝕜) :=
  @NormedRing.induced ((Matrix n n 𝕜) ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)) _
    _ _ _ ContinuousLinearMap.toNormedRing _ _ toEuclideanCLM.injective

open Bornology Filter
open scoped Topology Uniformity

/-- The metric on `Matrix m n 𝕜` arising from the operator norm given by the identification with
(continuous) linear maps of `EuclideanSpace`. -/
def instL2OpMetricSpace : MetricSpace (Matrix m n 𝕜) := by
  /- We first replace the topology so that we can automatically replace the uniformity using
  `IsUniformAddGroup.toUniformSpace_eq`. -/
  letI normed_add_comm_group : NormedAddCommGroup (Matrix m n 𝕜) :=
    { l2OpNormedAddCommGroupAux.replaceTopology <|
        (toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap
        |>.toContinuousLinearEquiv.toHomeomorph.isInducing.eq_induced with
      norm := l2OpNormedAddCommGroupAux.norm
      dist_eq := l2OpNormedAddCommGroupAux.dist_eq }
  exact normed_add_comm_group.replaceUniformity <| by
    congr
    rw [← @IsUniformAddGroup.toUniformSpace_eq _ (Matrix.instUniformSpace m n 𝕜) _ _]
    rw [@IsUniformAddGroup.toUniformSpace_eq _ PseudoEMetricSpace.toUniformSpace _ _]

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instL2OpMetricSpace

open scoped Matrix.L2OpNorm

/-- The norm structure on `Matrix m n 𝕜` arising from the operator norm given by the identification
with (continuous) linear maps of `EuclideanSpace`. -/
def instL2OpNormedAddCommGroup : NormedAddCommGroup (Matrix m n 𝕜) where
  norm := l2OpNormedAddCommGroupAux.norm
  dist_eq := l2OpNormedAddCommGroupAux.dist_eq

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instL2OpNormedAddCommGroup

lemma l2_opNorm_def (A : Matrix m n 𝕜) :
    ‖A‖ = ‖(toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap A‖ := rfl

lemma l2_opNNNorm_def (A : Matrix m n 𝕜) :
    ‖A‖₊ = ‖(toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap A‖₊ := rfl

lemma l2_opNorm_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) : ‖Aᴴ‖ = ‖A‖ := by
  rw [l2_opNorm_def, toEuclideanLin_eq_toLin_orthonormal, LinearEquiv.trans_apply,
    toLin_conjTranspose, adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

lemma l2_opNNNorm_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) : ‖Aᴴ‖₊ = ‖A‖₊ :=
  Subtype.ext <| l2_opNorm_conjTranspose _

lemma l2_opNorm_conjTranspose_mul_self (A : Matrix m n 𝕜) : ‖Aᴴ * A‖ = ‖A‖ * ‖A‖ := by
  classical
  rw [l2_opNorm_def, toEuclideanLin_eq_toLin_orthonormal, LinearEquiv.trans_apply,
    Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun m 𝕜).toBasis), toLin_conjTranspose]
  exact ContinuousLinearMap.norm_adjoint_comp_self _

lemma l2_opNNNorm_conjTranspose_mul_self (A : Matrix m n 𝕜) : ‖Aᴴ * A‖₊ = ‖A‖₊ * ‖A‖₊ :=
  Subtype.ext <| l2_opNorm_conjTranspose_mul_self _

-- note: with only a type ascription in the left-hand side, Lean picks the wrong norm.
lemma l2_opNorm_mulVec (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖(EuclideanSpace.equiv m 𝕜).symm <| A *ᵥ x‖ ≤ ‖A‖ * ‖x‖ :=
  toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜) |>.trans toContinuousLinearMap A |>.le_opNorm x

lemma l2_opNNNorm_mulVec (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖(EuclideanSpace.equiv m 𝕜).symm <| A *ᵥ x‖₊ ≤ ‖A‖₊ * ‖x‖₊ :=
  A.l2_opNorm_mulVec x

lemma l2_opNorm_mul (A : Matrix m n 𝕜) (B : Matrix n l 𝕜) :
    ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  simp only [l2_opNorm_def]
  have := (toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) A
    |>.opNorm_comp_le <| (toEuclideanLin (n := l) (m := n) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) B
  convert this
  ext1 x
  exact congr($(Matrix.toLin'_mul A B) x)

lemma l2_opNNNorm_mul (A : Matrix m n 𝕜) (B : Matrix n l 𝕜) : ‖A * B‖₊ ≤ ‖A‖₊ * ‖B‖₊ :=
  l2_opNorm_mul A B

/-- The normed algebra structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endmorphisms of `EuclideanSpace 𝕜 n`. -/
def instL2OpNormedSpace : NormedSpace 𝕜 (Matrix m n 𝕜) where
  norm_smul_le r x := by
    rw [l2_opNorm_def, LinearEquiv.map_smul]
    exact norm_smul_le r ((toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap x)

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instL2OpNormedSpace

/-- The normed ring structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endmorphisms of `EuclideanSpace 𝕜 n`. -/
def instL2OpNormedRing : NormedRing (Matrix n n 𝕜) where
  dist_eq := l2OpNormedRingAux.dist_eq
  norm_mul_le := l2OpNormedRingAux.norm_mul_le

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instL2OpNormedRing

/-- This is the same as `Matrix.l2_opNorm_def`, but with a more bundled RHS for square matrices. -/
lemma cstar_norm_def (A : Matrix n n 𝕜) : ‖A‖ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖ := rfl

/-- This is the same as `Matrix.l2_opNNNorm_def`, but with a more bundled RHS for square
matrices. -/
lemma cstar_nnnorm_def (A : Matrix n n 𝕜) : ‖A‖₊ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖₊ := rfl

/-- The normed algebra structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endmorphisms of `EuclideanSpace 𝕜 n`. -/
def instL2OpNormedAlgebra : NormedAlgebra 𝕜 (Matrix n n 𝕜) where
  norm_smul_le := norm_smul_le

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instL2OpNormedAlgebra

/-- The operator norm on `Matrix n n 𝕜` given by the identification with (continuous) linear
endmorphisms of `EuclideanSpace 𝕜 n` makes it into a `L2OpRing`. -/
lemma instCStarRing : CStarRing (Matrix n n 𝕜) where
  norm_mul_self_le M := le_of_eq <| Eq.symm <| l2_opNorm_conjTranspose_mul_self M

scoped[Matrix.L2OpNorm] attribute [instance] Matrix.instCStarRing

end Matrix

end L2OpNorm

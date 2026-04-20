/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# The partial order on matrices

This file constructs the partial order and star ordered instances on matrices on `𝕜`.
This allows us to use more general results from C⋆-algebras, like `CFC.sqrt`.

## Main results

* `Matrix.instPartialOrder`: the partial order on matrices given by `x ≤ y := (y - x).PosSemidef`.
* `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`: for a positive semi-definite matrix `A`,
  we have `x⋆ A x = 0` iff `A x = 0`.
* `Matrix.toMatrixInnerProductSpace`: the inner product on matrices induced by a
  positive semi-definite matrix `M`: `⟪x, y⟫ = (y * M * xᴴ).trace`.

## Implementation notes

Note that the partial order instance is scoped to `MatrixOrder`.
Please `open scoped MatrixOrder` to use this.
-/

@[expose] public section

variable {𝕜 n : Type*} [RCLike 𝕜]

open scoped ComplexOrder
open Matrix

namespace Matrix

section PartialOrder

/-- The preorder on matrices given by `A ≤ B := (B - A).PosSemidef`. -/
abbrev instPreOrder : Preorder (Matrix n n 𝕜) where
  le A B := (B - A).PosSemidef
  le_refl A := sub_self A ▸ PosSemidef.zero
  le_trans A B C h₁ h₂ := sub_add_sub_cancel C B A ▸ h₂.add h₁

scoped[MatrixOrder] attribute [instance] Matrix.instPreOrder

open MatrixOrder

lemma le_iff {A B : Matrix n n 𝕜} : A ≤ B ↔ (B - A).PosSemidef := Iff.rfl

lemma nonneg_iff_posSemidef {A : Matrix n n 𝕜} : 0 ≤ A ↔ A.PosSemidef := by rw [le_iff, sub_zero]

protected alias ⟨LE.le.posSemidef, PosSemidef.nonneg⟩ := nonneg_iff_posSemidef

attribute [aesop safe forward (rule_sets := [CStarAlgebra])] PosSemidef.nonneg

private lemma le_antisymm_aux {A : Matrix n n 𝕜} (h₁ : A.PosSemidef) (h₂ : (-A).PosSemidef) :
    A = 0 := by
  classical
  ext i j
  have hdiag i : A i i = 0 :=
    le_antisymm (by simpa using h₂.diag_nonneg) (by simpa using h₁.diag_nonneg)
  have h1 := h₁.2 (.single i 1 + .single j (A j i))
  have h2 := h₂.2 (.single i 1 + .single j (A j i))
  simp [Finsupp.sum_add_index, mul_add, add_mul,
      -neg_add_rev, hdiag, ← h₁.1.apply j i, -RCLike.star_def] at *
  simpa using le_antisymm h2 h1

/-- The partial order on matrices given by `A ≤ B := (B - A).PosSemidef`. -/
abbrev instPartialOrder : PartialOrder (Matrix n n 𝕜) where
  le_antisymm A B h₁ h₂ := by
    simpa [sub_eq_zero, eq_comm] using le_antisymm_aux h₁
     (by simpa only [← neg_sub B, le_iff] using h₂)

scoped[MatrixOrder] attribute [instance] Matrix.instPartialOrder

lemma instIsOrderedAddMonoid : IsOrderedAddMonoid (Matrix n n 𝕜) where
  add_le_add_left _ _ _ _ := by rwa [le_iff, add_sub_add_right_eq_sub]

scoped[MatrixOrder] attribute [instance] Matrix.instIsOrderedAddMonoid

variable [Fintype n]

lemma instNonnegSpectrumClass : NonnegSpectrumClass ℝ (Matrix n n 𝕜) where
  quasispectrum_nonneg_of_nonneg A hA := by
    classical
    simp only [quasispectrum_eq_spectrum_union_zero ℝ A, Set.union_singleton, Set.mem_insert_iff,
      forall_eq_or_imp, le_refl, true_and]
    intro x hx
    obtain ⟨i, rfl⟩ := Set.ext_iff.mp
      hA.posSemidef.1.spectrum_real_eq_range_eigenvalues x |>.mp hx
    exact hA.posSemidef.eigenvalues_nonneg _

scoped[MatrixOrder] attribute [instance] instNonnegSpectrumClass

lemma instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜) :=
  .of_nonneg_iff' add_le_add_right fun A ↦
    ⟨fun hA ↦ by
      classical
      obtain ⟨X, hX, -, rfl⟩ :=
        sub_zero A ▸ CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hA.isHermitian
          (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
      exact ⟨X, hX.star_eq.symm ▸ rfl⟩,
    fun ⟨A, hA⟩ => hA ▸ (posSemidef_conjTranspose_mul_self A).nonneg⟩

scoped[MatrixOrder] attribute [instance] instStarOrderedRing

end PartialOrder

open scoped MatrixOrder

variable [Fintype n]

namespace PosSemidef

section sqrtDeprecated

variable [DecidableEq n] {A : Matrix n n 𝕜} (hA : PosSemidef A)

include hA

lemma inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ := by
  rw [eq_comm, CFC.sqrt_eq_iff _ _ hA.inv.nonneg (CFC.sqrt_nonneg A).posSemidef.inv.nonneg, ← sq,
    inv_pow', CFC.sq_sqrt A]

end sqrtDeprecated

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0`. -/
theorem dotProduct_mulVec_zero_iff {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    star x ⬝ᵥ A *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ dotProduct_zero _⟩
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  simp_rw [← Matrix.mulVec_mulVec, dotProduct_mulVec _ _ (B *ᵥ x), star_eq_conjTranspose,
    vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero] at h ⊢
  rw [h, mulVec_zero]

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0` (linear maps version). -/
theorem toLinearMap₂'_zero_iff [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    Matrix.toLinearMap₂' 𝕜 A (star x) x = 0 ↔ A *ᵥ x = 0 := by
  simpa only [toLinearMap₂'_apply'] using hA.dotProduct_mulVec_zero_iff x

theorem det_sqrt [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    (CFC.sqrt A).det = RCLike.sqrt A.det := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ A, hA.1.cfc_eq, RCLike.sqrt_of_nonneg hA.det_nonneg]
  simp only [IsHermitian.cfc, Real.coe_sqrt, Real.coe_toNNReal', det_map, det_diagonal,
    Function.comp_apply, hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod,
    RCLike.ofReal_re, Real.sqrt_prod _ fun _ _ ↦ hA.eigenvalues_nonneg _]
  grind

end PosSemidef

theorem IsHermitian.det_abs [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    det (CFC.abs A) = ‖det A‖ := by
  rw [CFC.abs_eq_cfc_norm A, hA.cfc_eq]
  simp [IsHermitian.cfc, -Unitary.conjStarAlgAut_apply, hA.det_eq_prod_eigenvalues]

theorem posSemidef_iff_isHermitian_and_spectrum_nonneg [DecidableEq n] {A : Matrix n n 𝕜} :
    A.PosSemidef ↔ A.IsHermitian ∧ spectrum 𝕜 A ⊆ {a : 𝕜 | 0 ≤ a} := by
  refine ⟨fun h => ⟨h.isHermitian, fun a => ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · simp only [h.isHermitian.spectrum_eq_image_range, Set.mem_image, Set.mem_range,
      exists_exists_eq_and, Set.mem_setOf_eq, forall_exists_index]
    rintro i rfl
    exact_mod_cast h.eigenvalues_nonneg _
  · rw [h1.posSemidef_iff_eigenvalues_nonneg]
    intro i
    simpa [h1.spectrum_eq_image_range] using @h2 (h1.eigenvalues i)

/-- A positive semi-definite matrix is positive definite if and only if it is invertible. -/
@[grind =]
theorem PosSemidef.posDef_iff_isUnit [DecidableEq n] {x : Matrix n n 𝕜}
    (hx : x.PosSemidef) : x.PosDef ↔ IsUnit x := by
  refine ⟨fun h => h.isUnit, fun h => .of_dotProduct_mulVec_pos hx.1 fun v hv => ?_⟩
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  simp_rw [dotProduct_mulVec, ← vecMul_vecMul, star_eq_conjTranspose, ← star_mulVec,
    ← dotProduct_mulVec, dotProduct_star_self_pos_iff]
  contrapose! hv
  rw [← map_eq_zero_iff (f := (yᴴ * y).mulVecLin) (mulVec_injective_iff_isUnit.mpr h),
    mulVecLin_apply, ← mulVec_mulVec, hv, mulVec_zero]

theorem isStrictlyPositive_iff_posDef [DecidableEq n] {x : Matrix n n 𝕜} :
    IsStrictlyPositive x ↔ x.PosDef :=
  ⟨fun h => h.nonneg.posSemidef.posDef_iff_isUnit.mpr h.isUnit,
  fun h => h.isUnit.isStrictlyPositive h.posSemidef.nonneg⟩

alias ⟨IsStrictlyPositive.posDef, PosDef.isStrictlyPositive⟩ := isStrictlyPositive_iff_posDef

attribute [aesop safe forward (rule_sets := [CStarAlgebra])] PosDef.isStrictlyPositive

@[deprecated IsStrictlyPositive.commute_iff (since := "2025-09-26")]
theorem PosDef.commute_iff {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.PosDef) :
    Commute A B ↔ (A * B).PosDef := by
  classical
  rw [hA.isStrictlyPositive.commute_iff hB.isStrictlyPositive, isStrictlyPositive_iff_posDef]

set_option linter.unusedDecidableInType false in
@[deprecated IsStrictlyPositive.sqrt (since := "2025-09-26")]
lemma PosDef.posDef_sqrt [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosDef) :
    PosDef (CFC.sqrt M) := hM.isStrictlyPositive.sqrt.posDef

section kronecker

omit [Fintype n]

variable [Finite n] {m : Type*} [Finite m]

open scoped Kronecker

/-- The kronecker product of two positive semi-definite matrices is positive semi-definite. -/
theorem PosSemidef.kronecker {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosSemidef) (hy : y.PosSemidef) : (x ⊗ₖ y).PosSemidef := by
  classical
  have := Fintype.ofFinite n; have := Fintype.ofFinite m
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx.nonneg
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hy.nonneg
  simpa [mul_kronecker_mul, ← conjTranspose_kronecker, star_eq_conjTranspose] using
    posSemidef_conjTranspose_mul_self _

open Matrix in
/-- The kronecker of two positive definite matrices is positive definite. -/
theorem PosDef.kronecker {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosDef) (hy : y.PosDef) : (x ⊗ₖ y).PosDef := by
  classical
  have := Fintype.ofFinite n; have := Fintype.ofFinite m
  exact hx.posSemidef.kronecker hy.posSemidef |>.posDef_iff_isUnit.mpr <|
    hx.isUnit.kronecker hy.isUnit

end kronecker

section hadamard

variable {ι : Type*}

/-- [**Schur product theorem**][schur1911] (positive semidefinite version): the Hadamard (entrywise)
product of positive semidefinite matrices is positive semidefinite. -/
theorem PosSemidef.hadamard {A B : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊙ B).PosSemidef := by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x ↦ ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosSemidef := by
    have hAs := hA.submatrix ((↑) : x.support → ι)
    have hBs := hB.submatrix ((↑) : x.support → ι)
    rw [submatrix_hadamard, posSemidef_iff_dotProduct_mulVec]
    refine ⟨hAs.isHermitian.hadamard hBs.isHermitian, fun y ↦ ?_⟩
    rw [star_dotProduct_hadamard_mulVec_eq_kronecker]
    exact (hAs.kronecker hBs).dotProduct_mulVec_nonneg _
  simpa [Finsupp.sum, ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain] using hAB.2 _

/-- **Schur product theorem**: the Hadamard (entrywise) product of positive definite
matrices is positive definite. -/
theorem PosDef.hadamard {A B : Matrix ι ι 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) : (A ⊙ B).PosDef := by
  classical
  refine ⟨hA.isHermitian.hadamard hB.isHermitian, fun x hx ↦ ?_⟩
  have hAB : ((A ⊙ B).submatrix (↑) (↑) : Matrix x.support _ _).PosDef := by
    have hAs : (A.submatrix (↑) (↑) : Matrix x.support _ _).PosDef :=
      hA.submatrix Subtype.coe_injective
    have hBs : (B.submatrix (↑) (↑) : Matrix x.support _ _).PosDef :=
      hB.submatrix Subtype.coe_injective
    rw [submatrix_hadamard, posDef_iff_dotProduct_mulVec]
    refine ⟨hAs.isHermitian.hadamard hBs.isHermitian, fun y hy ↦ ?_⟩
    rw [star_dotProduct_hadamard_mulVec_eq_kronecker]
    exact (hAs.kronecker hBs).dotProduct_mulVec_pos <| by simpa
  simp_rw [RCLike.star_def, hadamard_apply, Finsupp.sum,
    ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain]
  refine hAB.2 ?_
  simpa [← Finsupp.support_nonempty_iff] using Finsupp.support_nonempty_iff.mpr hx

end hadamard

/--
A matrix is positive definite if and only if it has the form `Bᴴ * B` for some invertible `B`.
-/
@[deprecated CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self (since := "2025-09-28")]
lemma posDef_iff_eq_conjTranspose_mul_self [DecidableEq n] {A : Matrix n n 𝕜} :
    PosDef A ↔ ∃ B : Matrix n n 𝕜, IsUnit B ∧ A = Bᴴ * B :=
  isStrictlyPositive_iff_posDef.symm.trans CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self

section tracePositiveLinearMap
variable (n α 𝕜 : Type*) [Fintype n] [Semiring α] [RCLike 𝕜] [Module α 𝕜]

/-- `Matrix.trace` as a positive linear map. -/
def tracePositiveLinearMap : Matrix n n 𝕜 →ₚ[α] 𝕜 :=
  .mk₀ (traceLinearMap n α 𝕜) fun _ h ↦ h.posSemidef.trace_nonneg

@[simp] lemma toLinearMap_tracePositiveLinearMap :
    (tracePositiveLinearMap n α 𝕜).toLinearMap = traceLinearMap n α 𝕜 := rfl

@[simp] lemma tracePositiveLinearMap_apply (x) : tracePositiveLinearMap n α 𝕜 x = trace x := rfl

end tracePositiveLinearMap

set_option backward.privateInPublic true in
/-- The pre-inner product space structure implementation. Only an auxiliary for
`Matrix.toMatrixSeminormedAddCommGroup`, `Matrix.toMatrixNormedAddCommGroup`,
and `Matrix.toMatrixInnerProductSpace`. -/
private abbrev PosSemidef.matrixPreInnerProductSpace {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    PreInnerProductSpace.Core 𝕜 (Matrix n n 𝕜) where
  inner x y := (y * M * xᴴ).trace
  conj_inner_symm _ _ := by
    simp only [mul_assoc, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose, hM.isHermitian.eq]
  re_inner_nonneg x := RCLike.nonneg_iff.mp (hM.mul_mul_conjTranspose_same x).trace_nonneg |>.1
  add_left := by simp [mul_add]
  smul_left := by simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
@[implicit_reducible]
noncomputable def toMatrixSeminormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    SeminormedAddCommGroup (Matrix n n 𝕜) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ hM.matrixPreInnerProductSpace

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`:
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
@[implicit_reducible]
noncomputable def toMatrixNormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosDef) :
    NormedAddCommGroup (Matrix n n 𝕜) :=
  letI : InnerProductSpace.Core 𝕜 (Matrix n n 𝕜) :=
  { __ := hM.posSemidef.matrixPreInnerProductSpace
    definite x hx := by
      classical
      obtain ⟨y, hy, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
        hM.isStrictlyPositive
      simp +instances only at hx
      rw [← mul_assoc, ← conjTranspose_conjTranspose x, star_eq_conjTranspose, ← conjTranspose_mul,
        conjTranspose_conjTranspose, mul_assoc, trace_conjTranspose_mul_self_eq_zero_iff] at hx
      lift y to (Matrix n n 𝕜)ˣ using hy
      simpa [← mul_assoc] using congr(y⁻¹ * $hx) }
  this.toNormedAddCommGroup

/-- A positive semi-definite matrix `M` induces an inner product on `Matrix n n 𝕜`:
`⟪x, y⟫ = (y * M * xᴴ).trace`. -/
@[implicit_reducible]
def toMatrixInnerProductSpace (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    letI : SeminormedAddCommGroup (Matrix n n 𝕜) := M.toMatrixSeminormedAddCommGroup hM
    InnerProductSpace 𝕜 (Matrix n n 𝕜) :=
  InnerProductSpace.ofCore _

@[deprecated (since := "2025-11-18")] alias PosDef.matrixNormedAddCommGroup :=
  toMatrixNormedAddCommGroup
@[deprecated (since := "2025-11-12")] alias PosDef.matrixInnerProductSpace :=
  toMatrixInnerProductSpace

end Matrix

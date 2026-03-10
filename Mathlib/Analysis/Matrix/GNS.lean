/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Matrix.Order

/-! The GNS-inner product on matrices

This file shows that the GNS-inner product space on matrices is equivalent
to `Matrix.toMatrixInnerProductSpace`.
So choosing a positive linear map `Matrix n n ℂ →ₚ[ℂ] ℂ` is equivalent to choosing
a positive semi-definite matrix `Q`. -/

@[expose] public section

variable {n m R 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

open scoped MatrixOrder ComplexOrder

namespace Matrix

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
noncomputable def toMatrixSeminormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    SeminormedAddCommGroup (Matrix n n 𝕜) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ hM.matrixPreInnerProductSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive definite matrix `M` induces a norm on `Matrix n n 𝕜`:
`‖x‖ = sqrt (x * M * xᴴ).trace`. -/
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

set_option backward.isDefEq.respectTransparency false in
/-- A positive semi-definite matrix `M` induces an inner product on `Matrix n n 𝕜`:
`⟪x, y⟫ = (y * M * xᴴ).trace`. -/
def toMatrixInnerProductSpace (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    letI : SeminormedAddCommGroup (Matrix n n 𝕜) := M.toMatrixSeminormedAddCommGroup hM
    InnerProductSpace 𝕜 (Matrix n n 𝕜) :=
  InnerProductSpace.ofCore _

@[deprecated (since := "2025-11-18")] alias PosDef.matrixNormedAddCommGroup :=
  toMatrixNormedAddCommGroup
@[deprecated (since := "2025-11-12")] alias PosDef.matrixInnerProductSpace :=
  toMatrixInnerProductSpace

open Matrix

/-- The *weight* of a linear functional `f` on matrices is the matrix such that
`f a = trace (a * f.weight)` for all `a`. -/
def Module.Dual.weight [Semiring R] (f : Module.Dual R (Matrix n n R)) :
    Matrix n n R := ∑ i, ∑ j, .single j i (f (.single i j 1))

theorem Module.Dual.eq_trace_mul_weight [Semiring R] (f : Module.Dual R (Matrix n n R))
    (a : Matrix n n R) : f a = (a * f.weight).trace := by
  conv_lhs => rw [matrix_eq_sum_single a]
  simp_rw [fun i j ↦ show single i j (a i j) = a i j • single i j 1 by simp,
    map_sum, map_smul]
  simp [weight, Finset.mul_sum, trace, sum_apply, mul_apply,
    Matrix.single_apply, ite_and]

/-- `f` is star-preserving iff its weight is Hermitian. -/
theorem Module.Dual.isSelfAdjoint_toConv_iff_isHermitian_weight
    [CommSemiring R] [StarRing R] (f : Module.Dual R (Matrix n n R)) :
    IsSelfAdjoint (WithConv.toConv f) ↔ f.weight.IsHermitian := by
  simp only [IsSelfAdjoint, WithConv.ext_iff, LinearMap.ext_iff, LinearMap.intrinsicStar_apply]
  simp_rw [eq_trace_mul_weight, star_eq_conjTranspose, ← trace_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, trace_mul_comm _ f.weight, ← ext_iff_trace_mul_right, IsHermitian]

open scoped ComplexOrder MatrixOrder

-- `f` is a positive and star-preserving iff `f.weight` is positive semi-definite
-- when `R = ℂ`, we can drop `toConv f` is self-adjoint (but a lot of missing API ugh)
theorem Module.Dual.monotone_and_isSelfAdjoint_toConv_iff_posSemidef_weight
    {𝕜 : Type*} [RCLike 𝕜] (f : Module.Dual 𝕜 (Matrix n n 𝕜)) :
    Monotone f ∧ IsSelfAdjoint (WithConv.toConv f) ↔ f.weight.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec, isSelfAdjoint_toConv_iff_isHermitian_weight,
    and_comm, and_congr_right_iff]
  intro h
  simp_rw [fun y ↦ show star y ⬝ᵥ f.weight *ᵥ y = (f.weight * vecMulVec y (star y)).trace by
    rw [vecMulVec_eq Unit, trace_mul_cycle', ← replicateCol_mulVec, trace_mul_comm,
      trace_replicateCol_mul_replicateRow, dotProduct_comm]]
  refine ⟨fun hs ↦ ?_, fun H x y ↦ ?_⟩
  · simp only [Monotone, eq_trace_mul_weight] at hs
    intro y
    simpa [trace_mul_comm f.weight] using hs (posSemidef_vecMulVec_self_star y).nonneg
  · rw [← sub_nonneg, ← sub_nonneg (b := f x), ← map_sub, eq_trace_mul_weight,
      trace_mul_comm]
    intro h
    obtain ⟨m, e, he⟩ := posSemidef_iff_eq_sum_vecMulVec.mp h.posSemidef
    simp [he, Matrix.mul_sum]
    exact Finset.sum_nonneg fun _ _ ↦ H _

theorem isHermitian_iff_star_dotProduct {n} [Fintype n]
    {A : Matrix n n ℂ} :
    A.IsHermitian ↔ ∀ x, star (star x ⬝ᵥ A *ᵥ x) = star x ⬝ᵥ A *ᵥ x := by
  conv_lhs => rw [← conjTranspose_conjTranspose A, isHermitian_conjTranspose_iff]
  classical
  simp [isHermitian_iff_isSymmetric, LinearMap.isSymmetric_iff_inner_map_self_real,
    EuclideanSpace.inner_eq_star_dotProduct, star_mulVec, dotProduct_comm _ (_ ᵥ* _),
    ← dotProduct_mulVec, (WithLp.toLp_surjective _).forall]

theorem posSemidef_iff_complex {n} [Fintype n] (x : Matrix n n ℂ) :
    x.PosSemidef ↔ ∀ (y : n → ℂ), 0 ≤ star y ⬝ᵥ x.mulVec y := by
  rw [posSemidef_iff_dotProduct_mulVec, isHermitian_iff_star_dotProduct]
  simp_all [Complex.nonneg_iff, eq_comm (a := (0 : ℝ)), ← Complex.conj_eq_iff_im]

theorem Module.Dual.monotone_iff_posSemidef_weight (f : Module.Dual ℂ (Matrix n n ℂ)) :
    Monotone f ↔ f.weight.PosSemidef := by
  -- rw [← monotone_and_isSelfAdjoint_toConv_iff_posSemidef_weight, iff_self_and]
  -- intro hf
  -- rw [isSelfAdjoint_toConv_iff_isHermitian_weight]
  rw [posSemidef_iff_complex]
  -- literally the same exact code as above...
  simp_rw [fun y ↦ show star y ⬝ᵥ f.weight *ᵥ y = (f.weight * vecMulVec y (star y)).trace by
    rw [vecMulVec_eq Unit, trace_mul_cycle', ← replicateCol_mulVec, trace_mul_comm,
      trace_replicateCol_mul_replicateRow, dotProduct_comm]]
  refine ⟨fun hs ↦ ?_, fun H x y ↦ ?_⟩
  · simp only [Monotone, eq_trace_mul_weight] at hs
    intro y
    simpa [trace_mul_comm f.weight] using hs (posSemidef_vecMulVec_self_star y).nonneg
  · rw [← sub_nonneg, ← sub_nonneg (b := f x), ← map_sub, eq_trace_mul_weight,
      trace_mul_comm]
    intro h
    obtain ⟨m, e, he⟩ := posSemidef_iff_eq_sum_vecMulVec.mp h.posSemidef
    simp [he, Matrix.mul_sum]
    exact Finset.sum_nonneg fun _ _ ↦ H _

end Matrix

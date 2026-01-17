/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Permutation matrices

This file defines the matrix associated with a permutation

## Main definitions

- `Equiv.Perm.permMatrix`: the permutation matrix associated with an `Equiv.Perm`

## Main results

- `Matrix.det_permutation`: the determinant is the sign of the permutation
- `Matrix.trace_permutation`: the trace is the number of fixed points of the permutation

-/

@[expose] public section

open Equiv

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

variable (R) in
/-- the permutation matrix associated with an `Equiv.Perm` -/
abbrev Equiv.Perm.permMatrix [Zero R] [One R] : Matrix n n R :=
  σ.toPEquiv.toMatrix

namespace Matrix

@[simp] lemma permMatrix_refl [Zero R] [One R] : Equiv.Perm.permMatrix R (.refl n) = 1 := by
  simp [← Matrix.ext_iff, Matrix.one_apply]

@[simp]
lemma permMatrix_one [Zero R] [One R] : (1 : Equiv.Perm n).permMatrix R = 1 :=
  permMatrix_refl

@[simp]
lemma transpose_permMatrix [Zero R] [One R] : (σ.permMatrix R).transpose = (σ⁻¹).permMatrix R := by
  rw [← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, ← Equiv.Perm.inv_def]

@[simp]
lemma conjTranspose_permMatrix [NonAssocSemiring R] [StarRing R] :
    (σ.permMatrix R).conjTranspose = (σ⁻¹).permMatrix R := by
  simp only [conjTranspose, transpose_permMatrix, map]
  aesop

variable [Fintype n]

/-- The determinant of a permutation matrix equals its sign. -/
@[simp]
theorem det_permutation [CommRing R] : det (σ.permMatrix R) = Perm.sign σ := by
  rw [← Matrix.mul_one (σ.permMatrix R), PEquiv.toMatrix_toPEquiv_mul,
    det_permute, det_one, mul_one]

/-- The trace of a permutation matrix equals the number of fixed points. -/
theorem trace_permutation [AddCommMonoidWithOne R] :
    trace (σ.permMatrix R) = (Function.fixedPoints σ).ncard := by
  delta trace
  simp [toPEquiv_apply, ← Set.ncard_coe_finset, Function.fixedPoints, Function.IsFixedPt]

lemma permMatrix_mulVec {v : n → R} [CommRing R] :
    σ.permMatrix R *ᵥ v = v ∘ σ := by
  ext j
  simp [mulVec_eq_sum, Pi.single, Function.update, Equiv.eq_symm_apply]

lemma vecMul_permMatrix {v : n → R} [CommRing R] :
    v ᵥ* σ.permMatrix R = v ∘ σ.symm := by
  ext j
  simp [vecMul_eq_sum, Pi.single, Function.update, ← Equiv.symm_apply_eq]

@[simp]
lemma permMatrix_mul [NonAssocSemiring R] :
    (σ * τ).permMatrix R = τ.permMatrix R * σ.permMatrix R := by
  rw [Perm.permMatrix, Perm.mul_def, toPEquiv_trans, PEquiv.toMatrix_trans]

/-- `permMatrix` as a homomorphism. -/
@[simps]
def permMatrixHom [NonAssocSemiring R] : Perm n →* Matrix n n R where
  toFun σ := σ⁻¹.permMatrix R
  map_one' := permMatrix_one
  map_mul' σ τ := by rw [_root_.mul_inv_rev, permMatrix_mul]

open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜]

/--
The l2-operator norm of a permutation matrix is bounded above by 1.
See `Matrix.permMatrix_l2_opNorm_eq` for the equality statement assuming the matrix is nonempty.
-/
theorem permMatrix_l2_opNorm_le : ‖σ.permMatrix 𝕜‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by simp) <| by
    simp [EuclideanSpace.norm_eq, toEuclideanLin_apply, permMatrix_mulVec,
      σ.sum_comp _ (fun i ↦ ‖_‖ ^ 2)]

/--
The l2-operator norm of a nonempty permutation matrix is equal to 1.
Note that this is not true for the empty case, since the empty matrix has l2-operator norm 0.
See `Matrix.permMatrix_l2_opNorm_le` for the inequality version of the empty case.
-/
theorem permMatrix_l2_opNorm_eq [Nonempty n] : ‖σ.permMatrix 𝕜‖ = 1 :=
  le_antisymm (permMatrix_l2_opNorm_le σ) <| by
    inhabit n
    simpa [EuclideanSpace.norm_eq, permMatrix_mulVec, ← Equiv.eq_symm_apply, apply_ite] using
      (σ.permMatrix 𝕜).l2_opNorm_mulVec (WithLp.toLp _ (Pi.single default 1))

end Matrix

/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Matrix.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm

/-!
# The Gelfand radius as an algebra norm

This file uses the Gelfand radius to define an algebra norm on a finite extension of a normed field.

## Main definitions

* `gelfandRadiusNorm K L`: The algebra norm on a finite extension `L` of a normed field `K`.
  The norm of `x : L` is defined as the Gelfand radius of multiplication by `x` on `L`.

## Main statements

* `isPowMul_gelfandRadiusNorm`: the Gelfand radius norm is power-multiplicative.
* `gelfandRadiusNorm_algebraMap`: the Gelfand radius norm is invariant under algebra maps.
* `gelfandRadiusNorm_map`: the Gelfand radius norm is invariant under algebra homomorphisms.
-/

public section

variable (K L M : Type*) [NormedField K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra L M] [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional K M]

open scoped Matrix.Norms.Operator

/-- The algebra norm on a finite extension `L` of a normed field `K`.
The norm of `x : L` is defined as the Gelfand radius of multiplication by `x` on `L`. -/
noncomputable def gelfandRadiusNorm : AlgebraNorm K L where
  toFun x := gelfandRadius (Algebra.leftMulMatrix (Module.finBasis K L) x)
  map_zero' := by rw [map_zero, gelfandRadius_zero]
  add_le' x y := by grw [map_add, ((Commute.all x y).map _).gelfandRadius_add_le]
  neg' x := by rw [map_neg, gelfandRadius_neg]
  mul_le' x y := by grw [map_mul, ((Commute.all x y).map _).gelfandRadius_mul_le]
  eq_zero_of_map_eq_zero' x h := by
    have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
    have hx := ((Commute.inv_right_self₀ x).map
      (Algebra.leftMulMatrix (Module.finBasis K L))).gelfandRadius_mul_le
    contrapose! hx
    simp [← map_mul, h, hx]
  smul' x y := by rw [map_smul, gelfandRadius_smul]

variable {L} in
theorem gelfandRadiusNorm_def (x : L) :
    gelfandRadiusNorm K L x = gelfandRadius (Algebra.leftMulMatrix (Module.finBasis K L) x) := by
  rfl

@[simp]
theorem gelfandRadiusNorm_one : gelfandRadiusNorm K L 1 = 1 := by
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  rw [gelfandRadiusNorm_def, map_one, gelfandRadius_one]

variable {K} in
@[simp]
theorem gelfandRadiusNorm_eq_norm (x : K) : gelfandRadiusNorm K K x = ‖x‖ := by
  simpa using map_smul_eq_mul (gelfandRadiusNorm K K) x 1

/-- The Gelfand radius norm is power-multiplicative. -/
theorem isPowMul_gelfandRadiusNorm : IsPowMul (gelfandRadiusNorm K L) := by
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  intro x k hk
  simp_rw [gelfandRadiusNorm_def, map_pow, gelfandRadius_pow]

variable {K L} in
theorem Module.Basis.gelfandRadiusNorm_apply
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (x : L) :
    gelfandRadiusNorm K L x = gelfandRadius (Algebra.leftMulMatrix b x) := by
  simp_rw [gelfandRadiusNorm_def, Algebra.leftMulMatrix_apply]
  rw [← basis_toMatrix_mul_linearMap_toMatrix b b (Module.finBasis K L),
    Matrix.gelfandRadius_mul_comm, linearMap_toMatrix_mul_basis_toMatrix]

variable {L} in
/-- The Gelfand radius norm is invariant under algebra maps. -/
@[simp]
theorem gelfandRadiusNorm_algebraMap (M : Type*) [Field M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [FiniteDimensional K M] (x : L) :
    gelfandRadiusNorm K M (algebraMap L M x) = gelfandRadiusNorm K L x := by
  have : FiniteDimensional L M := .of_restrictScalars_finite K L M
  have : NeZero (Module.finrank L M) := ⟨Module.finrank_pos.ne'⟩
  let bKL := Module.finBasis K L
  let bLM := Module.finBasis L M
  rw [(bKL.smulTower bLM).gelfandRadiusNorm_apply, Algebra.smulTower_leftMulMatrix_algebraMap,
    Matrix.gelfandRadius_blockDiagonal, ciSup_const, bKL.gelfandRadiusNorm_apply]

variable {K L} in
/-- The Gelfand radius norm is invariant under algebra homomorphisms. -/
@[simp]
theorem gelfandRadiusNorm_map {M : Type*} [Field M] [Algebra K M] [FiniteDimensional K M]
    {F : Type*} [FunLike F L M] [AlgHomClass F K L M] (f : F) (x : L) :
    gelfandRadiusNorm K M (f x) = gelfandRadiusNorm K L x :=
  let := (AlgHom.ofClass f).toAlgebra
  gelfandRadiusNorm_algebraMap K M x

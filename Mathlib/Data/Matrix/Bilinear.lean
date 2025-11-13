/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Bundled versions of multiplication for matrices

This file provides versions of `LinearMap.mulLeft` and `LinearMap.mulRight` which work for the
heterogeneous multiplication of matrices.
-/

variable {l m n o : Type*} {R A : Type*}

section NonUnitalNonAssocSemiring
variable (R) [Fintype m]

section one_side
variable [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

section left
variable (n) [SMulCommClass R A A]

/-- A version of `LinearMap.mulLeft` for matrix multiplication. -/
@[simps]
def mulLeftLinearMap (X : Matrix l m A) :
    Matrix m n A →ₗ[R] Matrix l n A where
  toFun := (X * ·)
  map_smul' := Matrix.mul_smul _
  map_add' := Matrix.mul_add _

/-- On square matrices, `Matrix.mulLeftLinearMap` and `LinearMap.mulLeft` coincide. -/
theorem mulLeftLinearMap_eq_mulLeft :
    mulLeftLinearMap m R = LinearMap.mulLeft R (A := Matrix m m A) := rfl

/-- A version of `LinearMap.mulLeft_zero_eq_zero` for matrix multiplication. -/
@[simp]
theorem mulLeftLinearMap_zero_eq_zero : mulLeftLinearMap n R (0 : Matrix l m A) = 0 :=
  LinearMap.ext fun _ => Matrix.zero_mul _

end left

section right
variable (l) [IsScalarTower R A A]

/-- A version of `LinearMap.mulRight` for matrix multiplication. -/
@[simps]
def mulRightLinearMap (Y : Matrix m n A) :
    Matrix l m A →ₗ[R] Matrix l n A where
  toFun := (· * Y)
  map_smul' _ _ := Matrix.smul_mul _ _ _
  map_add' _ _ := Matrix.add_mul _ _ _

/-- On square matrices, `Matrix.mulRightLinearMap` and `LinearMap.mulRight` coincide. -/
theorem mulRightLinearMap_eq_mulRight :
    mulRightLinearMap m R = LinearMap.mulRight R (A := Matrix m m A) := rfl

/-- A version of `LinearMap.mulLeft_zero_eq_zero` for matrix multiplication. -/
@[simp]
theorem mulRightLinearMap_zero_eq_zero : mulRightLinearMap l R (0 : Matrix m n A) = 0 :=
  LinearMap.ext fun _ => Matrix.mul_zero _

end right

end one_side

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]

/-- A version of `LinearMap.mul` for matrix multiplication. -/
@[simps!]
def mulLinearMap : Matrix l m A →ₗ[R] Matrix m n A →ₗ[R] Matrix l n A where
  toFun := mulLeftLinearMap n R
  map_add' _ _ := LinearMap.ext fun _ => Matrix.add_mul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => Matrix.smul_mul _ _ _

/-- On square matrices, `Matrix.mulLinearMap` and `LinearMap.mul` coincide. -/
theorem mulLinearMap_eq_mul :
    mulLinearMap R = LinearMap.mul R (A := Matrix m m A) := rfl

end NonUnitalNonAssocSemiring

section NonUnital

section one_side
variable [Fintype m] [Fintype n] [Semiring R] [NonUnitalSemiring A] [Module R A]

/-- A version of `LinearMap.mulLeft_mul` for matrix multiplication. -/
@[simp]
theorem mulLeftLinearMap_mul [SMulCommClass R A A] (a : Matrix l m A) (b : Matrix m n A) :
    mulLeftLinearMap o R (a * b) = (mulLeftLinearMap o R a).comp (mulLeftLinearMap o R b) := by
  ext
  simp only [mulLeftLinearMap_apply, LinearMap.comp_apply, Matrix.mul_assoc]

/-- A version of `LinearMap.mulRight_mul` for matrix multiplication. -/
@[simp]
theorem mulRightLinearMap_mul [IsScalarTower R A A] (a : Matrix m n A) (b : Matrix n o A) :
    mulRightLinearMap l R (a * b) = (mulRightLinearMap l R b).comp (mulRightLinearMap l R a) := by
  ext
  simp only [mulRightLinearMap_apply, LinearMap.comp_apply, Matrix.mul_assoc]

end one_side

variable [Fintype m] [Fintype n] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]

/-- A version of `LinearMap.commute_mulLeft_right` for matrix multiplication. -/
theorem commute_mulLeftLinearMap_mulRightLinearMap (a : Matrix l m A) (b : Matrix n o A) :
    mulLeftLinearMap o R a ∘ₗ mulRightLinearMap m R b =
      mulRightLinearMap l R b ∘ₗ mulLeftLinearMap n R a := by
  ext c : 1
  exact (Matrix.mul_assoc a c b).symm

end NonUnital

section Semiring

section one_side
variable [Fintype m] [DecidableEq m] [Semiring R] [Semiring A]

section left
variable [Module R A] [SMulCommClass R A A]

/-- A version of `LinearMap.mulLeft_one` for matrix multiplication. -/
@[simp]
theorem mulLeftLinearMap_one : mulLeftLinearMap n R (1 : Matrix m m A) = LinearMap.id :=
  LinearMap.ext fun _ => Matrix.one_mul _

omit [DecidableEq m] in
/-- A version of `LinearMap.mulLeft_eq_zero_iff` for matrix multiplication. -/
@[simp]
theorem mulLeftLinearMap_eq_zero_iff [Nonempty n] (a : Matrix l m A) :
    mulLeftLinearMap n R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · inhabit n
    ext i j
    classical
    replace h := DFunLike.congr_fun h (Matrix.single j (default : n) 1)
    simpa using Matrix.ext_iff.2 h i default
  · rw [h]
    exact mulLeftLinearMap_zero_eq_zero _ _

/-- A version of `LinearMap.pow_mulLeft` for matrix multiplication. -/
@[simp]
theorem pow_mulLeftLinearMap (a : Matrix m m A) (k : ℕ) :
    mulLeftLinearMap n R a ^ k = mulLeftLinearMap n R (a ^ k) :=
  match k with
  | 0 => by rw [pow_zero, pow_zero, mulLeftLinearMap_one, Module.End.one_eq_id]
  | (n + 1) => by
    rw [pow_succ, pow_succ, mulLeftLinearMap_mul, Module.End.mul_eq_comp, pow_mulLeftLinearMap]

end left

section right
variable [Module R A] [IsScalarTower R A A]

/-- A version of `LinearMap.mulRight_one` for matrix multiplication. -/
@[simp]
theorem mulRightLinearMap_one : mulRightLinearMap l R (1 : Matrix m m A) = LinearMap.id :=
  LinearMap.ext fun _ => Matrix.mul_one _

omit [DecidableEq m] in
/-- A version of `LinearMap.mulRight_eq_zero_iff` for matrix multiplication. -/
@[simp]
theorem mulRightLinearMap_eq_zero_iff (a : Matrix m n A) [Nonempty l] :
    mulRightLinearMap l R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  · inhabit l
    ext i j
    classical
    replace h := DFunLike.congr_fun h (Matrix.single (default : l) i 1)
    simpa using Matrix.ext_iff.2 h default j
  · rw [h]
    exact mulRightLinearMap_zero_eq_zero _ _

/-- A version of `LinearMap.pow_mulRight` for matrix multiplication. -/
@[simp]
theorem pow_mulRightLinearMap (a : Matrix m m A) (k : ℕ) :
    mulRightLinearMap l R a ^ k = mulRightLinearMap l R (a ^ k) :=
  match k with
  | 0 => by rw [pow_zero, pow_zero, mulRightLinearMap_one, Module.End.one_eq_id]
  | (n + 1) => by
    rw [pow_succ, pow_succ', mulRightLinearMap_mul, Module.End.mul_eq_comp, pow_mulRightLinearMap]

end right

end one_side

end Semiring

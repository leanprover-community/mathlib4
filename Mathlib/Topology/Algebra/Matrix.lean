/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.Basic

namespace Matrix

variable {l m n R A M : Type*}
variable [TopologicalSpace R] [TopologicalSpace A] [TopologicalSpace M]

section semimodule
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [TopologicalSemiring R] [ContinuousAdd M]

/-- `Matrix.transpose` as a `ContinousLinearEquiv`. -/
def transposeCLE : Matrix m n M ≃L[R] Matrix n m M where
  toLinearEquiv := transposeLinearEquiv m n R M
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose


/-- `Matrix.trace` as a `ContinousLinearMap`. -/
def traceCLM [Fintype n] : Matrix n n M →L[R] M where
  toLinearMap := traceLinearMap _ _ _
  cont := continuous_id.matrix_trace

end semimodule

/-- `Matrix.conjTranspose` as a `ContinousLinearEquiv`. -/
def conjTransposeCLE
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    [StarRing R] [StarAddMonoid M] [StarModule R M]
    [TopologicalSemiring R] [ContinuousAdd M] [ContinuousStar M] :
    Matrix m n M ≃SL[starRingEnd R] Matrix n m M where
  toLinearEquiv := conjTransposeLinearEquiv m n R M
  continuous_toFun := continuous_id.matrix_conjTranspose
  continuous_invFun := continuous_id.matrix_conjTranspose

#check LinearMap.mulLeft

section linear

variable [Fintype m] [CommSemiring R] [NonAssocSemiring A] [Module R A]

/-- A version of `LinearMap.mulLeft` for matrix multiplication. -/
@[simps]
def mulLeft [SMulCommClass R A A] (X : Matrix l m A) :
    Matrix m n A →ₗ[R] Matrix l n A where
  toFun := (X * ·)
  map_smul' := Matrix.mul_smul _
  map_add' := Matrix.mul_add _

/-- A version of `LinearMap.mulRight` for matrix multiplication. -/
@[simps]
def mulRight [IsScalarTower R A A] (Y : Matrix m n A) :
    Matrix l m A →ₗ[R] Matrix l n A where
  toFun := (· * Y)
  map_smul' _ _ := Matrix.smul_mul _ _ _
  map_add' _ _ := Matrix.add_mul _ _ _

/-- A versoin of `LinearMap.mul` for matrix multiplication. -/
def mul [SMulCommClass R A A] [IsScalarTower R A A] :
    Matrix l m A →ₗ[R] Matrix m n A →ₗ[R] Matrix l n A where
  toFun := mulLeft
  map_add' _ _ := LinearMap.ext fun _ => Matrix.add_mul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => Matrix.smul_mul _ _ _

def mulLeftCLM
    [CommSemiring R] [NonAssocSemiring A] [Module R A]
    (M : Matrix l m A) :
    Matrix m n A →L[R] Matrix l n A where
  toLinearMap :=

end Matrix

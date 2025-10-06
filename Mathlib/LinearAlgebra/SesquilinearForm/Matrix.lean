/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.Hermitian

open Module LinearMap

variable {R M n m : Type*} [CommSemiring R] [StarRing R]
variable [AddCommMonoid M] [Module R M]
variable {σ : R →+* R} [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]
variable {B : M →ₛₗ[σ] M →ₗ[R] R} (b : Basis n R M)

section IsPosSemidef

lemma isSymm_iff_isHermitian_toMatrix : B.IsSymm ↔ (toMatrix₂ b b B).IsHermitian := by
  rw [isSymm_iff_basis f b, Matrix.IsHermitian.ext_iff]
  simp [Eq.comm]

end IsPosSemidef

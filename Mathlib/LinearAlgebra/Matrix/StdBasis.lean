/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.StdBasis

/-!
# Standard basis on matrices

## Main results

* `Basis.matrix`: extend a basis on `M` to the standard basis on `Matrix n m M`
-/

namespace Basis
variable {ι R M : Type*} (m n : Type*)
variable [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid M] [Module R M]

/-- The standard basis of `Matrix m n M` given a basis on `M`. -/
protected noncomputable def matrix (b : Basis ι R M) :
    Basis (m × n × ι) R (Matrix m n M) :=
  Basis.reindex (Pi.basis fun _ : m => Pi.basis fun _ : n => b)
    ((Equiv.sigmaEquivProd _ _).trans <| .prodCongr (.refl _) (Equiv.sigmaEquivProd _ _))
    |>.map (Matrix.ofLinearEquiv R)

variable {n m}

@[simp]
theorem matrix_apply (b : Basis ι R M) (i : m) (j : n) (k : ι) [DecidableEq m] [DecidableEq n] :
    b.matrix m n (i, j, k) = Matrix.stdBasisMatrix i j (b k) := by
  simp [Basis.matrix, Matrix.stdBasisMatrix_eq_of_single_single]

end Basis

namespace Matrix

variable (R : Type*) (m n : Type*) [Fintype m] [Finite n] [Semiring R]

/-- The standard basis of `Matrix m n R`. -/
noncomputable def stdBasis : Basis (m × n) R (Matrix m n R) :=
  Basis.reindex (Pi.basis fun _ : m => Pi.basisFun R n) (Equiv.sigmaEquivProd _ _)
    |>.map (ofLinearEquiv R)

variable {n m}

theorem stdBasis_eq_stdBasisMatrix (i : m) (j : n) [DecidableEq m] [DecidableEq n] :
    stdBasis R m n (i, j) = stdBasisMatrix i j (1 : R) := by
  simp [stdBasis, stdBasisMatrix_eq_of_single_single]

end Matrix

namespace Module.Free

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]

/-- The module of finite matrices is free. -/
instance matrix {m n : Type*} [Finite m] [Finite n] : Module.Free R (Matrix m n M) :=
  Module.Free.pi R _

end Module.Free

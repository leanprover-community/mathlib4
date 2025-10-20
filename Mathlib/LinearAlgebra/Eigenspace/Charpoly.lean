/-
Copyright (c) 2025 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvalues are the roots of the characteristic polynomial.

## Tags

eigenvalue, characteristic polynomial
-/

namespace Module

namespace End

open LinearMap

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

/--
The roots of the characteristic polynomial are exactly the eigenvalues.

`R` is required to be an integral domain, otherwise there is the counterexample:
R = M = Z/6Z, f(x) = 2x, v = 3, μ = 4, but p = X - 2.
-/
lemma hasEigenvalue_iff_isRoot_charpoly (f : End R M) (μ : R) :
    f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ := by
  rw [hasEigenvalue_iff, eigenspace_def, ← det_eq_zero_iff_ker_ne_bot, det_eq_sign_charpoly_coeff]
  simp [Polynomial.coeff_zero_eq_eval_zero, charpoly_sub_smul]

lemma mem_spectrum_iff_isRoot_charpoly (f : End K V) (μ : K) :
    μ ∈ spectrum K f ↔ f.charpoly.IsRoot μ := by
  rw [← hasEigenvalue_iff_mem_spectrum, hasEigenvalue_iff_isRoot_charpoly]

end End

end Module

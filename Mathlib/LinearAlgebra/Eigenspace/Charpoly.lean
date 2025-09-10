/-
Copyright (c) 2025 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Eigenvalues are the roots of the characteristic polynomial.

## Tags

eigenvalue, characteristic polynomial
-/

namespace Module

namespace End

open LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

lemma hasEigenvalue_iff_isRoot_charpoly (f : End K V) (μ : K) :
    f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ := by
  let b := Module.Free.chooseBasis K V
  rw [hasEigenvalue_iff_mem_spectrum, ← charpoly_toMatrix f b,
    Matrix.mem_spectrum_iff_isRoot_charpoly, spectrum_toMatrix f b]

end End

end Module

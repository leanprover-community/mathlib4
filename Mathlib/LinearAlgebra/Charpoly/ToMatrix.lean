/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Basis

#align_import linear_algebra.charpoly.to_matrix from "leanprover-community/mathlib"@"baab5d3091555838751562e6caad33c844bea15e"

/-!

# Characteristic polynomial

## Main result

* `LinearMap.charpoly_toMatrix f` : `charpoly f` is the characteristic polynomial of the matrix
of `f` in any basis.

-/


universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [Nontrivial R]

variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

open Matrix

noncomputable section

open Module.Free Polynomial Matrix

namespace LinearMap

section Basic

set_option maxHeartbeats 250000 in
/-- `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. -/
@[simp]
theorem charpoly_toMatrix {ι : Type w} [DecidableEq ι] [Fintype ι] (b : Basis ι R M) :
    (toMatrix b b f).charpoly = f.charpoly := by
  let A := toMatrix b b f
  let b' := chooseBasis R M
  let ι' := ChooseBasisIndex R M
  let A' := toMatrix b' b' f
  let e := Basis.indexEquiv b b'
  let φ := reindexLinearEquiv R R e e
  let φ₁ := reindexLinearEquiv R R e (Equiv.refl ι')
  let φ₂ := reindexLinearEquiv R R (Equiv.refl ι') (Equiv.refl ι')
  let φ₃ := reindexLinearEquiv R R (Equiv.refl ι') e
  let P := b.toMatrix b'
  let Q := b'.toMatrix b
  have hPQ : C.mapMatrix (φ₁ P) * C.mapMatrix (φ₃ Q) = 1 := by
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.map_mul,
      reindexLinearEquiv_mul R R, Basis.toMatrix_mul_toMatrix_flip,
      reindexLinearEquiv_one, ← RingHom.mapMatrix_apply, RingHom.map_one]
  calc
    A.charpoly = (reindex e e A).charpoly := (charpoly_reindex _ _).symm
    _ = det (scalar ι' X - C.mapMatrix (φ A)) := rfl
    _ = det (scalar ι' X - C.mapMatrix (φ (P * A' * Q))) := by
      rw [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
    _ = det (scalar ι' X - C.mapMatrix (φ₁ P * φ₂ A' * φ₃ Q)) := by
      rw [reindexLinearEquiv_mul, reindexLinearEquiv_mul]
    _ = det (scalar ι' X - C.mapMatrix (φ₁ P) * C.mapMatrix A' * C.mapMatrix (φ₃ Q)) := by simp
    _ = det (scalar ι' X * C.mapMatrix (φ₁ P) * C.mapMatrix (φ₃ Q) -
          C.mapMatrix (φ₁ P) * C.mapMatrix A' * C.mapMatrix (φ₃ Q)) := by
      rw [Matrix.mul_assoc ((scalar ι') X), hPQ, Matrix.mul_one]
    _ = det (C.mapMatrix (φ₁ P) * scalar ι' X * C.mapMatrix (φ₃ Q) -
          C.mapMatrix (φ₁ P) * C.mapMatrix A' * C.mapMatrix (φ₃ Q)) := by simp
    _ = det (C.mapMatrix (φ₁ P) * (scalar ι' X - C.mapMatrix A') * C.mapMatrix (φ₃ Q)) := by
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    _ = det (C.mapMatrix (φ₁ P)) * det (scalar ι' X - C.mapMatrix A') * det (C.mapMatrix (φ₃ Q)) :=
      by rw [det_mul, det_mul]
    _ = det (C.mapMatrix (φ₁ P)) * det (C.mapMatrix (φ₃ Q)) * det (scalar ι' X - C.mapMatrix A') :=
      by ring
    _ = det (scalar ι' X - C.mapMatrix A') := by
      rw [← det_mul, hPQ, det_one, one_mul]
    _ = f.charpoly := rfl
#align linear_map.charpoly_to_matrix LinearMap.charpoly_toMatrix

end Basic

end LinearMap

/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.TensorProduct.Finite


/-! # The characteristic polynomial of base change -/

@[simp]
lemma LinearMap.charpoly_baseChange {R M} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)
    (A) [CommRing A] [Algebra R A] :
    (f.baseChange A).charpoly = f.charpoly.map (algebraMap R A) := by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  let I := Module.Free.ChooseBasisIndex R M
  let b : Module.Basis I R M := Module.Free.chooseBasis R M
  rw [← f.charpoly_toMatrix b, ← (f.baseChange A).charpoly_toMatrix (b.baseChange A),
    ← Matrix.charpoly_map]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, ← Algebra.algebraMap_eq_smul_one]

lemma LinearMap.det_eq_sign_charpoly_coeff {R M} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) :
    LinearMap.det f = (-1) ^ Module.finrank R M * f.charpoly.coeff 0 := by
  nontriviality R
  rw [← LinearMap.det_toMatrix (Module.Free.chooseBasis R M), Matrix.det_eq_sign_charpoly_coeff,
    ← Module.finrank_eq_card_chooseBasisIndex, charpoly_def]

lemma LinearMap.det_baseChange {R M} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    {A} [CommRing A] [Algebra R A] (f : M →ₗ[R] M) :
    LinearMap.det (f.baseChange A) = algebraMap R A (LinearMap.det f) := by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  rw [LinearMap.det_eq_sign_charpoly_coeff, LinearMap.det_eq_sign_charpoly_coeff]
  simp

/-! Also see `LinearMap.trace_baseChange` in `Mathlib/LinearAlgebra/Trace` -/

/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.DualNumber
import Mathlib.Data.Matrix.Basic

/-!
# Matrices of dual numbers are isomorphic to dual numbers over matrices

Showing this for the more general case of `TrivSqZeroExt R M` would require an action between
`Matrix n n R` and `Matrix n n M`, which would risk causing diamonds.
-/


variable {R n : Type} [CommSemiring R] [Fintype n] [DecidableEq n]

open Matrix TrivSqZeroExt

/-- Matrices over dual numbers and dual numbers over matrices are isomorphic. -/
@[simps]
def Matrix.dualNumberEquiv : Matrix n n (DualNumber R) ≃ₐ[R] DualNumber (Matrix n n R) where
  toFun A := ⟨of fun i j => (A i j).fst, of fun i j => (A i j).snd⟩
  invFun d := of fun i j => (d.fst i j, d.snd i j)
  map_mul' A B := by
    ext
    · dsimp [mul_apply]
      simp_rw [fst_sum]
      rfl
    · simp_rw [snd_mul, smul_eq_mul, op_smul_eq_mul]
      simp only [mul_apply, snd_sum, DualNumber.snd_mul, snd_mk, of_apply, fst_mk, add_apply]
      rw [← Finset.sum_add_distrib]
  map_add' _ _ := TrivSqZeroExt.ext rfl rfl
  commutes' r := by
    simp_rw [algebraMap_eq_inl', algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.id.map_eq_self, algebraMap_eq_inl, ← diagonal_map (inl_zero R), map_apply, fst_inl,
      snd_inl]
    rfl

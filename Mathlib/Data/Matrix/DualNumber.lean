/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.DualNumber
import Mathlib.Data.Matrix.Basic

#align_import data.matrix.dual_number from "leanprover-community/mathlib"@"eb0cb4511aaef0da2462207b67358a0e1fe1e2ee"

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
  left_inv A := Matrix.ext fun i j => TrivSqZeroExt.ext rfl rfl
  right_inv d := TrivSqZeroExt.ext (Matrix.ext fun i j => rfl) (Matrix.ext fun i j => rfl)
  map_mul' A B := by
    ext
    -- ⊢ fst (Equiv.toFun { toFun := fun A => (↑of fun i j => fst (A i j), ↑of fun i  …
    · dsimp [mul_apply]
      -- ⊢ fst (Finset.sum Finset.univ fun j => A i✝ j * B j x✝) = Finset.sum Finset.un …
      simp_rw [fst_sum]
      -- ⊢ (Finset.sum Finset.univ fun i => fst (A i✝ i * B i x✝)) = Finset.sum Finset. …
      rfl
      -- 🎉 no goals
    · simp_rw [snd_mul, smul_eq_mul, op_smul_eq_mul]
      -- ⊢ snd (↑of fun i j => fst ((A * B) i j), ↑of fun i j => snd ((A * B) i j)) i✝  …
      simp [mul_apply, snd_sum, snd_mul]
      -- ⊢ (Finset.sum Finset.univ fun x => fst (A i✝ x) * snd (B x x✝) + snd (A i✝ x)  …
      rw [← Finset.sum_add_distrib]
      -- 🎉 no goals
  map_add' A B := TrivSqZeroExt.ext rfl rfl
  commutes' r := by
    simp_rw [algebraMap_eq_inl', algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.id.map_eq_self, algebraMap_eq_inl, ← diagonal_map (inl_zero R), map_apply, fst_inl,
      snd_inl]
    rfl
    -- 🎉 no goals
#align matrix.dual_number_equiv Matrix.dualNumberEquiv

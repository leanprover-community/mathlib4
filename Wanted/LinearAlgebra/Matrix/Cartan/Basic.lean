/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

namespace CartanMatrix

variable (n : ℕ)

theorem_wanted isFiniteCartan_a : (A n).IsFiniteCartan

theorem_wanted isFiniteCartan_b : (B n).IsFiniteCartan

theorem_wanted isFiniteCartan_c : (C n).IsFiniteCartan

theorem_wanted isFiniteCartan_d : (D n).IsFiniteCartan

theorem_wanted isFiniteCartan_e₆ : (E 6).IsFiniteCartan

theorem_wanted isFiniteCartan_e₇ : (E 7).IsFiniteCartan

theorem_wanted isFiniteCartan_e₈ : (E 8).IsFiniteCartan

theorem_wanted isFiniteCartan_f₄ : F₄.IsFiniteCartan

theorem isFiniteCartan_g₂ : G₂.IsFiniteCartan where
  diag := by simp
  offDiag_nonpos := by simp [G₂]
  zero_comm := by simp [G₂]
  exists_posDef := by
    use ![1, 3]
    have h : Matrix.diagonal ![1, 3] * G₂ = !![2, -3; -3, 6] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    simp only [h, Fin.forall_fin_two, Matrix.cons_val_zero, zero_lt_one, true_and,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.ofNat_pos, Int.reduceNeg]
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · intro x hx
      have h : star x ⬝ᵥ !![2, -3; -3, 6].mulVec x =
        2 * x 0 ^ 2 - 6 * x 0 * x 1 + 6 * x 1 ^ 2 := by
        simp [show Matrix.vecHead x = x 0 by rfl,
          show Matrix.vecHead (Matrix.vecTail x) = x 1 by rfl]
        ring
      rw [h]
      by_cases h : x 1 = 0
      · have h₀ : x 0 ≠ 0 := by
          contrapose hx
          ext i
          fin_cases i <;> simp_all
        simp [h, sq_pos_iff.mpr h₀]
      · nlinarith [sq_pos_iff.mpr h, sq_nonneg (2 * x 0 - 3 * x 1)]

end CartanMatrix

theorem_wanted Matrix.IsFiniteCartan.exists_A_or_B_or_C_or_D_or_E_or_F_or_G
    {l : Type*} [Fintype l] [DecidableEq l]
    {M : Matrix l l ℤ} (hM : M.IsFiniteCartan) (hM' : M.IsIndecomposable) :
    (∃ n e, M.reindex e e = CartanMatrix.A n) ∨
    (∃ n e, M.reindex e e = CartanMatrix.B n) ∨
    (∃ n e, M.reindex e e = CartanMatrix.C n) ∨
    (∃ n e, M.reindex e e = CartanMatrix.D n) ∨
    (∃ e, M.reindex e e = CartanMatrix.E 6) ∨
    (∃ e, M.reindex e e = CartanMatrix.E 7) ∨
    (∃ e, M.reindex e e = CartanMatrix.E 8) ∨
    (∃ e, M.reindex e e = CartanMatrix.F₄) ∨
    (∃ e, M.reindex e e = CartanMatrix.G₂)

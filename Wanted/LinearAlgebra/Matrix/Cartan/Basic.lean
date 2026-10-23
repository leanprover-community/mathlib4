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

theorem_wanted isFiniteCartan_e₇ : (E 7).IsFiniteCartan

theorem_wanted isFiniteCartan_e₈ : (E 8).IsFiniteCartan

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

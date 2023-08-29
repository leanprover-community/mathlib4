/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.CharP.Basic

#align_import data.matrix.char_p from "leanprover-community/mathlib"@"168ad7fc5d8173ad38be9767a22d50b8ecf1cd00"

/-!
# Matrices in prime characteristic
-/


open Matrix

variable {n : Type*} [Fintype n] {R : Type*} [Ring R]

instance Matrix.charP [DecidableEq n] [Nonempty n] (p : ℕ) [CharP R p] : CharP (Matrix n n R) p :=
  ⟨by
    intro k
    -- ⊢ ↑k = 0 ↔ p ∣ k
    rw [← CharP.cast_eq_zero_iff R p k, ← Nat.cast_zero, ← map_natCast <| scalar n]
    -- ⊢ ↑(scalar n) ↑k = ↑0 ↔ ↑k = 0
    convert @scalar_inj n _ _ _ _ _ (@Nat.cast R NonAssocSemiring.toNatCast k) 0
    -- ⊢ ↑0 = ↑(scalar n) 0
    simp⟩
    -- 🎉 no goals
#align matrix.char_p Matrix.charP

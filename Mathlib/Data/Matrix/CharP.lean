/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module data.matrix.char_p
! leanprover-community/mathlib commit 168ad7fc5d8173ad38be9767a22d50b8ecf1cd00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.CharP.Basic

/-!
# Matrices in prime characteristic
-/


open Matrix

variable {n : Type _} [Fintype n] {R : Type _} [Ring R]

instance Matrix.charP [DecidableEq n] [Nonempty n] (p : ℕ) [CharP R p] : CharP (Matrix n n R) p :=
  ⟨by
    intro k
    rw [← CharP.cast_eq_zero_iff R p k, ← Nat.cast_zero, ← map_natCast <| scalar n]
    convert @scalar_inj n _ _ _ _ _ (@Nat.cast R NonAssocSemiring.toNatCast k) 0
    simp⟩
#align matrix.char_p Matrix.charP

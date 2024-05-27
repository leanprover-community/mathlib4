/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Matrix.Basic

#align_import data.matrix.char_p from "leanprover-community/mathlib"@"168ad7fc5d8173ad38be9767a22d50b8ecf1cd00"

/-!
# Matrices in prime characteristic

In this file we prove that matrices over a ring of characteristic `p`
with nonempty index type have the same characteristic.
-/


open Matrix

variable {n : Type*} {R : Type*} [AddMonoidWithOne R]

instance Matrix.charP [DecidableEq n] [Nonempty n] (p : ℕ) [CharP R p] :
    CharP (Matrix n n R) p where
  cast_eq_zero_iff' k := by simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
    CharP.cast_eq_zero_iff R p k, forall_const]
#align matrix.char_p Matrix.charP

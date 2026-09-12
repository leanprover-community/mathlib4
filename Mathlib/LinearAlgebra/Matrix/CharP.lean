/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Matrix.Diagonal

/-!
# Matrices in prime characteristic

In this file we prove that matrices over a ring of characteristic `p`
with nonempty index type have the same characteristic.
-/

public section


namespace Matrix

variable {n : Type*} {R : Type*} [DecidableEq n] [Nonempty n] [AddMonoidWithOne R]

instance instCharP (p : ℕ) [CharP R p] : CharP (Matrix n n R) p where
  cast_eq_zero_iff k := by simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
    CharP.cast_eq_zero_iff R p k, forall_const]

instance instCharZero [CharZero R] : CharZero (Matrix n n R) where
  cast_injective _ _ h := by
    inhabit n
    simpa [natCast_apply] using congr($h default default)

instance instExpChar : ∀ {p} [ExpChar R p], ExpChar (Matrix n n R) p
  | _, @ExpChar.zero _ _ _ => .zero
  | _, @ExpChar.prime _ _ _ _ _ => .prime ‹_›

end Matrix

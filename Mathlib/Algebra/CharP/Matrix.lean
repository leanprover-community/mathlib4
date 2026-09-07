/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.CharP.Pi
public import Mathlib.Data.Matrix.Basic

/-!
# Characteristic of matrices
-/

@[expose] public section

universe u v

namespace Matrix
variable {m R : Type*}

theorem instCharZero [Nonempty m] [DecidableEq m] [AddMonoidWithOne R] [CharZero R] :
    CharZero (Matrix m m R) where
  cast_injective _ _ h := by
    inhabit m
    have := congrFun₂ h default default
    simp_rw [Matrix.natCast_apply, ite_true] at this
    exact Nat.cast_injective this

theorem instCharP {p} [Nonempty m] [DecidableEq m] [AddMonoidWithOne R] [CharP R p] :
    CharP (Matrix m m R) p where
  cast_eq_zero_iff n := by
    inhabit m
    simp_rw [← Matrix.ext_iff, Matrix.natCast_apply, ← CharP.cast_eq_zero_iff (R := R)]
    constructor
    · intro h
      simpa using h default default
    · simp

end Matrix

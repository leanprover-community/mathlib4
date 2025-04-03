/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Group action on fields
-/

variable {M} [Monoid M] {F} [DivisionRing F]

/-- Note that `smul_inv'` refers to the group case, and `smul_inv` has an additional inverse
on `x`. -/
@[simp]
theorem smul_inv'' [MulSemiringAction M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
  map_inv₀ (MulSemiringAction.toRingHom M F x) _
#align smul_inv'' smul_inv''

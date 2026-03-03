/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Idempotent elements of a group with zero
-/

@[expose] public section

assert_not_exists Ring

variable {M₀ : Type*}

namespace IsIdempotentElem
section MulZeroClass
variable [MulZeroClass M₀]

lemma zero : IsIdempotentElem (0 : M₀) := mul_zero _

instance : Zero { p : M₀ // IsIdempotentElem p } where zero := ⟨0, zero⟩

@[simp] lemma coe_zero : ↑(0 : { p : M₀ // IsIdempotentElem p }) = (0 : M₀) := rfl

end MulZeroClass

section CancelMonoidWithZero
variable {G₀ : Type*} [MonoidWithZero G₀] [IsLeftCancelMulZero G₀]

@[simp]
lemma iff_eq_zero_or_one {p : G₀} : IsIdempotentElem p ↔ p = 0 ∨ p = 1 where
  mp h := or_iff_not_imp_left.mpr fun hp ↦ mul_left_cancel₀ hp (h.trans (mul_one p).symm)
  mpr h := h.elim (fun hp => hp.symm ▸ zero) fun hp => hp.symm ▸ one

end CancelMonoidWithZero
end IsIdempotentElem

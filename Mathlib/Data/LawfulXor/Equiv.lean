/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

module
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Algebra.Group.End

/-!
# LawfulXor equivalences
-/

@[expose] public section

namespace Equiv

open LawfulXor

variable {α β : Type*} [XorOp α] [Zero α] [LawfulXor α] {a b c : α}

/-- `XorOp.xor` as a permutation. -/
@[simps! apply] protected def xor (a : α) : Perm α where
  toFun := (a ^^^ ·)
  invFun := (a ^^^ ·)
  left_inv := xor_cancel_left a
  right_inv := xor_cancel_left a

@[simp] theorem xor_symm : (Equiv.xor a).symm = Equiv.xor a := rfl

theorem xor_involutive (a : α) : Function.Involutive (Equiv.xor a) := xor_right_involutive a

@[simp] theorem xor_zero : Equiv.xor (0 : α) = 1 := Equiv.ext zero_xor

@[simp] theorem xor_eq_one_iff : Equiv.xor a = 1 ↔ a = 0 :=
  Equiv.coe_inj.symm.trans xor_left_eq_id_iff

theorem isFixedPt_xor : Function.IsFixedPt (Equiv.xor a) b ↔ a = 0 := isFixedPt_xor_left_iff

@[simp] theorem xor_trans_xor : (Equiv.xor b).trans (Equiv.xor a) = Equiv.xor (a ^^^ b) :=
  Equiv.ext <| (.symm <| xor_assoc a b ·)

end Equiv

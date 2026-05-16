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

variable {α β : Type*} [XorOp α] [Zero α] [LawfulXor α] (a b c : α)

/-- `XorOp.xor` as a permutation. -/
@[simps!] protected def xor (a : α) : Perm α where
  toFun := (· ^^^ a)
  invFun := (a ^^^ ·)
  left_inv := xor_xor_cancel_comm_assoc a
  right_inv := xor_xor_cancel_comm a

theorem xor_symm : (Equiv.xor a).symm = Equiv.xor a := Equiv.ext fun _ => xor_comm _ _

theorem xor_involutive : Function.Involutive (Equiv.xor a) := xor_left_involutive a

theorem xor_zero_apply : Equiv.xor 0 a = a := xor_zero a

@[simp] theorem xor_zero : Equiv.xor (0 : α) = 1 := Equiv.ext xor_zero_apply

@[simp] theorem xor_eq_one_iff : Equiv.xor a = 1 ↔ a = 0 :=
  Equiv.coe_inj.symm.trans (xor_right_id_iff a)

theorem isFixedPt_xor : Function.IsFixedPt (Equiv.xor a) b ↔ a = 0 :=
  isFixedPt_xor_right_iff a b

@[simp] theorem not_isFixedPt_xor_of_neZero [NeZero a] : ¬ Function.IsFixedPt (Equiv.xor a) b :=
  not_isFixedPt_xor_right_of_neZero a b

theorem xor_apply_comm : Equiv.xor a b = Equiv.xor b a := xor_comm b a

theorem xor_apply_xor_apply : Equiv.xor a (Equiv.xor b c) = Equiv.xor (Equiv.xor a b) c :=
  xor_assoc _ _ _

@[simp] theorem xor_trans_xor : (Equiv.xor b).trans (Equiv.xor a) = Equiv.xor (Equiv.xor a b) :=
  Equiv.ext <| xor_apply_xor_apply a b

theorem xor_self_apply : Equiv.xor a a = 0 := xor_self a

theorem xor_apply_eq_zero_iff : Equiv.xor a b = 0 ↔ a = b := by
  simp [xor_eq_zero_iff, eq_comm]

end Equiv

/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

module
public import Mathlib.Logic.Function.Basic

/-!
# The `LawfulXor` typeclass

This file generalizes basic lemmas about the `^^^` operator across numeric types.
-/

@[expose] public section

/-- A typeclass indicating that the xor operation, `^^^`, is lawful. -/
class LawfulXor (α : Type*) [XorOp α] [Zero α] where
  xor_assoc (a b c : α) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c)
  xor_self (a : α) : a ^^^ a = 0
  xor_zero (a : α) : a ^^^ 0 = a
  xor_comm (a b : α) : a ^^^ b = b ^^^ a

export LawfulXor (xor_assoc xor_self xor_zero xor_comm)

variable {α : Type*} [XorOp α] [Zero α] [LawfulXor α]

attribute [simp] xor_zero LawfulXor.xor_self

@[simp]
theorem zero_xor (a : α) : 0 ^^^ a = a := by rw [LawfulXor.xor_comm, xor_zero]

instance : Std.Commutative (α := α) XorOp.xor where comm := xor_comm
instance : Std.Associative (α := α) XorOp.xor where assoc := xor_assoc

instance : Std.LawfulCommIdentity (α := α) XorOp.xor 0 where
  left_id := zero_xor
  right_id := xor_zero

@[simp]
theorem xor_cancel_right (a b : α) : (a ^^^ b) ^^^ b = a := by
  rw [xor_assoc, LawfulXor.xor_self, xor_zero]

@[simp]
theorem xor_cancel_left (a b : α) : a ^^^ (a ^^^ b) = b := by
  rw [← xor_assoc, LawfulXor.xor_self, zero_xor]

instance : LawfulXor Nat where
  xor_assoc := Nat.xor_assoc
  xor_comm := Nat.xor_comm
  xor_self := Nat.xor_self
  xor_zero := Nat.xor_zero

instance {w : Nat} : LawfulXor (BitVec w) where
  xor_assoc := BitVec.xor_assoc
  xor_comm := BitVec.xor_comm
  xor_self _ := BitVec.xor_self
  xor_zero _ := BitVec.xor_zero

instance : LawfulXor UInt8 where
  xor_assoc := UInt8.xor_assoc
  xor_comm := UInt8.xor_comm
  xor_self _ := UInt8.xor_self
  xor_zero _ := UInt8.xor_zero

instance : LawfulXor UInt16 where
  xor_assoc := UInt16.xor_assoc
  xor_comm := UInt16.xor_comm
  xor_self _ := UInt16.xor_self
  xor_zero _ := UInt16.xor_zero

instance : LawfulXor UInt32 where
  xor_assoc := UInt32.xor_assoc
  xor_comm := UInt32.xor_comm
  xor_self _ := UInt32.xor_self
  xor_zero _ := UInt32.xor_zero

instance : LawfulXor UInt64 where
  xor_assoc := UInt64.xor_assoc
  xor_comm := UInt64.xor_comm
  xor_self _ := UInt64.xor_self
  xor_zero _ := UInt64.xor_zero

instance : LawfulXor USize where
  xor_assoc := USize.xor_assoc
  xor_comm := USize.xor_comm
  xor_self _ := USize.xor_self
  xor_zero _ := USize.xor_zero

instance : LawfulXor Int8 where
  xor_assoc := Int8.xor_assoc
  xor_comm := Int8.xor_comm
  xor_self _ := Int8.xor_self
  xor_zero _ := Int8.xor_zero

instance : LawfulXor Int16 where
  xor_assoc := Int16.xor_assoc
  xor_comm := Int16.xor_comm
  xor_self _ := Int16.xor_self
  xor_zero _ := Int16.xor_zero

instance : LawfulXor Int32 where
  xor_assoc := Int32.xor_assoc
  xor_comm := Int32.xor_comm
  xor_self _ := Int32.xor_self
  xor_zero _ := Int32.xor_zero

instance : LawfulXor Int64 where
  xor_assoc := Int64.xor_assoc
  xor_comm := Int64.xor_comm
  xor_self _ := Int64.xor_self
  xor_zero _ := Int64.xor_zero

instance : LawfulXor ISize where
  xor_assoc := ISize.xor_assoc
  xor_comm := ISize.xor_comm
  xor_self _ := ISize.xor_self
  xor_zero _ := ISize.xor_zero

lemma xor_right_involutive (a : α) : Function.Involutive (a ^^^ ·) := xor_cancel_left a

lemma xor_left_involutive (a : α) : Function.Involutive (· ^^^ a) := (xor_cancel_right · a)

lemma xor_eq_iff_left_eq (a b c : α) :
    a ^^^ b = c ↔ a = c ^^^ b := xor_left_involutive _ |>.eq_iff

lemma xor_eq_iff_right_eq (a b c : α) :
    a ^^^ b = c ↔ b = a ^^^ c := xor_right_involutive _ |>.eq_iff

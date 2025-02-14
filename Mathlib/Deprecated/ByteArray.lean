/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.ByteSubarray -- Only needed for the deprecation.
import Mathlib.Init

/-!
# Main result
Introduce main properties of `Up` (well-ordered relation for "upwards" induction on `ℕ`) and of
 `ByteArray`

This entire file has been deprecated on 2024-08-19 in favour of `ByteSubarray` in Batteries.
-/

set_option linter.deprecated false

namespace Nat

/-- A well-ordered relation for "upwards" induction on the natural numbers up to some bound `ub`. -/
@[deprecated "No deprecation message was provided." (since := "2024-08-19")]
def Up (ub a i : Nat) := i < a ∧ i < ub

theorem Up.next {ub i} (h : i < ub) : Up ub (i+1) i := ⟨Nat.lt_succ_self _, h⟩

theorem Up.WF (ub) : WellFounded (Up ub) :=
  Subrelation.wf (h₂ := (measure (ub - ·)).wf) fun ⟨ia, iu⟩ ↦ Nat.sub_lt_sub_left iu ia

/-- A well-ordered relation for "upwards" induction on the natural numbers up to some bound `ub`. -/
@[deprecated "No deprecation message was provided." (since := "2024-08-19")]
def upRel (ub : Nat) : WellFoundedRelation Nat := ⟨Up ub, Up.WF ub⟩

end Nat

/-- A terminal byte slice, a suffix of a byte array. -/
@[deprecated "No deprecation message was provided." (since := "2024-08-19")]
structure ByteSliceT := (arr : ByteArray) (off : Nat)

namespace ByteSliceT

/-- The number of elements in the byte slice. -/
@[inline] def size (self : ByteSliceT) : Nat := self.arr.size - self.off

/-- Index into a byte slice. The `getOp` function allows the use of the `buf[i]` notation. -/
@[inline] def getOp (self : ByteSliceT) (idx : Nat) : UInt8 := self.arr.get! (self.off + idx)

end ByteSliceT

/-- Convert a byte array into a terminal slice. -/
def ByteArray.toSliceT (arr : ByteArray) : ByteSliceT := ⟨arr, 0⟩

/-- A byte slice, given by a backing byte array, and an offset and length. -/
@[deprecated Batteries.ByteSubarray (since := "2024-08-19")]
structure ByteSlice := (arr : ByteArray) (off len : Nat)

namespace ByteSlice

/-- Convert a byte slice into an array, by copying the data if necessary. -/
def toArray : ByteSlice → ByteArray
  | ⟨arr, off, len⟩ => arr.extract off len

/-- Index into a byte slice. The `getOp` function allows the use of the `buf[i]` notation. -/
@[inline] def getOp (self : ByteSlice) (idx : Nat) : UInt8 := self.arr.get! (self.off + idx)

universe u v

/-- The inner loop of the `forIn` implementation for byte slices. -/
@[deprecated "No deprecation message was provided." (since := "2024-08-19")]
def forIn.loop {m : Type u → Type v} {β : Type u} [Monad m] (f : UInt8 → β → m (ForInStep β))
    (arr : ByteArray) (off _end : Nat) (i : Nat) (b : β) : m β :=
  if h : i < _end then do
    match ← f (arr.get! i) b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => have := Nat.Up.next h; loop f arr off _end (i+1) b
  else pure b

@[deprecated "No deprecation message was provided." (since := "2024-08-19")]
instance {m : Type u → Type v} : ForIn m ByteSlice UInt8 :=
  ⟨fun ⟨arr, off, len⟩ b f ↦ forIn.loop f arr off (off + len) off b⟩

end ByteSlice

/-- Convert a terminal byte slice into a regular byte slice. -/
def ByteSliceT.toSlice : ByteSliceT → ByteSlice
  | ⟨arr, off⟩ => ⟨arr, off, arr.size - off⟩

/-- Convert a byte array into a byte slice. -/
def ByteArray.toSlice (arr : ByteArray) : ByteSlice := ⟨arr, 0, arr.size⟩

/-- Convert a byte slice into a string. This does not handle non-ASCII characters correctly:
every byte will become a unicode character with codepoint < 256. -/
def ByteSlice.toString (bs : ByteSlice) : String := Id.run do
  let mut s := ""
  for c in bs do s := s.push (Char.ofUInt8 c)
  s

instance : ToString ByteSlice where
  toString bs := Id.run do
    let mut s := ""
    for c in bs do s := s.push (Char.ofUInt8 c)
    s

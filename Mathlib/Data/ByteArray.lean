/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Char

set_option autoImplicit true

namespace Nat

/- Up -/

/-- A well-ordered relation for "upwards" induction on the natural numbers up to some bound `ub`. -/
def Up (ub a i : ℕ) := i < a ∧ i < ub

lemma Up.next {ub i} (h : i < ub) : Up ub (i+1) i := ⟨Nat.lt_succ_self _, h⟩

lemma Up.WF (ub) : WellFounded (Up ub) :=
  Subrelation.wf (h₂ := (measure (ub - ·)).wf) fun ⟨ia, iu⟩ ↦ Nat.sub_lt_sub_left iu ia

/-- A well-ordered relation for "upwards" induction on the natural numbers up to some bound `ub`. -/
def upRel (ub : ℕ) : WellFoundedRelation Nat := ⟨Up ub, Up.WF ub⟩

end Nat

/-- A terminal byte slice, a suffix of a byte array. -/
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
structure ByteSlice := (arr : ByteArray) (off len : Nat)

namespace ByteSlice

/-- Convert a byte slice into an array, by copying the data if necessary. -/
def toArray : ByteSlice → ByteArray
  | ⟨arr, off, len⟩ => arr.extract off len

/-- Index into a byte slice. The `getOp` function allows the use of the `buf[i]` notation. -/
@[inline] def getOp (self : ByteSlice) (idx : Nat) : UInt8 := self.arr.get! (self.off + idx)


/-- The inner loop of the `forIn` implementation for byte slices. -/
def forIn.loop [Monad m] (f : UInt8 → β → m (ForInStep β))
    (arr : ByteArray) (off _end : Nat) (i : Nat) (b : β) : m β :=
  if h : i < _end then do
    match ← f (arr.get! i) b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => have := Nat.Up.next h; loop f arr off _end (i+1) b
  else pure b
termination_by _end - i

instance : ForIn m ByteSlice UInt8 :=
  ⟨fun ⟨arr, off, len⟩ b f ↦ forIn.loop f arr off (off + len) off b⟩

end ByteSlice

/-- Convert a terminal byte slice into a regular byte slice. -/
def ByteSliceT.toSlice : ByteSliceT → ByteSlice
  | ⟨arr, off⟩ => ⟨arr, off, arr.size - off⟩

/-- Convert a byte array into a byte slice. -/
def ByteArray.toSlice (arr : ByteArray) : ByteSlice := ⟨arr, 0, arr.size⟩

/-- Convert a string of assumed-ASCII characters into a byte array.
(If any characters are non-ASCII they will be reduced modulo 256.) -/
def String.toAsciiByteArray (s : String) : ByteArray :=
  let rec loop (p : Pos) (out : ByteArray) : ByteArray :=
    if h : s.atEnd p then out else
    let c := s.get p
    have : utf8ByteSize s - (next s p).byteIdx < utf8ByteSize s - p.byteIdx :=
      Nat.sub_lt_sub_left (Nat.lt_of_not_le <| mt decide_eq_true h)
        (Nat.lt_add_of_pos_right (String.csize_pos _))
    loop (s.next p) (out.push c.toUInt8)
    termination_by utf8ByteSize s - p.byteIdx
  loop 0 ByteArray.empty

/-- Convert a byte slice into a string. This does not handle non-ASCII characters correctly:
every byte will become a unicode character with codepoint < 256. -/
def ByteSlice.toString (bs : ByteSlice) : String := Id.run do
  let mut s := ""
  for c in bs do s := s.push c.toChar
  s

instance : ToString ByteSlice where
  toString bs := Id.run do
    let mut s := ""
    for c in bs do s := s.push c.toChar
    s

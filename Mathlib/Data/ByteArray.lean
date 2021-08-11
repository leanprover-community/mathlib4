import Mathlib.Data.Nat.Basic
import Mathlib.Data.Char
import Mathlib.Data.UInt

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

/-- Implementation of `forIn.loop`. -/
partial def forIn.loop.impl [Monad m] (f : UInt8 → β → m (ForInStep β))
  (arr : ByteArray) (off _end : Nat) (i : Nat) (b : β) : m β :=
  if i < _end then do
    match ← f (arr.get! i) b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => impl f arr off _end (i+1) b
  else b

set_option codegen false in
/-- The inner loop of the `forIn` implementation for byte slices. It is defined twice:
this version is the model, while `forIn.loop.impl` is the version used for code generation. -/
@[implementedBy forIn.loop.impl]
def forIn.loop [Monad m] (f : UInt8 → β → m (ForInStep β))
  (arr : ByteArray) (off _end : Nat) (i : Nat) (b : β) : m β := do
(Nat.Up.WF _end).fix (x := i) (C := fun _ => ∀ b, m β) (b := b)
  fun i IH b =>
    if h : i < _end then do
      let b ← f (arr.get! i) b
      match b with
      | ForInStep.done b => pure b
      | ForInStep.yield b => IH (i+1) (Nat.Up.next h) b
    else b

instance : ForIn m ByteSlice UInt8 :=
  ⟨fun ⟨arr, off, len⟩ b f => forIn.loop f arr off (off + len) off b⟩

end ByteSlice

/-- Convert a terminal byte slice into a regular byte slice. -/
def ByteSliceT.toSlice : ByteSliceT → ByteSlice
| ⟨arr, off⟩ => ⟨arr, off, arr.size - off⟩

/-- Convert a byte array into a byte slice. -/
def ByteArray.toSlice (arr : ByteArray) : ByteSlice := ⟨arr, 0, arr.size⟩

/-- Implementation of `String.toAsciiByteArray.loop`. -/
partial def String.toAsciiByteArray.loop.impl
  (s : String) (out : ByteArray) (p : Pos) : ByteArray :=
  if s.atEnd p then out else
  let c := s.get p
  impl s (out.push c.toUInt8) (s.next p)

set_option codegen false in
/-- The inner loop of  `String.toAsciiByteArray`. Because it uses well founded recursion, we have
to write the compiler version of the implementation separately from the version used for
reasoning inside lean. -/
@[implementedBy String.toAsciiByteArray.loop.impl]
def String.toAsciiByteArray.loop (s : String) (out : ByteArray) (p : Pos) : ByteArray :=
(Nat.Up.WF (utf8ByteSize s)).fix (x := p) (C := fun _ => ∀ out, ByteArray) (out := out)
  fun p IH i =>
    if h : s.atEnd p then out else
    let c := s.get p
    IH (s.next p) (out := out.push c.toUInt8)
      ⟨Nat.lt_add_of_pos_right (String.csize_pos _),
      Nat.lt_of_not_le (mt decide_eq_true h)⟩

/-- Convert a string of assumed-ASCII characters into a byte array.
(If any characters are non-ASCII they will be reduced modulo 256.) -/
def String.toAsciiByteArray (s : String) : ByteArray :=
  String.toAsciiByteArray.loop s ByteArray.empty 0

/-- Convert a byte slice into a string. This does not handle non-ASCII characters correctly:
every byte will become a unicode character with codepoint < 256. -/
def ByteSlice.toString (bs : ByteSlice) : String := do
  let mut s := ""
  for c in bs do s := s.push c.toChar
  s

instance : ToString ByteSlice where
  toString bs := do
    let mut s := ""
    for c in bs do s := s.push c.toChar
    s

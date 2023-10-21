/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Alex Keizer, Abdalrhman M Mohamed
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Defs
import Std.Data.BitVec


/-!
# Basic operations on bitvectors
Std has defined bitvector of length `w` as `Fin (2^w)`.
Here we define a few more operations on these bitvectors

## Main definitions

* `Std.BitVec.sgt`: Signed greater-than comparison of bitvectors
* `Std.BitVec.sge`: Signed greater-equals comparison of bitvectors
* `Std.BitVec.ugt`: Unsigned greater-than comparison of bitvectors
* `Std.BitVec.uge`: Unsigned greater-equals comparison of bitvectors
* `Std.BitVec.ofLEList`: Turn a little-endian list of Booleans into a bitvector
* `Std.BitVec.ofBEList`: Turn a big-endian list of Booleans into a bitvector

-/

variable {w v : Nat}

namespace Std.BitVec

#align bitvec Std.BitVec
#align bitvec.zero Std.BitVec.zero
#align bitvec.cong Std.BitVec.cast
#align bitvec.append Std.BitVec.append
#align bitvec.shl Std.BitVec.shiftLeft
#align bitvec.ushr Std.BitVec.ushiftRight
#align bitvec.sshr Std.BitVec.sshiftRight
#align bitvec.not Std.BitVec.not
#align bitvec.and Std.BitVec.and
#align bitvec.or Std.BitVec.or
#align bitvec.xor Std.BitVec.xor
#align bitvec.neg Std.BitVec.neg
#align bitvec.add Std.BitVec.add
#align bitvec.sub Std.BitVec.sub
#align bitvec.mul Std.BitVec.mul
#align bitvec.ult Std.BitVec.ult
#align bitvec.ule Std.BitVec.ule
#align bitvec.slt Std.BitVec.slt
#align bitvec.sle Std.BitVec.sle
#align bitvec.of_nat Std.BitVec.ofNat
#align bitvec.add_lsb Nat.bit
#align bitvec.to_nat Std.BitVec.toNat
#align bitvec.of_fin Std.BitVec.ofFin
#align bitvec.to_fin Std.BitVec.toFin
#align bitvec.to_int Std.BitVec.toInt

#noalign bitvec.one
#noalign bitvec.adc
#noalign bitvec.sbb
#noalign bitvec.uborrow
#noalign bitvec.sborrow
#noalign bitvec.bits_to_nat



/-!
## Bitwise operations
-/

/-- Signed greater than for bitvectors. -/
protected def sgt (x y : BitVec w) : Prop := BitVec.slt y x
#align bitvec.sgt Std.BitVec.sgt

/-- Signed greater than or equal to for bitvectors. -/
protected def sge (x y : BitVec w) : Prop := BitVec.sle y x
#align bitvec.sge Std.BitVec.sge

/-- Unsigned greater than for bitvectors. -/
protected def ugt (x y : BitVec w) : Prop := BitVec.ult y x
#align bitvec.ugt Std.BitVec.ugt

/-- Signed greater than or equal to for bitvectors. -/
protected def uge (x y : BitVec w) : Prop := BitVec.ule y x
#align bitvec.uge Std.BitVec.uge

/--
  Convert a list of booleans to a bitvector, using little-endian bit-order.
  That is, we take the head of the list to be the least significant bit
-/
def ofLEList (bs : List Bool) : BitVec bs.length :=
  ⟨Nat.ofBits (λ i => bs[i]!) 0 bs.length, @Nat.ofBits_lt _ (bs.length)⟩

/--
  Convert a list of booleans to a bitvector, using big-endian bit order.
  That is, we take the head of the list to be the most significant bit
-/
def ofBEList (bs : List Bool) : BitVec bs.length :=
  (ofLEList bs.reverse).cast (List.length_reverse ..)



end Std.BitVec

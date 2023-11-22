/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich, Harun Khan, Alex Keizer, Abdalrhman M Mohamed
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Defs
import Std.Data.BitVec

#align_import data.bitvec.core from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# Basic operations on bitvectors

Std has defined bitvector of length `w` as `Fin (2^w)`.
Here we define a few more operations on these bitvectors

## Main definitions

* `Std.BitVec.sgt`: Signed greater-than comparison of bitvectors
* `Std.BitVec.sge`: Signed greater-equals comparison of bitvectors
* `Std.BitVec.ugt`: Unsigned greater-than comparison of bitvectors
* `Std.BitVec.uge`: Unsigned greater-equals comparison of bitvectors

-/

variable {w v : Nat}

namespace Std.BitVec

#align bitvec Std.BitVec
#align bitvec.zero Std.BitVec.zero

/-!
## Constants
-/

/-- The bitvector representing `1`.
    That is, the bitvector with least-significant bit `1` and all other bits `0` -/
@[simp] abbrev one (w : ℕ) : BitVec w := 1
#align bitvec.one Std.BitVec.one

#align bitvec.cong Std.BitVec.cast
#align bitvec.append Std.BitVec.append
#align bitvec.shl Std.BitVec.shiftLeft
#align bitvec.ushr Std.BitVec.ushiftRight
#align bitvec.sshr Std.BitVec.sshiftRight

/-! ### Bitwise operations -/

#align bitvec.not Std.BitVec.not
#align bitvec.and Std.BitVec.and
#align bitvec.or Std.BitVec.or
#align bitvec.xor Std.BitVec.xor

/-! ### Arithmetic operators -/

#align bitvec.neg Std.BitVec.neg
/-- Add with carry (no overflow) -/
def adc {n} (x y : BitVec n) (c : Bool) : BitVec (n+1) :=
  ofFin (x.toNat + y.toNat + c.toNat)
#align bitvec.adc Std.BitVec.adc

#align bitvec.add Std.BitVec.add

/-- Subtract with borrow -/
def sbb {n} (x y : BitVec n) (b : Bool) : Bool × BitVec n :=
  let y := y + ofFin b.toNat
  (x < y, x - y)
#align bitvec.sbb Std.BitVec.sbb

#align bitvec.sub Std.BitVec.sub
#align bitvec.mul Std.BitVec.mul

/-! ### Comparison operators -/

#align bitvec.uborrow Std.BitVec.ult
#align bitvec.ult Std.BitVec.ult

/-- Unsigned greater than for bitvectors. -/
protected def ugt (x y : BitVec w) : Bool := BitVec.ult y x
#align bitvec.ugt Std.BitVec.ugt

#align bitvec.ule Std.BitVec.ule

/-- Signed greater than or equal to for bitvectors. -/
protected def uge (x y : BitVec w) : Bool := BitVec.ule y x
#align bitvec.uge Std.BitVec.uge

#align bitvec.sborrow Std.BitVec.slt
#align bitvec.slt Std.BitVec.slt

/-- Signed greater than for bitvectors. -/
protected def sgt (x y : BitVec w) : Bool := BitVec.slt y x
#align bitvec.sgt Std.BitVec.sgt

#align bitvec.sle Std.BitVec.sle

/-- Signed greater than or equal to for bitvectors. -/
protected def sge (x y : BitVec w) : Bool := BitVec.sle y x
#align bitvec.sge Std.BitVec.sge

/-! ### Conversion to `nat` and `int` -/

#align bitvec.of_nat Std.BitVec.ofNat

/-- `addLsb r b` is `r + r + 1` if `b` is `true` and `r + r` otherwise. -/
def addLsb (r : ℕ) (b : Bool) :=
  Nat.bit b r
#align bitvec.add_lsb Std.BitVec.addLsb

#noalign bitvec.bits_to_nat
#align bitvec.to_nat Std.BitVec.toNat
#align bitvec.of_fin Std.BitVec.ofFin
#align bitvec.to_fin Std.BitVec.toFin
#align bitvec.to_int Std.BitVec.toInt


/-- Return the `i`-th least significant bit, where `i` is a statically known in-bounds index -/
def getLsb' (x : BitVec w) (i : Fin w) := x.getLsb i

/-- Return the `i`-th most significant bit, where `i` is a statically known in-bounds index -/
def getMsb' (x : BitVec w) (i : Fin w) := x.getMsb i

/--
  Convert a bitvector to a little-endian list of Booleans.
  That is, the head of the list is the least significant bit
-/
def toLEList (x : BitVec w) : List Bool :=
  List.ofFn x.getLsb'

/--
  Convert a bitvector to a big-endian list of Booleans.
  That is, the head of the list is the most significant bit
-/
def toBEList (x : BitVec w) : List Bool :=
  List.ofFn x.getMsb'

end Std.BitVec

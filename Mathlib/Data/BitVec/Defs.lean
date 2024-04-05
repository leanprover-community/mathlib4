/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich, Harun Khan, Alex Keizer, Abdalrhman M Mohamed
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fin.Basic
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

namespace BitVec

#align bitvec BitVec
#align bitvec.zero BitVec.zero

/-!
## Constants
-/

/-- The bitvector representing `1`.
    That is, the bitvector with least-significant bit `1` and all other bits `0` -/
@[simp] abbrev one (w : ℕ) : BitVec w := 1
#align bitvec.one BitVec.one

#align bitvec.cong BitVec.cast
#align bitvec.append BitVec.append
#align bitvec.shl BitVec.shiftLeft
#align bitvec.ushr BitVec.ushiftRight
#align bitvec.sshr BitVec.sshiftRight

/-! ### Bitwise operations -/

#align bitvec.not BitVec.not
#align bitvec.and BitVec.and
#align bitvec.or BitVec.or
#align bitvec.xor BitVec.xor

/-! ### Arithmetic operators -/

#align bitvec.neg BitVec.neg
/-- Add with carry (no overflow)

See also `Std.BitVec.adc`, which stores the carry bit separately. -/
def adc' {n} (x y : BitVec n) (c : Bool) : BitVec (n+1) :=
  let a := x.adc y c; .cons a.1 a.2
#align bitvec.adc BitVec.adc

#align bitvec.add BitVec.add

/-- Subtract with borrow -/
def sbb {n} (x y : BitVec n) (b : Bool) : Bool × BitVec n :=
  let y := y + ofFin b.toNat
  (x < y, x - y)
#align bitvec.sbb BitVec.sbb

#align bitvec.sub BitVec.sub
#align bitvec.mul BitVec.mul

/-! ### Comparison operators -/

#align bitvec.uborrow BitVec.ult
#align bitvec.ult BitVec.ult

/-- Unsigned greater than for bitvectors. -/
protected def ugt (x y : BitVec w) : Bool := BitVec.ult y x
#align bitvec.ugt BitVec.ugt

#align bitvec.ule BitVec.ule

/-- Signed greater than or equal to for bitvectors. -/
protected def uge (x y : BitVec w) : Bool := BitVec.ule y x
#align bitvec.uge BitVec.uge

#align bitvec.sborrow BitVec.slt
#align bitvec.slt BitVec.slt

/-- Signed greater than for bitvectors. -/
protected def sgt (x y : BitVec w) : Bool := BitVec.slt y x
#align bitvec.sgt BitVec.sgt

#align bitvec.sle BitVec.sle

/-- Signed greater than or equal to for bitvectors. -/
protected def sge (x y : BitVec w) : Bool := BitVec.sle y x
#align bitvec.sge BitVec.sge

/-! ### Conversion to `nat` and `int` -/

#align bitvec.of_nat BitVec.ofNat

/-- `addLsb r b` is `r + r + 1` if `b` is `true` and `r + r` otherwise. -/
def addLsb (r : ℕ) (b : Bool) :=
  Nat.bit b r
#align bitvec.add_lsb BitVec.addLsb

#noalign bitvec.bits_to_nat
#align bitvec.to_nat BitVec.toNat
#align bitvec.of_fin BitVec.ofFin
#align bitvec.to_fin BitVec.toFin
#align bitvec.to_int BitVec.toInt


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

instance : SMul ℕ (BitVec w) := ⟨fun x y => ofFin <| x • y.toFin⟩
instance : SMul ℤ (BitVec w) := ⟨fun x y => ofFin <| x • y.toFin⟩
instance : Pow (BitVec w) ℕ  := ⟨fun x n => ofFin <| x.toFin ^ n⟩

end BitVec

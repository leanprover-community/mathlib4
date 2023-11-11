/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Alex Keizer, Abdalrhman M Mohamed
-/

import Mathlib.Algebra.GroupPower.Order
import Mathlib.Data.Fin.Basic
-- import Mathlib.Data.Nat.Bitwise
-- import Mathlib.Data.ZMod.Defs
import Std.Data.BitVec
import Mathlib.Tactic


/-!
# Basic operations on bitvectors
Std has defined bitvector of length `w` as `Fin (2^w)`.
Here we define a few more operations on these bitvectors.

Note that `Std.BitVec` is distinct from mathlibs `Bitvec` type, this file is about the former.
For the latter, go to `Data.Bitvec` (notice the difference in capitalization).
Eventually, `Std.BitVec` will replace `Bitvec`, so we include the relevant `#align`s, but
comment them out for now.

## Main definitions

### Constants
* `Std.BitVec.one`: Constant `1`

### Structural
* `Std.BitVec.zeroExtendLE`: Zero extend a bitvector to a statically known larger size
* `Std.BitVec.ofBool`: Turn a Boolean into a bitvector of length 1
* `Std.BitVec.nil`: The empty bitvector
* `Std.BitVec.concat`: Append a new MSB to a bitvector
* `Std.BitVec.cons`: Prepend a new LSB to a bitvector

### Comparisons
* `Std.BitVec.sgt`: Signed greater-than comparison of bitvectors
* `Std.BitVec.sge`: Signed greater-equals comparison of bitvectors
* `Std.BitVec.ugt`: Unsigned greater-than comparison of bitvectors
* `Std.BitVec.uge`: Unsigned greater-equals comparison of bitvectors

### Arithmetic
* `Std.BitVec.adc`: Add with carry (no overflow)
* `Std.BitVec.sbb`: Subtract with borrow

-/

variable {w v : Nat}

namespace Std.BitVec

-- #align bitvec Std.BitVec
-- #align bitvec.zero Std.BitVec.zero
-- #align bitvec.cong Std.BitVec.cast
-- #align bitvec.append Std.BitVec.append
-- #align bitvec.shl Std.BitVec.shiftLeft
-- #align bitvec.ushr Std.BitVec.ushiftRight
-- #align bitvec.sshr Std.BitVec.sshiftRight
-- #align bitvec.not Std.BitVec.not
-- #align bitvec.and Std.BitVec.and
-- #align bitvec.or Std.BitVec.or
-- #align bitvec.xor Std.BitVec.xor
-- #align bitvec.neg Std.BitVec.neg
-- #align bitvec.add Std.BitVec.add
-- #align bitvec.sub Std.BitVec.sub
-- #align bitvec.mul Std.BitVec.mul
-- #align bitvec.ult Std.BitVec.ult
-- #align bitvec.ule Std.BitVec.ule
-- #align bitvec.slt Std.BitVec.slt
-- #align bitvec.sle Std.BitVec.sle
-- #align bitvec.of_nat Std.BitVec.ofNat
-- #align bitvec.to_nat Std.BitVec.toNat
-- #align bitvec.of_fin Std.BitVec.ofFin
-- #align bitvec.to_fin Std.BitVec.toFin
-- #align bitvec.to_int Std.BitVec.toInt
-- #align bitvec.uborrow Std.BitVec.ult
-- #align bitvec.sborrow Std.BitVec.slt

-- #noalign bitvec.bits_to_nat



/-!
## Constants
-/

/-- The bitvector representing `1`.
    That is, the bitvector with least-significant bit `1` and all other bits `0` -/
@[simp] abbrev one (w : ℕ) : BitVec w := 1
-- #align bitvec.one Std.BitVec.one

/-!
## Structural
-/

/-- Zero extend vector `x` of length `w` by adding zeros in the high bits until it has length `v`.
    Behaves exactly like `zeroExtend`, except it takes a proof that `w ≤ v`, so that no truncating
    is necessary. `zeroExtendLE` is easier to reason about than `zeroExtend`, and should thus be
    preferred whenever such a proof is available.
-/
def zeroExtendLE {w v : ℕ} (h : w ≤ v) (x : BitVec w) : BitVec v :=
  ⟨x.toFin.castLE <| pow_le_pow (by decide) h⟩

/-- Turn a `Bool` into a bitvector of length `1` -/
def ofBool : Bool → BitVec 1
  | true  => 1
  | false => 0

/-- The empty bitvector -/
def nil : BitVec 0 :=
  BitVec.zero 0

/-- Append a single bit to the end of a bitvector, using big endian order (see `append`).
    That is, the new bit is the least significant bit. -/
def concat {n} (msbs : BitVec n) (lsb : Bool) : BitVec (n+1) := msbs ++ (ofBool lsb)

/-- Prepend a single bit to the front of a bitvector, using big endian order (see `append`).
    That is, the new bit is the most significant bit. -/
def cons {n} (msb : Bool) (lsbs : BitVec n) : BitVec (n+1) :=
  ((ofBool msb) ++ lsbs).cast (Nat.add_comm ..)

/-!
## Comparisons
-/

/-- Signed greater than for bitvectors. -/
protected def sgt (x y : BitVec w) : Bool := BitVec.slt y x
-- #align bitvec.sgt Std.BitVec.sgt

/-- Signed greater than or equal to for bitvectors. -/
protected def sge (x y : BitVec w) : Bool := BitVec.sle y x
-- #align bitvec.sge Std.BitVec.sge

/-- Unsigned greater than for bitvectors. -/
protected def ugt (x y : BitVec w) : Bool := BitVec.ult y x
-- #align bitvec.ugt Std.BitVec.ugt

/-- Signed greater than or equal to for bitvectors. -/
protected def uge (x y : BitVec w) : Bool := BitVec.ule y x
-- #align bitvec.uge Std.BitVec.uge

/-!
## Arithmetic
-/

/-- Add with carry (no overflow) -/
def adc {n} (x y : BitVec n) (c : Bool) : BitVec (n+1) :=
  let x := x.zeroExtendLE (Nat.le_succ n)
  let y := y.zeroExtendLE (Nat.le_succ n)
  let c : BitVec (n + 1) := (ofBool c).zeroExtendLE (Nat.le_add_left 1 n)
  x + y + c
-- #align bitvec.adc Std.BitVec.adc

/-- Subtract with borrow -/
def sbb {n} (x y : BitVec n) (b : Bool) : Bool × BitVec n :=
  let y := y + (ofBool b).zeroExtend n
  (x < y, x - y)
-- #align bitvec.sbb Std.BitVec.sbb

/-- `addLsb r b` is `r + r + 1` if `b` is `true` and `r + r` otherwise. -/
@[deprecated Nat.bit] -- `addLsb` is just `flip Nat.bit`, prefer the latter
def addLsb (r : ℕ) (b : Bool) : ℕ :=
  Nat.bit b r
-- #align bitvec.add_lsb Std.BitVec.addLsb

end Std.BitVec

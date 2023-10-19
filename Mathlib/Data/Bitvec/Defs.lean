/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Joe Hendrix, Harun Khan, Abdalrhman M Mohamed
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Defs
import Std.Data.BitVec


/-!
# Basic operations on bitvectors
We define bitvectors. We choose the `Fin` representation over others for its relative efficiency
(Lean has special support for `Nat`), alignment with `UIntXY` types which are also represented
with `Fin`, and the fact that bitwise operations on `Fin` are already defined. Some other possible
representations are `List Bool`, `{ l : List Bool // l.length = w}`, `Fin w → Bool`.

We also define many bitvector operations from the
[`QF_BV` logic](https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV).
of SMT-LIBv2.
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

#noalign bitvec.ugt
#noalign bitvec.uge


/-!
## Bitwise operations
-/

/-- Signed greater than for bitvectors. -/
protected def sgt (x y : BitVec (w + 1)) : Prop := BitVec.slt y x
#align bitvec.sgt Std.BitVec.sgt

/-- Signed greater than or equal to for bitvectors. -/
protected def sge (x y : BitVec (w + 1)) : Prop := BitVec.sle y x
#align bitvec.sge Std.BitVec.sge


@[simp] lemma shiftLeft_def (x : BitVec w) (n: Nat)     : BitVec.shiftLeft x n = x <<< n    := rfl
@[simp] lemma ushiftRight_def (x : BitVec w) (n: Nat)   : BitVec.ushiftRight x n = x >>> n  := rfl
@[simp] lemma append_def (x : BitVec w) (y : BitVec v)  : BitVec.append x y = x ++ y        := rfl

/-- Convert a list of booleans to a bitvector. -/
def to_BV (bs : List Bool) : BitVec bs.length :=
  ⟨Nat.ofBits (λ i => bs[i]!) 0 bs.length, @Nat.ofBits_lt _ (bs.length)⟩

instance : GetElem (BitVec w) Nat Bool (Function.const _ (· < w)) where
  getElem x i _ := x.getLsb i

end Std.BitVec

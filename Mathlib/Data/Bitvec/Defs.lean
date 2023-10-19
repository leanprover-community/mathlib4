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

/-!
## Bitwise operations
-/

/-- Signed greater than for bitvectors. -/
protected def sgt (x y : BitVec (w + 1)) : Prop := BitVec.slt y x

/-- Signed greater than or equal to for bitvectors. -/
protected def sge (x y : BitVec (w + 1)) : Prop := BitVec.sle y x


@[simp] lemma shiftLeft_def (x : BitVec w) (n: Nat)     : BitVec.shiftLeft x n = x <<< n    := rfl
@[simp] lemma ushiftRight_def (x : BitVec w) (n: Nat)   : BitVec.ushiftRight x n = x >>> n  := rfl
@[simp] lemma append_def (x : BitVec w) (y : BitVec v)  : BitVec.append x y = x ++ y        := rfl

/-- Extract the bitvector between indices i (exclusive) and j (inclusive) where i > j. -/
@[simp]
def extract (i j) (x : BitVec w) : BitVec (i - j) :=
  .ofFin <| x.toInt >>> j

/-- Convert a list of booleans to a bitvector. -/
def to_BV (bs : List Bool) : BitVec bs.length :=
  ⟨Nat.ofBits (λ i => bs[i]!) 0 bs.length, @Nat.ofBits_lt _ (bs.length)⟩

instance : GetElem (BitVec w) Nat Bool (Function.const _ (· < w)) where
  getElem x i _ := x.getLsb i

end Std.BitVec

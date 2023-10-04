/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Joe Hendrix, Harun Khan, Abdalrhman M Mohamed
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Defs


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

/-- A bitvector of the specified width. This is represented as the underlying `Nat` number
in both the runtime and the kernel, inheriting all the special support for `Nat`. -/

abbrev BitVec (w : Nat) := Fin (2^w)

variable {w v : Nat}

namespace BitVec

/-!
## Bitwise operations
-/

/-- Signed less than for bitvectors. -/
protected def slt (x y : BitVec (w + 1)) : Prop :=
  ((x.val >>> w = 1) ∧ (y.val >>> w = 0)) ∨ ((x.val >>> w = y.val >>> w) ∧ x < y)

/-- Signed less than or equal to for bitvectors. -/
protected def sle (x y : BitVec (w + 1)) : Prop :=
  ((x.val >>> w = 1) ∧ (y.val >>> w = 0)) ∨ ((x.val >>> w = y.val >>> w) ∧ x ≤ y)

/-- Signed greater than for bitvectors. -/
protected def sgt (x y : BitVec (w + 1)) : Prop := BitVec.slt y x

/-- Signed greater than or equal to for bitvectors. -/
protected def sge (x y : BitVec (w + 1)) : Prop := BitVec.sle y x

/-- The left-shift of a bitvector by some amount. -/
protected def shiftLeft (x : BitVec w) (n : Nat) : BitVec w := (x.val <<< n)

/-- The right-shift of a bitvector by some amount. -/
protected def shiftRight (x : BitVec w) (n : Nat) : BitVec w :=
  ⟨x.val >>> n, by
      simp only [Nat.shiftRight_eq_div_pow]
      exact lt_of_le_of_lt (Nat.div_le_self' _ _) (x.isLt)⟩

instance : Complement (BitVec w) := ⟨(· + (1 : BitVec w))⟩
instance : HShiftLeft (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftLeft⟩
instance : HShiftRight (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftRight⟩

@[simp] lemma shiftLeft_def (x : BitVec w) (n: Nat) : BitVec.shiftLeft x n = x <<< n := rfl
@[simp] lemma shiftRight_def (x : BitVec w) (n: Nat) : BitVec.shiftRight x n = x >>> n := rfl

/-- Rotate `n` times to the left so that the lsb is `x [w - n]`. -/
def rotateLeft (x : BitVec w) (n : Nat) : BitVec w :=
  x <<< n ||| x >>> (w - n)

/-- Rotate `l` times to the right so that the lsb is `x [l]`. -/
def rotateRight (x : BitVec w) (l : Nat) : BitVec w :=
  x >>> l ||| x <<< (w - l)

/-- Concatenation of two bitvectors. where `x` forms the most significant bits. -/
protected def append (x : BitVec w) (y : BitVec v) : BitVec (w + v) :=
  ⟨x.val <<< v ||| y.val, Nat.add_comm _ _ ▸ Nat.append_lt y.isLt x.isLt⟩

instance : HAppend (BitVec w) (BitVec v) (BitVec (w + v)) := ⟨BitVec.append⟩

@[simp]
lemma append_def (x : BitVec w) (y : BitVec v) : BitVec.append x y = x ++ y := rfl

/-- Extract the bitvector between indices i (exclusive) and j (inclusive) where i > j. -/
@[simp]
def extract (i j) (x : BitVec w) : BitVec (i - j) := x.val >>> j

/-- Generate and concatenate `i` copies of a bitvector. -/
def replicate : (i : Nat) → BitVec w → BitVec (w * i)
  | 0,   _ => 0
  | n + 1, x =>
    have hEq : w + w * n = w * (n + 1) := by
      rw [Nat.mul_add, Nat.add_comm, Nat.mul_one]
    hEq ▸ (x ++ replicate n x)

/-- Pad a bitvector by `i` zeros as the most significant bits. -/
def zeroExtend (i : Nat) (x : BitVec w) : BitVec (w + i) :=
  have hEq : w+i = i+w := Nat.add_comm _ _
  hEq ▸ ((0 : BitVec i) ++ x)

/-- Extend a bitvector by repeating the most significant bit `i` times. -/
def signExtend (i) (x : BitVec w) : BitVec (w + i) :=
  have hEq : ((w - 1) - (w - 1) + 1) * i + w = w + i := by
    rw [Nat.sub_self, Nat.zero_add, Nat.one_mul, Nat.add_comm]
  hEq ▸ ((replicate i (extract w (w - 1) x)) ++ x)

/-- Return the `i`-th least significant bit. -/
@[simp]
def get (x : BitVec w) (i : Nat) : Bool :=
  x.extract (i + 1) i != 0

/-- Convert a list of booleans to a bitvector. -/
def to_BV (bs : List Bool) : BitVec bs.length :=
  ⟨Nat.ofBits (λ i => bs[i]!) 0 bs.length, @Nat.ofBits_lt _ (bs.length)⟩

instance : GetElem (BitVec w) Nat Bool (Function.const _ (· < w)) where
  getElem x i _ := x.get i

end BitVec

/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Joe Hendrix, Harun Khan, Abdalrhman M Mohamed
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bitwise

/-!
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

def BitVec (w : Nat) := Fin (2^w)

instance : DecidableEq (BitVec w) :=
  inferInstanceAs (DecidableEq (Fin _))

namespace BitVec

protected def zero (w : Nat) : BitVec w :=
  ⟨0, Nat.two_pow_pos w⟩

/-- The bitvector `n mod 2^w`. -/
protected def ofNat (w : Nat) (n : Nat) : BitVec w :=
  Fin.ofNat' n (Nat.two_pow_pos w)

instance : Inhabited (BitVec w) := ⟨BitVec.zero w⟩

instance : OfNat (BitVec w) (nat_lit 0) :=
  ⟨BitVec.zero w⟩

/-!
## Arithmetic
We inherit `Fin` implementations when fast but write mod/div
ourselves to avoid the extra modulo operation.
-/

protected def mod (x y : BitVec w) : BitVec w :=
  ⟨x.val % y.val, Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt⟩
protected def div (x y : BitVec w) : BitVec w :=
  ⟨x.val / y.val, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt⟩
protected def lt (x y : BitVec w) : Bool :=
  x.val < y.val
protected def le (x y : BitVec w) : Bool :=
  x.val ≤ y.val

instance : Add (BitVec w) := inferInstanceAs (Add (Fin _))
instance : Sub (BitVec w) := inferInstanceAs (Sub (Fin _))
instance : Mul (BitVec w) := inferInstanceAs (Mul (Fin _))
instance : Neg (BitVec w) := inferInstanceAs (Neg (Fin _))
instance : Mod (BitVec w) := ⟨BitVec.mod⟩
instance : Div (BitVec w) := ⟨BitVec.div⟩
instance : LT (BitVec w)  := ⟨fun x y => BitVec.lt x y⟩
instance : LE (BitVec w)  := ⟨fun x y => BitVec.le x y⟩

/-!
## Bitwise operations
-/

@[norm_cast]
theorem val_bitvec_eq {a b : BitVec w} : a.val = b.val ↔ a = b :=
  ⟨(match a, b, · with | ⟨_, _⟩,⟨_, _⟩, rfl => rfl), (· ▸ rfl)⟩

/-- `a < b` as natural numbers if and only if `a < b` in `Fin n`. -/
@[norm_cast]
theorem val_bitvec_lt {a b : BitVec w} : a.val < b.val ↔ a < b := by
  simp [LT.lt, BitVec.lt]

/-- `a ≠ b` as natural numbers if and only if `a != b` in `Fin n`. -/
@[norm_cast]
theorem val_bitvec_bne {a b : BitVec w} : a.val ≠ b.val ↔ a != b := by
  simp [bne, val_bitvec_eq]

protected def complement (x : BitVec w) : BitVec w :=
  0 - (x + .ofNat w 1)

protected def and (x y : BitVec w) : BitVec w :=
  ⟨x.val &&& y.val, by simp [HAnd.hAnd, AndOp.and, Nat.land, Nat.bitwise_lt]⟩

protected def or (x y : BitVec w) : BitVec w :=
  ⟨x.val ||| y.val, by simp [HOr.hOr, OrOp.or, Nat.lor, Nat.bitwise_lt]⟩

protected def xor (x y : BitVec w) : BitVec w :=
  ⟨x.val ^^^ y.val, by simp [HXor.hXor, Xor.xor, Nat.xor, Nat.bitwise_lt]⟩

protected def shiftLeft (x : BitVec w) (n : Nat) : BitVec w :=
  .ofNat w (x.val <<< n)

protected def shiftRight (x : BitVec w) (n : Nat) : BitVec w :=
  ⟨x.val >>> n, by
      simp only [Nat.shiftRight_eq_shiftr, Nat.shiftr_eq_div_pow]
      exact lt_of_le_of_lt (Nat.div_le_self' _ _) (x.isLt) ⟩

protected def slt (x y : BitVec (w + 1)) : Prop :=
  if (y.val >>> w) < (x.val >>> w) then True
  else x.val >>> w = y.val >>> w ∧ x.val % 2^w < y.val % 2^w

protected def sle (x y : BitVec (w + 1)) : Prop :=
  if (y.val >>> w) < (x.val >>> w) then True
  else (x.val >>> w = y.val >>> w) ∧ x.val % 2^w ≤ y.val % 2^w

protected def sgt (x y : BitVec (w + 1)) : Prop := BitVec.slt y x

protected def sge (x y : BitVec (w + 1)) : Prop := BitVec.sle y x

instance : Complement (BitVec w) := ⟨BitVec.complement⟩
instance : AndOp (BitVec w) := ⟨BitVec.and⟩
instance : OrOp (BitVec w) := ⟨BitVec.or⟩
instance : Xor (BitVec w) := ⟨BitVec.xor⟩
instance : HShiftLeft (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftLeft⟩
instance : HShiftRight (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftRight⟩

def rotateLeft (x : BitVec w) (n : Nat) : BitVec w :=
  x <<< n ||| x >>> (w - n)

def rotateRight (x : BitVec w) (n : Nat) : BitVec w :=
  x >>> n ||| x <<< (w - n)

protected def append (x : BitVec w) (y : BitVec v) : BitVec (w+v) :=
  ⟨x.val <<< v ||| y.val, Nat.add_comm _ _ ▸ Nat.append_lt y.isLt x.isLt⟩

instance : HAppend (BitVec w) (BitVec v) (BitVec (w+v)) := ⟨BitVec.append⟩

/-- Extract the bitvector between indices i and j. -/
@[simp]
def extract (i j : Nat) (x : BitVec w) : BitVec (i - j + 1) :=
  BitVec.ofNat _ (x.val >>> j)

def repeat_ : (i : Nat) → BitVec w → BitVec (w*i)
  | 0,   _ => 0
  | n+1, x =>
    have hEq : w + w*n = w*(n + 1) := by
      rw [Nat.mul_add, Nat.add_comm, Nat.mul_one]
    hEq ▸ (x ++ repeat_ n x)

def zeroExtend (i : Nat) (x : BitVec w) : BitVec (w+i) :=
  have hEq : w+i = i+w := Nat.add_comm _ _
  hEq ▸ ((0 : BitVec i) ++ x)

def signExtend (i : Nat) (x : BitVec w) : BitVec (w+i) :=
  have hEq : ((w-1) - (w-1) + 1)*i + w = w+i := by
    rw [Nat.sub_self, Nat.zero_add, Nat.one_mul, Nat.add_comm]
  hEq ▸ ((repeat_ i (extract (w-1) (w-1) x)) ++ x)

def shrink (v : Nat) (x : BitVec w) : BitVec v :=
  if hZero : 0 < v then
    have hEq : v - 1 + 0 + 1 = v := by
      rw [Nat.add_zero]
      exact Nat.sub_add_cancel hZero
    hEq ▸ x.extract (v - 1) 0
  else 0

/-- Return the `i`-th least significant bit. -/
@[simp]
def get (x : BitVec w) (i : Nat) : Bool :=
  x.extract i i != 0

def bbT (bs : List Bool) : BitVec bs.length :=
  ⟨Nat.ofBits (λ i => bs[i]!) 0 bs.length, @Nat.ofBits_lt _ (bs.length)⟩

instance : GetElem (BitVec w) Nat Bool (fun _ i => i < w) where
  getElem x i _ := Nat.testBit x.val i

end BitVec

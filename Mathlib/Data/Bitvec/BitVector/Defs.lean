/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich

! This file was ported from Lean 3 source module data.bitvec.core
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Pow
import Init.Data.Format.Basic
import Mathlib.Init.Data.Nat.Lemmas
/-!
# Basic operations on bitvectors

This is a work-in-progress, and contains additions to other theories.

This file was moved to mathlib from core Lean in the switch to Lean 3.20.0c.
It is not fully in compliance with mathlib style standards.
-/

/-- `Bitvec.BitVector n` is a `Vector` of `Bool` with length `n`. -/
protected abbrev Bitvec.BitVector (n : ℕ) :=
  Vector Bool n

namespace Bitvec.BitVector

open Nat Vector
open Bitvec (BitVector)

-- mathport name: «expr ++ₜ »
local infixl:65 "++ₜ" => Vector.append

/-- Create a zero bitvector -/
@[reducible]
protected def zero (n : ℕ) : BitVector n :=
  replicate n false
#align bitvec.zero Bitvec.BitVector.zero

/-- Create a bitvector of length `n` whose `n-1`st entry is 1 and other entries are 0. -/
@[reducible]
protected def one : ∀ n : ℕ, BitVector n
  | 0 => nil
  | succ n => replicate n false++ₜtrue ::ᵥ nil
#align bitvec.one Bitvec.BitVector.one

/-- Create a bitvector from another with a provably equal length. -/
protected def cong {a b : ℕ} (h : a = b) : BitVector a → BitVector b
  | ⟨x, p⟩ => ⟨x, h ▸ p⟩
#align bitvec.cong Bitvec.BitVector.cong

/-- `BitVector` specific version of `Vector.append` -/
def append {m n} : BitVector m → BitVector n → BitVector (m + n) :=
  Vector.append
#align bitvec.append Bitvec.BitVector.append

/-! ### Shift operations -/


section Shift

variable {n : ℕ}

/-- `shl x i` is the bitvector obtained by left-shifting `x` `i` times and padding with `false`.
If `x.length < i` then this will return the all-`false`s bitvector. -/
def shl (x : BitVector n) (i : ℕ) : BitVector n :=
  BitVector.cong (by simp) <| drop i x++ₜreplicate (min n i) false
#align bitvec.shl Bitvec.BitVector.shl

/-- `fill_shr x i fill` is the bitvector obtained by right-shifting `x` `i` times and then
padding with `fill : Bool`. If `x.length < i` then this will return the constant `fill`
bitvector. -/
def fillShr (x : BitVector n) (i : ℕ) (fill : Bool) : BitVector n :=
  BitVector.cong
      (by
        by_cases h : i ≤ n
        · have h₁ := Nat.sub_le n i
          rw [min_eq_right h]
          rw [min_eq_left h₁, ← add_tsub_assoc_of_le h, Nat.add_comm, add_tsub_cancel_right]
        · have h₁ := le_of_not_ge h
          rw [min_eq_left h₁, tsub_eq_zero_iff_le.mpr h₁, zero_min, Nat.add_zero]) <|
    replicate (min n i) fill++ₜtake (n - i) x
#align bitvec.fill_shr Bitvec.BitVector.fillShr

/-- unsigned shift right -/
def ushr (x : BitVector n) (i : ℕ) : BitVector n :=
  fillShr x i false
#align bitvec.ushr Bitvec.BitVector.ushr

/-- signed shift right -/
def sshr : ∀ {m : ℕ}, BitVector m → ℕ → BitVector m
  | 0, _, _ => nil
  | succ _, x, i => head x ::ᵥ fillShr (tail x) i (head x)
#align bitvec.sshr Bitvec.BitVector.sshr

end Shift

/-! ### Bitwise operations -/


section Bitwise

variable {n : ℕ}

-- porting note: added protected, since now this clashes with `_root_.not` (formerly `bnot`)
/-- bitwise not -/
protected def not (bv : BitVector n) : BitVector n :=
  map not bv
#align bitvec.not Bitvec.BitVector.not

-- porting note: added protected, since now this clashes with `_root_.and` (formerly `band`)
/-- bitwise and -/
protected def and : BitVector n → BitVector n → BitVector n :=
  map₂ and
#align bitvec.and Bitvec.BitVector.and

-- porting note: added protected, since now this clashes with `_root_.or` (formerly `bor`)
/-- bitwise or -/
protected def or : BitVector n → BitVector n → BitVector n :=
  map₂ or
#align bitvec.or Bitvec.BitVector.or

-- porting note: added protected, since now this clashes with `_root_.xor` (formerly `bxor`)
/-- bitwise xor -/
protected def xor : BitVector n → BitVector n → BitVector n :=
  map₂ xor
#align bitvec.xor Bitvec.BitVector.xor

instance : Complement (BitVector n) :=
⟨Bitvec.BitVector.not⟩

instance : AndOp (BitVector n) :=
⟨Bitvec.BitVector.and⟩

instance : OrOp (BitVector n) :=
⟨Bitvec.BitVector.or⟩

instance : Xor (BitVector n) :=
⟨Bitvec.BitVector.xor⟩

end Bitwise

/-! ### Arithmetic operators -/


section Arith

variable {n : ℕ}

/-- `neg x` is the two's complement of `x`. -/
protected def neg (x : BitVector n) : BitVector n :=
  let f y c := (y || c, xor y c)
  Prod.snd (mapAccumr f x false)
#align bitvec.neg Bitvec.BitVector.neg

/-- Add with carry (no overflow) -/
def adc (x y : BitVector n) (c : Bool) : BitVector (n + 1) :=
  let f x y c := (Bool.carry x y c, Bool.xor3 x y c)
  let ⟨c, z⟩ := Vector.mapAccumr₂ f x y c
  c ::ᵥ z
#align bitvec.adc Bitvec.BitVector.adc

/-- The sum of two bitvectors -/
protected def add (x y : BitVector n) : BitVector n :=
  tail (adc x y false)
#align bitvec.add Bitvec.BitVector.add

/-- Subtract with borrow -/
def sbb (x y : BitVector n) (b : Bool) : Bool × BitVector n :=
  let f x y c := (Bool.carry (not x) y c, Bool.xor3 x y c)
  Vector.mapAccumr₂ f x y b
#align bitvec.sbb Bitvec.BitVector.sbb

/-- The difference of two bitvectors -/
protected def sub (x y : BitVector n) : BitVector n :=
  Prod.snd (sbb x y false)
#align bitvec.sub Bitvec.BitVector.sub

instance : Zero (BitVector n) :=
  ⟨BitVector.zero n⟩

instance : One (BitVector n) :=
  ⟨BitVector.one n⟩

instance : Add (BitVector n) :=
  ⟨BitVector.add⟩

instance : Sub (BitVector n) :=
  ⟨BitVector.sub⟩

instance : Neg (BitVector n) :=
  ⟨BitVector.neg⟩

/-- The product of two bitvectors -/
protected def mul (x y : BitVector n) : BitVector n :=
  let f r b := cond b (r + r + y) (r + r)
  (toList x).foldl f 0
#align bitvec.mul Bitvec.BitVector.mul

instance : Mul (BitVector n) :=
  ⟨BitVector.mul⟩

end Arith

/-! ### Comparison operators -/


section Comparison

variable {n : ℕ}

/-- `uborrow x y` returns `true` iff the "subtract with borrow" operation on `x`, `y` and `false`
required a borrow. -/
def uborrow (x y : BitVector n) : Bool :=
  Prod.fst (sbb x y false)
#align bitvec.uborrow Bitvec.BitVector.uborrow

/-- unsigned less-than proposition -/
def Ult (x y : BitVector n) : Prop :=
  uborrow x y
#align bitvec.ult Bitvec.BitVector.Ult

/-- unsigned greater-than proposition -/
def Ugt (x y : BitVector n) : Prop :=
  Ult y x
#align bitvec.ugt Bitvec.BitVector.Ugt

/-- unsigned less-than-or-equal-to proposition -/
def Ule (x y : BitVector n) : Prop :=
  ¬Ult y x
#align bitvec.ule Bitvec.BitVector.Ule

/-- unsigned greater-than-or-equal-to proposition -/
def Uge (x y : BitVector n) : Prop :=
  Ule y x
#align bitvec.uge Bitvec.BitVector.Uge

/-- `sborrow x y` returns `true` iff `x < y` as two's complement integers -/
def sborrow : ∀ {n : ℕ}, BitVector n → BitVector n → Bool
  | 0, _, _ => false
  | succ _, x, y =>
    match (head x, head y) with
    | (true, false) => true
    | (false, true) => false
    | _ => uborrow (tail x) (tail y)
#align bitvec.sborrow Bitvec.BitVector.sborrow

/-- signed less-than proposition -/
def Slt (x y : BitVector n) : Prop :=
  sborrow x y
#align bitvec.slt Bitvec.BitVector.Slt

/-- signed greater-than proposition -/
def Sgt (x y : BitVector n) : Prop :=
  Slt y x
#align bitvec.sgt Bitvec.BitVector.Sgt

/-- signed less-than-or-equal-to proposition -/
def Sle (x y : BitVector n) : Prop :=
  ¬Slt y x
#align bitvec.sle Bitvec.BitVector.Sle

/-- signed greater-than-or-equal-to proposition -/
def Sge (x y : BitVector n) : Prop :=
  Sle y x
#align bitvec.sge Bitvec.BitVector.Sge

end Comparison

/-! ### Conversion to `nat` and `int` -/


section Conversion

variable {α : Type}

/-- Create a bitvector from a `nat` -/
protected def ofNat : ∀ n : ℕ, Nat → BitVector n
  | 0, _ => nil
  | succ n, x => BitVector.ofNat n (x / 2)++ₜdecide (x % 2 = 1) ::ᵥ nil
#align bitvec.of_nat Bitvec.BitVector.ofNat

/-- Create a bitvector from an `Int`. The ring homomorphism from Int to bitvectors. -/
protected def ofInt : ∀ n : ℕ, Int → BitVector n
  | n, Int.ofNat m => BitVector.ofNat n m
  | n, Int.negSucc m => (BitVector.ofNat n m).not

/-- `add_lsb r b` is `r + r + 1` if `b` is `true` and `r + r` otherwise. -/
def addLsb (r : ℕ) (b : Bool) :=
  r + r + cond b 1 0
#align bitvec.add_lsb Bitvec.BitVector.addLsb

/-- Given a `List` of `Bool`s, return the `nat` they represent as a list of binary digits. -/
def bitsToNat (v : List Bool) : Nat :=
  v.foldl addLsb 0
#align bitvec.bits_to_nat Bitvec.BitVector.bitsToNat

/-- Return the natural number encoded by the input bitvector -/
protected def toNat {n : Nat} (v : BitVector n) : Nat :=
  bitsToNat (toList v)
#align bitvec.to_nat Bitvec.BitVector.toNat

instance (n : ℕ) : Preorder (BitVector n) :=
  Preorder.lift BitVector.toNat

/-- convert `fin` to `BitVector` -/
def ofFin {n : ℕ} (i : Fin <| 2 ^ n) : BitVector n :=
  BitVector.ofNat _ i.val
#align bitvec.of_fin Bitvec.BitVector.ofFin

/-- convert `BitVector` to `fin` -/
def toFin {n : ℕ} (i : BitVector n) : Fin (2 ^ n) :=
  i.toNat
#align bitvec.to_fin Bitvec.BitVector.toFin


/-- Return the integer encoded by the input bitvector -/
protected def toInt : ∀ {n : Nat}, BitVector n → Int
  | 0, _ => 0
  | succ _, v =>
    cond (head v) (Int.negSucc <| BitVector.toNat <| BitVector.not <| tail v)
      (Int.ofNat <| BitVector.toNat <| tail v)
#align bitvec.to_int Bitvec.BitVector.toInt

end Conversion

/-! ### Miscellaneous instances -/


private def repr {n : Nat} : BitVector n → String
  | ⟨bs, _⟩ => "0b" ++ (bs.map fun b : Bool => if b then '1' else '0').asString

instance (n : Nat) : Repr (BitVector n) where
  reprPrec (b : BitVector n) _ := Std.Format.text (repr b)

instance {n} {x y : BitVector n} : Decidable (BitVector.Ult x y) :=
  decEq _ _

instance {n} {x y : BitVector n} : Decidable (BitVector.Ugt x y) :=
  decEq _ _

instance {n} : HShiftLeft (BitVector n) Nat (BitVector n) := ⟨BitVector.shl⟩

instance {n} : HShiftRight (BitVector n) Nat (BitVector n) := ⟨BitVector.ushr⟩

instance {n} : ShiftLeft (BitVector n) := ⟨fun x y => x <<< y.toNat⟩

instance {n} : ShiftRight (BitVector n) := ⟨fun x y => x >>> y.toNat⟩

end BitVector

end Bitvec

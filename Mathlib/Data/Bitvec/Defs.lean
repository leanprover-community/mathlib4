/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Pow
import Init.Data.Format.Basic
import Mathlib.Init.Data.Nat.Lemmas

#align_import data.bitvec.core from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"
/-!
# Basic operations on bitvectors

This is a work-in-progress, and contains additions to other theories.

This file was moved to mathlib from core Lean in the switch to Lean 3.20.0c.
It is not fully in compliance with mathlib style standards.
-/

/-- `Bitvec n` is a `Vector` of `Bool` with length `n`. -/
@[reducible]
def Bitvec (n : ℕ) :=
  Vector Bool n
#align bitvec Bitvec

namespace Bitvec

open Nat

open Vector

-- mathport name: «expr ++ₜ »
local infixl:65 "++ₜ" => Vector.append

/-- Create a zero bitvector -/
@[reducible]
protected def zero (n : ℕ) : Bitvec n :=
  replicate n false
#align bitvec.zero Bitvec.zero

/-- Create a bitvector of length `n` whose `n-1`st entry is 1 and other entries are 0. -/
@[reducible]
protected def one : ∀ n : ℕ, Bitvec n
  | 0 => nil
  | succ n => replicate n false++ₜtrue ::ᵥ nil
#align bitvec.one Bitvec.one

/-- Create a bitvector from another with a provably equal length. -/
protected def cong {a b : ℕ} : a = b → Bitvec a → Bitvec b :=
  Vector.congr
#align bitvec.cong Bitvec.cong

/-- `Bitvec` specific version of `Vector.append` -/
def append {m n} : Bitvec m → Bitvec n → Bitvec (m + n) :=
  Vector.append
#align bitvec.append Bitvec.append

/-! ### Shift operations -/


section Shift

variable {n : ℕ}

/-- `shl x i` is the bitvector obtained by left-shifting `x` `i` times and padding with `false`.
If `x.length < i` then this will return the all-`false`s bitvector. -/
def shl (x : Bitvec n) (i : ℕ) : Bitvec n :=
  shiftLeftFill x i false
#align bitvec.shl Bitvec.shl

#noalign bitvec.fill_shr

/-- unsigned shift right -/
def ushr (x : Bitvec n) (i : ℕ) : Bitvec n :=
  shiftRightFill x i false
#align bitvec.ushr Bitvec.ushr

/-- signed shift right -/
def sshr : ∀ {m : ℕ}, Bitvec m → ℕ → Bitvec m
  | 0, _, _ => nil
  | succ _, x, i => head x ::ᵥ shiftRightFill (tail x) i (head x)
#align bitvec.sshr Bitvec.sshr

end Shift

/-! ### Bitwise operations -/


section Bitwise

variable {n : ℕ}

-- porting note: added protected, since now this clashes with `_root_.not` (formerly `bnot`)
/-- bitwise not -/
protected def not (bv : Bitvec n) : Bitvec n :=
  map not bv
#align bitvec.not Bitvec.not

-- porting note: added protected, since now this clashes with `_root_.and` (formerly `band`)
/-- bitwise and -/
protected def and : Bitvec n → Bitvec n → Bitvec n :=
  map₂ and
#align bitvec.and Bitvec.and

-- porting note: added protected, since now this clashes with `_root_.or` (formerly `bor`)
/-- bitwise or -/
protected def or : Bitvec n → Bitvec n → Bitvec n :=
  map₂ or
#align bitvec.or Bitvec.or

-- porting note: added protected, since now this clashes with `_root_.xor` (formerly `bxor`)
/-- bitwise xor -/
protected def xor : Bitvec n → Bitvec n → Bitvec n :=
  map₂ xor
#align bitvec.xor Bitvec.xor

instance : Complement (Bitvec n) :=
⟨Bitvec.not⟩

instance : AndOp (Bitvec n) :=
⟨Bitvec.and⟩

instance : OrOp (Bitvec n) :=
⟨Bitvec.or⟩

instance : Xor (Bitvec n) :=
⟨Bitvec.xor⟩

end Bitwise

/-! ### Arithmetic operators -/


section Arith

variable {n : ℕ}

/-- `neg x` is the two's complement of `x`. -/
protected def neg (x : Bitvec n) : Bitvec n :=
  let f y c := (y || c, xor y c)
  Prod.snd (mapAccumr f x false)
#align bitvec.neg Bitvec.neg

/-- Add with carry (no overflow) -/
def adc (x y : Bitvec n) (c : Bool) : Bitvec (n + 1) :=
  let f x y c := (Bool.carry x y c, Bool.xor3 x y c)
  let ⟨c, z⟩ := Vector.mapAccumr₂ f x y c
  c ::ᵥ z
#align bitvec.adc Bitvec.adc

/-- The sum of two bitvectors -/
protected def add (x y : Bitvec n) : Bitvec n :=
  tail (adc x y false)
#align bitvec.add Bitvec.add

/-- Subtract with borrow -/
def sbb (x y : Bitvec n) (b : Bool) : Bool × Bitvec n :=
  let f x y c := (Bool.carry (not x) y c, Bool.xor3 x y c)
  Vector.mapAccumr₂ f x y b
#align bitvec.sbb Bitvec.sbb

/-- The difference of two bitvectors -/
protected def sub (x y : Bitvec n) : Bitvec n :=
  Prod.snd (sbb x y false)
#align bitvec.sub Bitvec.sub

instance : Zero (Bitvec n) :=
  ⟨Bitvec.zero n⟩

instance : One (Bitvec n) :=
  ⟨Bitvec.one n⟩

instance : Add (Bitvec n) :=
  ⟨Bitvec.add⟩

instance : Sub (Bitvec n) :=
  ⟨Bitvec.sub⟩

instance : Neg (Bitvec n) :=
  ⟨Bitvec.neg⟩

/-- The product of two bitvectors -/
protected def mul (x y : Bitvec n) : Bitvec n :=
  let f r b := cond b (r + r + y) (r + r)
  (toList x).foldl f 0
#align bitvec.mul Bitvec.mul

instance : Mul (Bitvec n) :=
  ⟨Bitvec.mul⟩

end Arith

/-! ### Comparison operators -/


section Comparison

variable {n : ℕ}

/-- `uborrow x y` returns `true` iff the "subtract with borrow" operation on `x`, `y` and `false`
required a borrow. -/
def uborrow (x y : Bitvec n) : Bool :=
  Prod.fst (sbb x y false)
#align bitvec.uborrow Bitvec.uborrow

/-- unsigned less-than proposition -/
def Ult (x y : Bitvec n) : Prop :=
  uborrow x y
#align bitvec.ult Bitvec.Ult

/-- unsigned greater-than proposition -/
def Ugt (x y : Bitvec n) : Prop :=
  Ult y x
#align bitvec.ugt Bitvec.Ugt

/-- unsigned less-than-or-equal-to proposition -/
def Ule (x y : Bitvec n) : Prop :=
  ¬Ult y x
#align bitvec.ule Bitvec.Ule

/-- unsigned greater-than-or-equal-to proposition -/
def Uge (x y : Bitvec n) : Prop :=
  Ule y x
#align bitvec.uge Bitvec.Uge

/-- `sborrow x y` returns `true` iff `x < y` as two's complement integers -/
def sborrow : ∀ {n : ℕ}, Bitvec n → Bitvec n → Bool
  | 0, _, _ => false
  | succ _, x, y =>
    match (head x, head y) with
    | (true, false) => true
    | (false, true) => false
    | _ => uborrow (tail x) (tail y)
#align bitvec.sborrow Bitvec.sborrow

/-- signed less-than proposition -/
def Slt (x y : Bitvec n) : Prop :=
  sborrow x y
#align bitvec.slt Bitvec.Slt

/-- signed greater-than proposition -/
def Sgt (x y : Bitvec n) : Prop :=
  Slt y x
#align bitvec.sgt Bitvec.Sgt

/-- signed less-than-or-equal-to proposition -/
def Sle (x y : Bitvec n) : Prop :=
  ¬Slt y x
#align bitvec.sle Bitvec.Sle

/-- signed greater-than-or-equal-to proposition -/
def Sge (x y : Bitvec n) : Prop :=
  Sle y x
#align bitvec.sge Bitvec.Sge

end Comparison

/-! ### Conversion to `nat` and `int` -/


section Conversion

variable {α : Type}

/-- Create a bitvector from a `nat` -/
protected def ofNat : ∀ n : ℕ, Nat → Bitvec n
  | 0, _ => nil
  | succ n, x => Bitvec.ofNat n (x / 2)++ₜdecide (x % 2 = 1) ::ᵥ nil
#align bitvec.of_nat Bitvec.ofNat

/-- Create a bitvector from an `Int`. The ring homomorphism from Int to bitvectors. -/
protected def ofInt : ∀ n : ℕ, Int → Bitvec n
  | n, Int.ofNat m => Bitvec.ofNat n m
  | n, Int.negSucc m => (Bitvec.ofNat n m).not

/-- `add_lsb r b` is `r + r + 1` if `b` is `true` and `r + r` otherwise. -/
def addLsb (r : ℕ) (b : Bool) :=
  r + r + cond b 1 0
#align bitvec.add_lsb Bitvec.addLsb

/-- Given a `List` of `Bool`s, return the `nat` they represent as a list of binary digits. -/
def bitsToNat (v : List Bool) : Nat :=
  v.foldl addLsb 0
#align bitvec.bits_to_nat Bitvec.bitsToNat

/-- Return the natural number encoded by the input bitvector -/
protected def toNat {n : Nat} (v : Bitvec n) : Nat :=
  bitsToNat (toList v)
#align bitvec.to_nat Bitvec.toNat

instance (n : ℕ) : Preorder (Bitvec n) :=
  Preorder.lift Bitvec.toNat

/-- convert `fin` to `Bitvec` -/
def ofFin {n : ℕ} (i : Fin <| 2 ^ n) : Bitvec n :=
  Bitvec.ofNat _ i.val
#align bitvec.of_fin Bitvec.ofFin

/-- convert `Bitvec` to `fin` -/
def toFin {n : ℕ} (i : Bitvec n) : Fin (2 ^ n) :=
  i.toNat
#align bitvec.to_fin Bitvec.toFin


/-- Return the integer encoded by the input bitvector -/
protected def toInt : ∀ {n : Nat}, Bitvec n → Int
  | 0, _ => 0
  | succ _, v =>
    cond (head v) (Int.negSucc <| Bitvec.toNat <| Bitvec.not <| tail v)
      (Int.ofNat <| Bitvec.toNat <| tail v)
#align bitvec.to_int Bitvec.toInt

end Conversion

/-! ### Miscellaneous instances -/


private def repr {n : Nat} : Bitvec n → String
  | ⟨bs, _⟩ => "0b" ++ (bs.map fun b : Bool => if b then '1' else '0').asString

instance (n : Nat) : Repr (Bitvec n) where
  reprPrec (b : Bitvec n) _ := Std.Format.text (repr b)

end Bitvec

instance {n} {x y : Bitvec n} : Decidable (Bitvec.Ult x y) :=
  decEq _ _

instance {n} {x y : Bitvec n} : Decidable (Bitvec.Ugt x y) :=
  decEq _ _

instance {n} : HShiftLeft (Bitvec n) Nat (Bitvec n) := ⟨Bitvec.shl⟩

instance {n} : HShiftRight (Bitvec n) Nat (Bitvec n) := ⟨Bitvec.ushr⟩

instance {n} : ShiftLeft (Bitvec n) := ⟨fun x y => x <<< y.toNat⟩

instance {n} : ShiftRight (Bitvec n) := ⟨fun x y => x >>> y.toNat⟩

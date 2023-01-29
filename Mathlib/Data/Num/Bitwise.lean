/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.num.bitwise
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Num.Basic
import Mathbin.Data.Bitvec.Core

/-!
# Bitwise operations using binary representation of integers

## Definitions

* bitwise operations for `pos_num` and `num`,
* `snum`, a type that represents integers as a bit string with a sign bit at the end,
* arithmetic operations for `snum`.
-/


namespace PosNum

/-- Bitwise "or" for `pos_num`. -/
def lor : PosNum → PosNum → PosNum
  | 1, bit0 q => bit1 q
  | 1, q => q
  | bit0 p, 1 => bit1 p
  | p, 1 => p
  | bit0 p, bit0 q => bit0 (lor p q)
  | bit0 p, bit1 q => bit1 (lor p q)
  | bit1 p, bit0 q => bit1 (lor p q)
  | bit1 p, bit1 q => bit1 (lor p q)
#align pos_num.lor PosNum.lor

/-- Bitwise "and" for `pos_num`. -/
def land : PosNum → PosNum → Num
  | 1, bit0 q => 0
  | 1, _ => 1
  | bit0 p, 1 => 0
  | _, 1 => 1
  | bit0 p, bit0 q => Num.bit0 (land p q)
  | bit0 p, bit1 q => Num.bit0 (land p q)
  | bit1 p, bit0 q => Num.bit0 (land p q)
  | bit1 p, bit1 q => Num.bit1 (land p q)
#align pos_num.land PosNum.land

/-- Bitwise `λ a b, a && !b` for `pos_num`. For example, `ldiff 5 9 = 4`:

     101
    1001
    ----
     100

  -/
def ldiff : PosNum → PosNum → Num
  | 1, bit0 q => 1
  | 1, _ => 0
  | bit0 p, 1 => Num.pos (bit0 p)
  | bit1 p, 1 => Num.pos (bit0 p)
  | bit0 p, bit0 q => Num.bit0 (ldiff p q)
  | bit0 p, bit1 q => Num.bit0 (ldiff p q)
  | bit1 p, bit0 q => Num.bit1 (ldiff p q)
  | bit1 p, bit1 q => Num.bit0 (ldiff p q)
#align pos_num.ldiff PosNum.ldiff

/-- Bitwise "xor" for `pos_num`. -/
def lxor : PosNum → PosNum → Num
  | 1, 1 => 0
  | 1, bit0 q => Num.pos (bit1 q)
  | 1, bit1 q => Num.pos (bit0 q)
  | bit0 p, 1 => Num.pos (bit1 p)
  | bit1 p, 1 => Num.pos (bit0 p)
  | bit0 p, bit0 q => Num.bit0 (lxor p q)
  | bit0 p, bit1 q => Num.bit1 (lxor p q)
  | bit1 p, bit0 q => Num.bit1 (lxor p q)
  | bit1 p, bit1 q => Num.bit0 (lxor p q)
#align pos_num.lxor PosNum.lxor

/-- `a.test_bit n` is `tt` iff the `n`-th bit (starting from the LSB) in the binary representation
      of `a` is active. If the size of `a` is less than `n`, this evaluates to `ff`. -/
def testBit : PosNum → Nat → Bool
  | 1, 0 => true
  | 1, n + 1 => false
  | bit0 p, 0 => false
  | bit0 p, n + 1 => test_bit p n
  | bit1 p, 0 => true
  | bit1 p, n + 1 => test_bit p n
#align pos_num.test_bit PosNum.testBit

/-- `n.one_bits 0` is the list of indices of active bits in the binary representation of `n`. -/
def oneBits : PosNum → Nat → List Nat
  | 1, d => [d]
  | bit0 p, d => one_bits p (d + 1)
  | bit1 p, d => d :: one_bits p (d + 1)
#align pos_num.one_bits PosNum.oneBits

/-- Left-shift the binary representation of a `pos_num`. -/
def shiftl (p : PosNum) : Nat → PosNum
  | 0 => p
  | n + 1 => bit0 (shiftl n)
#align pos_num.shiftl PosNum.shiftl

/-- Right-shift the binary representation of a `pos_num`. -/
def shiftr : PosNum → Nat → Num
  | p, 0 => Num.pos p
  | 1, n + 1 => 0
  | bit0 p, n + 1 => shiftr p n
  | bit1 p, n + 1 => shiftr p n
#align pos_num.shiftr PosNum.shiftr

end PosNum

namespace Num

/-- Bitwise "or" for `num`. -/
def lor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | Pos p, Pos q => pos (p.lor q)
#align num.lor Num.lor

/-- Bitwise "and" for `num`. -/
def land : Num → Num → Num
  | 0, q => 0
  | p, 0 => 0
  | Pos p, Pos q => p.land q
#align num.land Num.land

/-- Bitwise `λ a b, a && !b` for `num`. For example, `ldiff 5 9 = 4`:

     101
    1001
    ----
     100

  -/
def ldiff : Num → Num → Num
  | 0, q => 0
  | p, 0 => p
  | Pos p, Pos q => p.ldiff q
#align num.ldiff Num.ldiff

/-- Bitwise "xor" for `num`. -/
def lxor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | Pos p, Pos q => p.lxor q
#align num.lxor Num.lxor

/-- Left-shift the binary representation of a `num`. -/
def shiftl : Num → Nat → Num
  | 0, n => 0
  | Pos p, n => pos (p.shiftl n)
#align num.shiftl Num.shiftl

/-- Right-shift the binary representation of a `pos_num`. -/
def shiftr : Num → Nat → Num
  | 0, n => 0
  | Pos p, n => p.shiftr n
#align num.shiftr Num.shiftr

/-- `a.test_bit n` is `tt` iff the `n`-th bit (starting from the LSB) in the binary representation
      of `a` is active. If the size of `a` is less than `n`, this evaluates to `ff`. -/
def testBit : Num → Nat → Bool
  | 0, n => false
  | Pos p, n => p.testBit n
#align num.test_bit Num.testBit

/-- `n.one_bits` is the list of indices of active bits in the binary representation of `n`. -/
def oneBits : Num → List Nat
  | 0 => []
  | Pos p => p.oneBits 0
#align num.one_bits Num.oneBits

end Num

/-- This is a nonzero (and "non minus one") version of `snum`.
    See the documentation of `snum` for more details. -/
inductive Nzsnum : Type
  | msb : Bool → Nzsnum
  | bit : Bool → Nzsnum → Nzsnum
  deriving has_reflect, DecidableEq
#align nzsnum Nzsnum

/-- Alternative representation of integers using a sign bit at the end.
  The convention on sign here is to have the argument to `msb` denote
  the sign of the MSB itself, with all higher bits set to the negation
  of this sign. The result is interpreted in two's complement.

     13  = ..0001101(base 2) = nz (bit1 (bit0 (bit1 (msb tt))))
     -13 = ..1110011(base 2) = nz (bit1 (bit1 (bit0 (msb ff))))

  As with `num`, a special case must be added for zero, which has no msb,
  but by two's complement symmetry there is a second special case for -1.
  Here the `bool` field indicates the sign of the number.

     0  = ..0000000(base 2) = zero ff
     -1 = ..1111111(base 2) = zero tt -/
inductive Snum : Type
  | zero : Bool → Snum
  | nz : Nzsnum → Snum
  deriving has_reflect, DecidableEq
#align snum Snum

instance : Coe Nzsnum Snum :=
  ⟨Snum.nz⟩

instance : Zero Snum :=
  ⟨Snum.zero false⟩

instance : One Nzsnum :=
  ⟨Nzsnum.msb true⟩

instance : One Snum :=
  ⟨Snum.nz 1⟩

instance : Inhabited Nzsnum :=
  ⟨1⟩

instance : Inhabited Snum :=
  ⟨0⟩

/-!
The `snum` representation uses a bit string, essentially a list of 0 (`ff`) and 1 (`tt`) bits,
and the negation of the MSB is sign-extended to all higher bits.
-/


namespace Nzsnum

-- mathport name: nznum.bit
notation a "::" b => bit a b

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Sign of a `nzsnum`. -/
def sign : Nzsnum → Bool
  | msb b => not b
  | b::p => sign p
#align nzsnum.sign Nzsnum.sign

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Bitwise `not` for `nzsnum`. -/
@[match_pattern]
def not : Nzsnum → Nzsnum
  | msb b => msb (not b)
  | b::p => not b::Not p
#align nzsnum.not Nzsnum.not

-- mathport name: «expr~ »
prefix:100 "~" => not

/-- Add an inactive bit at the end of a `nzsnum`. This mimics `pos_num.bit0`. -/
def bit0 : Nzsnum → Nzsnum :=
  bit false
#align nzsnum.bit0 Nzsnum.bit0

/-- Add an active bit at the end of a `nzsnum`. This mimics `pos_num.bit1`. -/
def bit1 : Nzsnum → Nzsnum :=
  bit true
#align nzsnum.bit1 Nzsnum.bit1

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The `head` of a `nzsnum` is the boolean value of its LSB. -/
def head : Nzsnum → Bool
  | msb b => b
  | b::p => b
#align nzsnum.head Nzsnum.head

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The `tail` of a `nzsnum` is the `snum` obtained by removing the LSB.
      Edge cases: `tail 1 = 0` and `tail (-2) = -1`. -/
def tail : Nzsnum → Snum
  | msb b => Snum.zero (not b)
  | b::p => p
#align nzsnum.tail Nzsnum.tail

end Nzsnum

namespace Snum

open Nzsnum

/-- Sign of a `snum`. -/
def sign : Snum → Bool
  | zero z => z
  | nz p => p.sign
#align snum.sign Snum.sign

/-- Bitwise `not` for `snum`. -/
@[match_pattern]
def not : Snum → Snum
  | zero z => zero (not z)
  | nz p => ~p
#align snum.not Snum.not

-- mathport name: snum.not
prefix:0 "~" => not

/-- Add a bit at the end of a `snum`. This mimics `nzsnum.bit`. -/
@[match_pattern]
def bit : Bool → Snum → Snum
  | b, zero z => if b = z then zero b else msb b
  | b, nz p => p.bit b
#align snum.bit Snum.bit

-- mathport name: snum.bit
notation a "::" b => bit a b

/-- Add an inactive bit at the end of a `snum`. This mimics `znum.bit0`. -/
def bit0 : Snum → Snum :=
  bit false
#align snum.bit0 Snum.bit0

/-- Add an active bit at the end of a `snum`. This mimics `znum.bit1`. -/
def bit1 : Snum → Snum :=
  bit true
#align snum.bit1 Snum.bit1

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem bit_zero (b) : (b::zero b) = zero b := by cases b <;> rfl
#align snum.bit_zero Snum.bit_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem bit_one (b) : (b::zero (not b)) = msb b := by cases b <;> rfl
#align snum.bit_one Snum.bit_one

end Snum

namespace Nzsnum

open Snum

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A dependent induction principle for `nzsnum`, with base cases
      `0 : snum` and `(-1) : snum`. -/
def drec' {C : Snum → Sort _} (z : ∀ b, C (Snum.zero b)) (s : ∀ b p, C p → C (b::p)) :
    ∀ p : Nzsnum, C p
  | msb b => by rw [← bit_one] <;> exact s b (Snum.zero (not b)) (z (not b))
  | bit b p => s b p (drec' p)
#align nzsnum.drec' Nzsnum.drec'

end Nzsnum

namespace Snum

open Nzsnum

/-- The `head` of a `snum` is the boolean value of its LSB. -/
def head : Snum → Bool
  | zero z => z
  | nz p => p.head
#align snum.head Snum.head

/-- The `tail` of a `snum` is obtained by removing the LSB.
      Edge cases: `tail 1 = 0`, `tail (-2) = -1`, `tail 0 = 0` and `tail (-1) = -1`. -/
def tail : Snum → Snum
  | zero z => zero z
  | nz p => p.tail
#align snum.tail Snum.tail

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A dependent induction principle for `snum` which avoids relying on `nzsnum`. -/
def drec' {C : Snum → Sort _} (z : ∀ b, C (Snum.zero b)) (s : ∀ b p, C p → C (b::p)) : ∀ p, C p
  | zero b => z b
  | nz p => p.drec' z s
#align snum.drec' Snum.drec'

/-- An induction principle for `snum` which avoids relying on `nzsnum`. -/
def rec' {α} (z : Bool → α) (s : Bool → Snum → α → α) : Snum → α :=
  drec' z s
#align snum.rec' Snum.rec'

/-- `snum.test_bit n a` is `tt` iff the `n`-th bit (starting from the LSB) of `a` is active.
      If the size of `a` is less than `n`, this evaluates to `ff`. -/
def testBit : Nat → Snum → Bool
  | 0, p => head p
  | n + 1, p => test_bit n (tail p)
#align snum.test_bit Snum.testBit

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The successor of a `snum` (i.e. the operation adding one). -/
def succ : Snum → Snum :=
  rec' (fun b => cond b 0 1) fun b p succp => cond b (ff::succp) (tt::p)
#align snum.succ Snum.succ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The predecessor of a `snum` (i.e. the operation of removing one). -/
def pred : Snum → Snum :=
  rec' (fun b => cond b (~1) (~0)) fun b p predp => cond b (ff::p) (tt::predp)
#align snum.pred Snum.pred

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The opposite of a `snum`. -/
protected def neg (n : Snum) : Snum :=
  succ (~n)
#align snum.neg Snum.neg

instance : Neg Snum :=
  ⟨Snum.neg⟩

/-- `snum.czadd a b n` is `n + a - b` (where `a` and `b` should be read as either 0 or 1).
      This is useful to implement the carry system in `cadd`. -/
def czadd : Bool → Bool → Snum → Snum
  | ff, ff, p => p
  | ff, tt, p => pred p
  | tt, ff, p => succ p
  | tt, tt, p => p
#align snum.czadd Snum.czadd

end Snum

namespace Snum

/-- `a.bits n` is the vector of the `n` first bits of `a` (starting from the LSB). -/
def bits : Snum → ∀ n, Vector Bool n
  | p, 0 => Vector.nil
  | p, n + 1 => head p ::ᵥ bits (tail p) n
#align snum.bits Snum.bits

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
def cadd : Snum → Snum → Bool → Snum :=
  rec' (fun a p c => czadd c a p) fun a p IH =>
    rec' (fun b c => czadd c b (a::p)) fun b q _ c => Bitvec.xor3 a b c::IH q (Bitvec.carry a b c)
#align snum.cadd Snum.cadd

/-- Add two `snum`s. -/
protected def add (a b : Snum) : Snum :=
  cadd a b false
#align snum.add Snum.add

instance : Add Snum :=
  ⟨Snum.add⟩

/-- subtract two `snum`s. -/
protected def sub (a b : Snum) : Snum :=
  a + -b
#align snum.sub Snum.sub

instance : Sub Snum :=
  ⟨Snum.sub⟩

/-- Multiply two `snum`s. -/
protected def mul (a : Snum) : Snum → Snum :=
  rec' (fun b => cond b (-a) 0) fun b q IH => cond b (bit0 IH + a) (bit0 IH)
#align snum.mul Snum.mul

instance : Mul Snum :=
  ⟨Snum.mul⟩

end Snum


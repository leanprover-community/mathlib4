/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Num.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Vector.Basic

#align_import data.num.bitwise from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Bitwise operations using binary representation of integers

## Definitions

* bitwise operations for `PosNum` and `Num`,
* `SNum`, a type that represents integers as a bit string with a sign bit at the end,
* arithmetic operations for `SNum`.
-/


namespace PosNum

/-- Bitwise "or" for `PosNum`. -/
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

instance : OrOp PosNum where or := PosNum.lor

@[simp] lemma lor_eq_or (p q : PosNum) : p.lor q = p ||| q := rfl

/-- Bitwise "and" for `PosNum`. -/
def land : PosNum → PosNum → Num
  | 1, bit0 _ => 0
  | 1, _ => 1
  | bit0 _, 1 => 0
  | _, 1 => 1
  | bit0 p, bit0 q => Num.bit0 (land p q)
  | bit0 p, bit1 q => Num.bit0 (land p q)
  | bit1 p, bit0 q => Num.bit0 (land p q)
  | bit1 p, bit1 q => Num.bit1 (land p q)
#align pos_num.land PosNum.land

instance : HAnd PosNum PosNum Num where hAnd := PosNum.land

@[simp] lemma land_eq_and (p q : PosNum) : p.land q = p &&& q := rfl

/-- Bitwise `fun a b ↦ a && !b` for `PosNum`. For example, `ldiff 5 9 = 4`:
```
 101
1001
----
 100
```
-/
def ldiff : PosNum → PosNum → Num
  | 1, bit0 _ => 1
  | 1, _ => 0
  | bit0 p, 1 => Num.pos (bit0 p)
  | bit1 p, 1 => Num.pos (bit0 p)
  | bit0 p, bit0 q => Num.bit0 (ldiff p q)
  | bit0 p, bit1 q => Num.bit0 (ldiff p q)
  | bit1 p, bit0 q => Num.bit1 (ldiff p q)
  | bit1 p, bit1 q => Num.bit0 (ldiff p q)
#align pos_num.ldiff PosNum.ldiff

/-- Bitwise "xor" for `PosNum`. -/
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

instance : HXor PosNum PosNum Num where hXor := PosNum.lxor

@[simp] lemma lxor_eq_xor (p q : PosNum) : p.lxor q = p ^^^ q := rfl

/-- `a.testBit n` is `true` iff the `n`-th bit (starting from the LSB) in the binary representation
      of `a` is active. If the size of `a` is less than `n`, this evaluates to `false`. -/
def testBit : PosNum → Nat → Bool
  | 1, 0 => true
  | 1, _ => false
  | bit0 _, 0 => false
  | bit0 p, n + 1 => testBit p n
  | bit1 _, 0 => true
  | bit1 p, n + 1 => testBit p n
#align pos_num.test_bit PosNum.testBit

/-- `n.oneBits 0` is the list of indices of active bits in the binary representation of `n`. -/
def oneBits : PosNum → Nat → List Nat
  | 1, d => [d]
  | bit0 p, d => oneBits p (d + 1)
  | bit1 p, d => d :: oneBits p (d + 1)
#align pos_num.one_bits PosNum.oneBits

/-- Left-shift the binary representation of a `PosNum`. -/
def shiftl : PosNum → Nat → PosNum
  | p, 0 => p
  | p, n + 1 => shiftl p.bit0 n
#align pos_num.shiftl PosNum.shiftl

instance : HShiftLeft PosNum Nat PosNum where hShiftLeft := PosNum.shiftl

@[simp] lemma shiftl_eq_shiftLeft (p : PosNum) (n : Nat) : p.shiftl n = p <<< n := rfl


-- Porting note: `PosNum.shiftl` is defined as tail-recursive in Lean4.
--               This theorem ensures the definition is same to one in Lean3.
theorem shiftl_succ_eq_bit0_shiftl : ∀ (p : PosNum) (n : Nat), p <<< n.succ = bit0 (p <<< n)
  | _, 0       => rfl
  | p, .succ n => shiftl_succ_eq_bit0_shiftl p.bit0 n

/-- Right-shift the binary representation of a `PosNum`. -/
def shiftr : PosNum → Nat → Num
  | p, 0 => Num.pos p
  | 1, _ => 0
  | bit0 p, n + 1 => shiftr p n
  | bit1 p, n + 1 => shiftr p n
#align pos_num.shiftr PosNum.shiftr

instance : HShiftRight PosNum Nat Num where hShiftRight := PosNum.shiftr

@[simp] lemma shiftr_eq_shiftRight (p : PosNum) (n : Nat) : p.shiftr n = p >>> n := rfl

end PosNum

namespace Num

/-- Bitwise "or" for `Num`. -/
protected def lor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | pos p, pos q => pos (p ||| q)
#align num.lor OrOp.or

instance : OrOp Num where or := Num.lor

@[simp] lemma lor_eq_or (p q : Num) : p.lor q = p ||| q := rfl

/-- Bitwise "and" for `Num`. -/
def land : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | pos p, pos q => p &&& q
#align num.land Num.land

instance : AndOp Num where and := Num.land

@[simp] lemma land_eq_and (p q : Num) : p.land q = p &&& q := rfl

/-- Bitwise `fun a b ↦ a && !b` for `Num`. For example, `ldiff 5 9 = 4`:
```
 101
1001
----
 100
```
-/
def ldiff : Num → Num → Num
  | 0, _ => 0
  | p, 0 => p
  | pos p, pos q => p.ldiff q
#align num.ldiff Num.ldiff

/-- Bitwise "xor" for `Num`. -/
def lxor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | pos p, pos q => p ^^^ q
#align num.lxor Num.lxor

instance : Xor Num where xor := Num.lxor

@[simp] lemma lxor_eq_xor (p q : Num) : p.lxor q = p ^^^ q := rfl

/-- Left-shift the binary representation of a `Num`. -/
def shiftl : Num → Nat → Num
  | 0, _ => 0
  | pos p, n => pos (p <<< n)
#align num.shiftl Num.shiftl

instance : HShiftLeft Num Nat Num where hShiftLeft := Num.shiftl

@[simp] lemma shiftl_eq_shiftLeft (p : Num) (n : Nat) : p.shiftl n = p <<< n := rfl

/-- Right-shift the binary representation of a `Num`. -/
def shiftr : Num → Nat → Num
  | 0, _ => 0
  | pos p, n => p >>> n
#align num.shiftr Num.shiftr

instance : HShiftRight Num Nat Num where hShiftRight := Num.shiftr

@[simp] lemma shiftr_eq_shiftRight (p : Num) (n : Nat) : p.shiftr n = p >>> n := rfl

/-- `a.testBit n` is `true` iff the `n`-th bit (starting from the LSB) in the binary representation
      of `a` is active. If the size of `a` is less than `n`, this evaluates to `false`. -/
def testBit : Num → Nat → Bool
  | 0, _ => false
  | pos p, n => p.testBit n
#align num.test_bit Num.testBit

/-- `n.oneBits` is the list of indices of active bits in the binary representation of `n`. -/
def oneBits : Num → List Nat
  | 0 => []
  | pos p => p.oneBits 0
#align num.one_bits Num.oneBits

end Num

/-- This is a nonzero (and "non minus one") version of `SNum`.
    See the documentation of `SNum` for more details. -/
inductive NzsNum : Type
  | msb : Bool → NzsNum
  /-- Add a bit at the end of a `NzsNum`. -/
  | bit : Bool → NzsNum → NzsNum
  deriving DecidableEq  -- Porting note: Removed `deriving has_reflect`.
#align nzsnum NzsNum

/-- Alternative representation of integers using a sign bit at the end.
  The convention on sign here is to have the argument to `msb` denote
  the sign of the MSB itself, with all higher bits set to the negation
  of this sign. The result is interpreted in two's complement.

     13  = ..0001101(base 2) = nz (bit1 (bit0 (bit1 (msb true))))
     -13 = ..1110011(base 2) = nz (bit1 (bit1 (bit0 (msb false))))

  As with `Num`, a special case must be added for zero, which has no msb,
  but by two's complement symmetry there is a second special case for -1.
  Here the `Bool` field indicates the sign of the number.

     0  = ..0000000(base 2) = zero false
     -1 = ..1111111(base 2) = zero true -/
inductive SNum : Type
  | zero : Bool → SNum
  | nz : NzsNum → SNum
  deriving DecidableEq  -- Porting note: Removed `deriving has_reflect`.
#align snum SNum

instance : Coe NzsNum SNum :=
  ⟨SNum.nz⟩

instance : Zero SNum :=
  ⟨SNum.zero false⟩

instance : One NzsNum :=
  ⟨NzsNum.msb true⟩

instance : One SNum :=
  ⟨SNum.nz 1⟩

instance : Inhabited NzsNum :=
  ⟨1⟩

instance : Inhabited SNum :=
  ⟨0⟩

/-!
The `SNum` representation uses a bit string, essentially a list of 0 (`false`) and 1 (`true`) bits,
and the negation of the MSB is sign-extended to all higher bits.
-/


namespace NzsNum

@[inherit_doc]
scoped notation a "::" b => bit a b

/-- Sign of a `NzsNum`. -/
def sign : NzsNum → Bool
  | msb b => not b
  | _ :: p => sign p
#align nzsnum.sign NzsNum.sign

/-- Bitwise `not` for `NzsNum`. -/
@[match_pattern]
def not : NzsNum → NzsNum
  | msb b => msb (Not b)
  | b :: p => Not b :: not p
#align nzsnum.not NzsNum.not

@[inherit_doc]
scoped prefix:100 "~" => not

/-- Add an inactive bit at the end of a `NzsNum`. This mimics `PosNum.bit0`. -/
def bit0 : NzsNum → NzsNum :=
  bit false
#align nzsnum.bit0 NzsNum.bit0

/-- Add an active bit at the end of a `NzsNum`. This mimics `PosNum.bit1`. -/
def bit1 : NzsNum → NzsNum :=
  bit true
#align nzsnum.bit1 NzsNum.bit1

/-- The `head` of a `NzsNum` is the boolean value of its LSB. -/
def head : NzsNum → Bool
  | msb b => b
  | b :: _ => b
#align nzsnum.head NzsNum.head

/-- The `tail` of a `NzsNum` is the `SNum` obtained by removing the LSB.
      Edge cases: `tail 1 = 0` and `tail (-2) = -1`. -/
def tail : NzsNum → SNum
  | msb b => SNum.zero (Not b)
  | _ :: p => p
#align nzsnum.tail NzsNum.tail

end NzsNum

namespace SNum

open NzsNum

/-- Sign of a `SNum`. -/
def sign : SNum → Bool
  | zero z => z
  | nz p => p.sign
#align snum.sign SNum.sign

/-- Bitwise `not` for `SNum`. -/
@[match_pattern]
def not : SNum → SNum
  | zero z => zero (Not z)
  | nz p => ~p
#align snum.not SNum.not

-- Porting note: Defined `priority` so that `~1 : SNum` is unambiguous.
@[inherit_doc]
scoped prefix:100 (priority := default + 1) "~" => not

/-- Add a bit at the end of a `SNum`. This mimics `NzsNum.bit`. -/
@[match_pattern]
def bit : Bool → SNum → SNum
  | b, zero z => if b = z then zero b else msb b
  | b, nz p => p.bit b
#align snum.bit SNum.bit

@[inherit_doc]
scoped notation a "::" b => bit a b

/-- Add an inactive bit at the end of a `SNum`. This mimics `ZNum.bit0`. -/
def bit0 : SNum → SNum :=
  bit false
#align snum.bit0 SNum.bit0

/-- Add an active bit at the end of a `SNum`. This mimics `ZNum.bit1`. -/
def bit1 : SNum → SNum :=
  bit true
#align snum.bit1 SNum.bit1

theorem bit_zero (b : Bool) : (b :: zero b) = zero b := by cases b <;> rfl
#align snum.bit_zero SNum.bit_zero

theorem bit_one (b : Bool) : (b :: zero (Not b)) = msb b := by cases b <;> rfl
#align snum.bit_one SNum.bit_one

end SNum

namespace NzsNum

open SNum

/-- A dependent induction principle for `NzsNum`, with base cases
      `0 : SNum` and `(-1) : SNum`. -/
def drec' {C : SNum → Sort*} (z : ∀ b, C (SNum.zero b)) (s : ∀ b p, C p → C (b :: p)) :
    ∀ p : NzsNum, C p
  | msb b => by rw [← bit_one]; exact s b (SNum.zero (Not b)) (z (Not b))
  | bit b p => s b p (drec' z s p)
#align nzsnum.drec' NzsNum.drec'

end NzsNum

namespace SNum

open NzsNum

/-- The `head` of a `SNum` is the boolean value of its LSB. -/
def head : SNum → Bool
  | zero z => z
  | nz p => p.head
#align snum.head SNum.head

/-- The `tail` of a `SNum` is obtained by removing the LSB.
      Edge cases: `tail 1 = 0`, `tail (-2) = -1`, `tail 0 = 0` and `tail (-1) = -1`. -/
def tail : SNum → SNum
  | zero z => zero z
  | nz p => p.tail
#align snum.tail SNum.tail

/-- A dependent induction principle for `SNum` which avoids relying on `NzsNum`. -/
def drec' {C : SNum → Sort*} (z : ∀ b, C (SNum.zero b)) (s : ∀ b p, C p → C (b :: p)) : ∀ p, C p
  | zero b => z b
  | nz p => p.drec' z s
#align snum.drec' SNum.drec'

/-- An induction principle for `SNum` which avoids relying on `NzsNum`. -/
def rec' {α} (z : Bool → α) (s : Bool → SNum → α → α) : SNum → α :=
  drec' z s
#align snum.rec' SNum.rec'

/-- `SNum.testBit n a` is `true` iff the `n`-th bit (starting from the LSB) of `a` is active.
      If the size of `a` is less than `n`, this evaluates to `false`. -/
def testBit : Nat → SNum → Bool
  | 0, p => head p
  | n + 1, p => testBit n (tail p)
#align snum.test_bit SNum.testBit

/-- The successor of a `SNum` (i.e. the operation adding one). -/
def succ : SNum → SNum :=
  rec' (fun b ↦ cond b 0 1) fun b p succp ↦ cond b (false :: succp) (true :: p)
#align snum.succ SNum.succ

/-- The predecessor of a `SNum` (i.e. the operation of removing one). -/
def pred : SNum → SNum :=
  rec' (fun b ↦ cond b (~1) (~0)) fun b p predp ↦ cond b (false :: p) (true :: predp)
#align snum.pred SNum.pred

/-- The opposite of a `SNum`. -/
protected def neg (n : SNum) : SNum :=
  succ (~n)
#align snum.neg SNum.neg

instance : Neg SNum :=
  ⟨SNum.neg⟩

/-- `SNum.czAdd a b n` is `n + a - b` (where `a` and `b` should be read as either 0 or 1).
      This is useful to implement the carry system in `cAdd`. -/
def czAdd : Bool → Bool → SNum → SNum
  | false, false, p => p
  | false, true, p => pred p
  | true, false, p => succ p
  | true, true, p => p
#align snum.czadd SNum.czAdd

end SNum

namespace SNum

/-- `a.bits n` is the vector of the `n` first bits of `a` (starting from the LSB). -/
def bits : SNum → ∀ n, Vector Bool n
  | _, 0 => Vector.nil
  | p, n + 1 => head p ::ᵥ bits (tail p) n
#align snum.bits SNum.bits

/-- `SNum.cAdd n m a` is `n + m + a` (where `a` should be read as either 0 or 1).
      `a` represents a carry bit. -/
def cAdd : SNum → SNum → Bool → SNum :=
  rec' (fun a p c ↦ czAdd c a p) fun a p IH ↦
    rec' (fun b c ↦ czAdd c b (a :: p)) fun b q _ c ↦ Bool.xor3 a b c :: IH q (Bool.carry a b c)
#align snum.cadd SNum.cAdd

/-- Add two `SNum`s. -/
protected def add (a b : SNum) : SNum :=
  cAdd a b false
#align snum.add SNum.add

instance : Add SNum :=
  ⟨SNum.add⟩

/-- Subtract two `SNum`s. -/
protected def sub (a b : SNum) : SNum :=
  a + -b
#align snum.sub SNum.sub

instance : Sub SNum :=
  ⟨SNum.sub⟩

/-- Multiply two `SNum`s. -/
protected def mul (a : SNum) : SNum → SNum :=
  rec' (fun b ↦ cond b (-a) 0) fun b _ IH ↦ cond b (bit0 IH + a) (bit0 IH)
#align snum.mul SNum.mul

instance : Mul SNum :=
  ⟨SNum.mul⟩

end SNum

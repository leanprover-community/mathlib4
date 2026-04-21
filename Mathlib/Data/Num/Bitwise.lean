/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Num.Basic
public import Mathlib.Data.Vector.Basic

/-!
# Bitwise operations using binary representation of integers

## Definitions

* bitwise operations for `PosNum` and `Num`,
* `SNum`, a type that represents integers as a bit string with a sign bit at the end,
* arithmetic operations for `SNum`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open List (Vector)

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

/-- `n.oneBits 0` is the list of indices of active bits in the binary representation of `n`. -/
def oneBits : PosNum → Nat → List Nat
  | 1, d => [d]
  | bit0 p, d => oneBits p (d + 1)
  | bit1 p, d => d :: oneBits p (d + 1)

/-- Left-shift the binary representation of a `PosNum`. -/
def shiftl : PosNum → Nat → PosNum
  | p, 0 => p
  | p, n + 1 => shiftl p.bit0 n

instance : HShiftLeft PosNum Nat PosNum where hShiftLeft := PosNum.shiftl

@[simp] lemma shiftl_eq_shiftLeft (p : PosNum) (n : Nat) : p.shiftl n = p <<< n := rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
-- This shows that the tail-recursive definition is the same as the more naïve recursion.
theorem shiftl_succ_eq_bit0_shiftl : ∀ (p : PosNum) (n : Nat), p <<< n.succ = bit0 (p <<< n)
  | _, 0       => rfl
  | p, .succ n => shiftl_succ_eq_bit0_shiftl p.bit0 n

/-- Right-shift the binary representation of a `PosNum`. -/
def shiftr : PosNum → Nat → Num
  | p, 0 => Num.pos p
  | 1, _ => 0
  | bit0 p, n + 1 => shiftr p n
  | bit1 p, n + 1 => shiftr p n

instance : HShiftRight PosNum Nat Num where hShiftRight := PosNum.shiftr

@[simp] lemma shiftr_eq_shiftRight (p : PosNum) (n : Nat) : p.shiftr n = p >>> n := rfl

end PosNum

namespace Num

/-- Bitwise "or" for `Num`. -/
protected def lor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | pos p, pos q => pos (p ||| q)

instance : OrOp Num where or := Num.lor

@[simp] lemma lor_eq_or (p q : Num) : p.lor q = p ||| q := rfl

/-- Bitwise "and" for `Num`. -/
def land : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | pos p, pos q => p &&& q

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

/-- Bitwise "xor" for `Num`. -/
def lxor : Num → Num → Num
  | 0, q => q
  | p, 0 => p
  | pos p, pos q => p ^^^ q

instance : XorOp Num where xor := Num.lxor

@[simp] lemma lxor_eq_xor (p q : Num) : p.lxor q = p ^^^ q := rfl

/-- Left-shift the binary representation of a `Num`. -/
def shiftl : Num → Nat → Num
  | 0, _ => 0
  | pos p, n => pos (p <<< n)

instance : HShiftLeft Num Nat Num where hShiftLeft := Num.shiftl

@[simp] lemma shiftl_eq_shiftLeft (p : Num) (n : Nat) : p.shiftl n = p <<< n := rfl

/-- Right-shift the binary representation of a `Num`. -/
def shiftr : Num → Nat → Num
  | 0, _ => 0
  | pos p, n => p >>> n

instance : HShiftRight Num Nat Num where hShiftRight := Num.shiftr

@[simp] lemma shiftr_eq_shiftRight (p : Num) (n : Nat) : p.shiftr n = p >>> n := rfl

/-- `a.testBit n` is `true` iff the `n`-th bit (starting from the LSB) in the binary representation
of `a` is active. If the size of `a` is less than `n`, this evaluates to `false`. -/
def testBit : Num → Nat → Bool
  | 0, _ => false
  | pos p, n => p.testBit n

/-- `n.oneBits` is the list of indices of active bits in the binary representation of `n`. -/
def oneBits : Num → List Nat
  | 0 => []
  | pos p => p.oneBits 0

end Num

/-- This is a nonzero (and "non minus one") version of `SNum`.
See the documentation of `SNum` for more details. -/
inductive NzsNum : Type
  | msb : Bool → NzsNum
  /-- Add a bit at the end of a `NzsNum`. -/
  | bit : Bool → NzsNum → NzsNum
  deriving DecidableEq

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
  deriving DecidableEq

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

/-- Bitwise `not` for `NzsNum`. -/
@[match_pattern]
def not : NzsNum → NzsNum
  | msb b => msb (Not b)
  | b :: p => Not b :: not p

@[inherit_doc]
scoped prefix:100 "~" => not

/-- Add an inactive bit at the end of a `NzsNum`. This mimics `PosNum.bit0`. -/
def bit0 : NzsNum → NzsNum :=
  bit false

/-- Add an active bit at the end of a `NzsNum`. This mimics `PosNum.bit1`. -/
def bit1 : NzsNum → NzsNum :=
  bit true

/-- The `head` of a `NzsNum` is the Boolean value of its LSB. -/
def head : NzsNum → Bool
  | msb b => b
  | b :: _ => b

/-- The `tail` of a `NzsNum` is the `SNum` obtained by removing the LSB.
Edge cases: `tail 1 = 0` and `tail (-2) = -1`. -/
def tail : NzsNum → SNum
  | msb b => SNum.zero (Not b)
  | _ :: p => p

end NzsNum

namespace SNum

open NzsNum

/-- Sign of a `SNum`. -/
def sign : SNum → Bool
  | zero z => z
  | nz p => p.sign

/-- Bitwise `not` for `SNum`. -/
@[match_pattern]
def not : SNum → SNum
  | zero z => zero (Not z)
  | nz p => ~p

-- Higher `priority` so that `~1 : SNum` is unambiguous.
@[inherit_doc]
scoped prefix:100 (priority := default + 1) "~" => not

/-- Add a bit at the end of a `SNum`. This mimics `NzsNum.bit`. -/
@[match_pattern]
def bit : Bool → SNum → SNum
  | b, zero z => if b = z then zero b else msb b
  | b, nz p => p.bit b

@[inherit_doc]
scoped notation a "::" b => bit a b

/-- Add an inactive bit at the end of a `SNum`. This mimics `ZNum.bit0`. -/
def bit0 : SNum → SNum :=
  bit false

/-- Add an active bit at the end of a `SNum`. This mimics `ZNum.bit1`. -/
def bit1 : SNum → SNum :=
  bit true

theorem bit_zero (b : Bool) : (b :: zero b) = zero b := by cases b <;> rfl

theorem bit_one (b : Bool) : (b :: zero (Not b)) = msb b := by cases b <;> rfl

end SNum

namespace NzsNum

open SNum

/-- A dependent induction principle for `NzsNum`, with base cases `0 : SNum` and `(-1) : SNum`. -/
def drec' {C : SNum → Sort*} (z : ∀ b, C (SNum.zero b)) (s : ∀ b p, C p → C (b :: p)) :
    ∀ p : NzsNum, C p
  | msb b => by rw [← bit_one]; exact s b (SNum.zero (Not b)) (z (Not b))
  | bit b p => s b p (drec' z s p)

end NzsNum

namespace SNum

open NzsNum

/-- The `head` of a `SNum` is the Boolean value of its LSB. -/
def head : SNum → Bool
  | zero z => z
  | nz p => p.head

/-- The `tail` of a `SNum` is obtained by removing the LSB.
Edge cases: `tail 1 = 0`, `tail (-2) = -1`, `tail 0 = 0` and `tail (-1) = -1`. -/
def tail : SNum → SNum
  | zero z => zero z
  | nz p => p.tail

/-- A dependent induction principle for `SNum` which avoids relying on `NzsNum`. -/
def drec' {C : SNum → Sort*} (z : ∀ b, C (SNum.zero b)) (s : ∀ b p, C p → C (b :: p)) : ∀ p, C p
  | zero b => z b
  | nz p => p.drec' z s

/-- An induction principle for `SNum` which avoids relying on `NzsNum`. -/
def rec' {α} (z : Bool → α) (s : Bool → SNum → α → α) : SNum → α :=
  drec' z s

/-- `SNum.testBit n a` is `true` iff the `n`-th bit (starting from the LSB) of `a` is active.
If the size of `a` is less than `n`, this evaluates to `false`. -/
def testBit : Nat → SNum → Bool
  | 0, p => head p
  | n + 1, p => testBit n (tail p)

/-- The successor of a `SNum` (i.e. the operation adding one). -/
def succ : SNum → SNum :=
  rec' (fun b ↦ cond b 0 1) fun b p succp ↦ cond b (false :: succp) (true :: p)

/-- The predecessor of a `SNum` (i.e. the operation of removing one). -/
def pred : SNum → SNum :=
  rec' (fun b ↦ cond b (~1) (~0)) fun b p predp ↦ cond b (false :: p) (true :: predp)

/-- The opposite of a `SNum`. -/
protected def neg (n : SNum) : SNum :=
  succ (~n)

instance : Neg SNum :=
  ⟨SNum.neg⟩

/-- `SNum.czAdd a b n` is `n + a - b` (where `a` and `b` should be read as either 0 or 1).
This is useful to implement the carry system in `cAdd`. -/
def czAdd : Bool → Bool → SNum → SNum
  | false, false, p => p
  | false, true, p => pred p
  | true, false, p => succ p
  | true, true, p => p

end SNum

namespace SNum

/-- `a.bits n` is the vector of the `n` first bits of `a` (starting from the LSB). -/
def bits : SNum → ∀ n, List.Vector Bool n
  | _, 0 => Vector.nil
  | p, n + 1 => head p ::ᵥ bits (tail p) n

/-- `SNum.cAdd n m a` is `n + m + a` (where `a` should be read as either 0 or 1).
`a` represents a carry bit. -/
def cAdd : SNum → SNum → Bool → SNum :=
  rec' (fun a p c ↦ czAdd c a p) fun a p IH ↦
    rec' (fun b c ↦ czAdd c b (a :: p)) fun b q _ c ↦ Bool.xor3 a b c :: IH q (Bool.carry a b c)

/-- Add two `SNum`s. -/
protected def add (a b : SNum) : SNum :=
  cAdd a b false

instance : Add SNum :=
  ⟨SNum.add⟩

/-- Subtract two `SNum`s. -/
protected def sub (a b : SNum) : SNum :=
  a + -b

instance : Sub SNum :=
  ⟨SNum.sub⟩

/-- Multiply two `SNum`s. -/
protected def mul (a : SNum) : SNum → SNum :=
  rec' (fun b ↦ cond b (-a) 0) fun b _ IH ↦ cond b (bit0 IH + a) (bit0 IH)

instance : Mul SNum :=
  ⟨SNum.mul⟩

end SNum

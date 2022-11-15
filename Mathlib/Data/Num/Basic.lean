/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/

/-!
# Binary representation of integers using inductive types

Note: Unlike in Coq, where this representation is preferred because of
the reliance on kernel reduction, in Lean this representation is discouraged
in favor of the "Peano" natural numbers `nat`, and the purpose of this
collection of theorems is to show the equivalence of the different approaches.
-/


/-- The type of positive binary numbers.

     13 = 1101(base 2) = bit1 (bit0 (bit1 one)) -/
inductive PosNum : Type
  | one : PosNum
  | bit1 : PosNum → PosNum
  | bit0 : PosNum → PosNum
  deriving has_reflect, DecidableEq
#align pos_num PosNum

instance : One PosNum :=
  ⟨PosNum.one⟩

instance : Inhabited PosNum :=
  ⟨1⟩

/-- The type of nonnegative binary numbers, using `pos_num`.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one))) -/
inductive Num : Type
  | zero : Num
  | Pos : PosNum → Num
  deriving has_reflect, DecidableEq
#align num Num

instance : Zero Num :=
  ⟨Num.zero⟩

instance : One Num :=
  ⟨Num.pos 1⟩

instance : Inhabited Num :=
  ⟨0⟩

/-- Representation of integers using trichotomy around zero.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one)))
     -13 = -1101(base 2) = neg (bit1 (bit0 (bit1 one))) -/
inductive Znum : Type
  | zero : Znum
  | Pos : PosNum → Znum
  | neg : PosNum → Znum
  deriving has_reflect, DecidableEq
#align znum Znum

instance : Zero Znum :=
  ⟨Znum.zero⟩

instance : One Znum :=
  ⟨Znum.pos 1⟩

instance : Inhabited Znum :=
  ⟨0⟩

namespace PosNum

/-- `bit b n` appends the bit `b` to the end of `n`, where `bit tt x = x1` and `bit ff x = x0`.
  -/
def bit (b : Bool) : PosNum → PosNum :=
  cond b bit1 bit0
#align pos_num.bit PosNum.bit

/-- The successor of a `pos_num`.
  -/
def succ : PosNum → PosNum
  | 1 => bit0 one
  | bit1 n => bit0 (succ n)
  | bit0 n => bit1 n
#align pos_num.succ PosNum.succ

/-- Returns a boolean for whether the `pos_num` is `one`.
  -/
def isOne : PosNum → Bool
  | 1 => true
  | _ => false
#align pos_num.is_one PosNum.isOne

/-- Addition of two `pos_num`s.
  -/
protected def add : PosNum → PosNum → PosNum
  | 1, b => succ b
  | a, 1 => succ a
  | bit0 a, bit0 b => bit0 (add a b)
  | bit1 a, bit1 b => bit0 (succ (add a b))
  | bit0 a, bit1 b => bit1 (add a b)
  | bit1 a, bit0 b => bit1 (add a b)
#align pos_num.add PosNum.add

instance : Add PosNum :=
  ⟨PosNum.add⟩

/-- The predecessor of a `pos_num` as a `num`.
  -/
def pred' : PosNum → Num
  | 1 => 0
  | bit0 n => Num.pos (Num.casesOn (pred' n) 1 bit1)
  | bit1 n => Num.pos (bit0 n)
#align pos_num.pred' PosNum.pred'

/-- The predecessor of a `pos_num` as a `pos_num`. This means that `pred 1 = 1`.
  -/
def pred (a : PosNum) : PosNum :=
  Num.casesOn (pred' a) 1 id
#align pos_num.pred PosNum.pred

/-- The number of bits of a `pos_num`, as a `pos_num`.
  -/
def size : PosNum → PosNum
  | 1 => 1
  | bit0 n => succ (size n)
  | bit1 n => succ (size n)
#align pos_num.size PosNum.size

/-- The number of bits of a `pos_num`, as a `nat`.
  -/
def natSize : PosNum → Nat
  | 1 => 1
  | bit0 n => Nat.succ (nat_size n)
  | bit1 n => Nat.succ (nat_size n)
#align pos_num.nat_size PosNum.natSize

/-- Multiplication of two `pos_num`s.
  -/
protected def mul (a : PosNum) : PosNum → PosNum
  | 1 => a
  | bit0 b => bit0 (mul b)
  | bit1 b => bit0 (mul b) + a
#align pos_num.mul PosNum.mul

instance : Mul PosNum :=
  ⟨PosNum.mul⟩

/-- `of_nat_succ n` is the `pos_num` corresponding to `n + 1`.
  -/
def ofNatSucc : ℕ → PosNum
  | 0 => 1
  | Nat.succ n => succ (of_nat_succ n)
#align pos_num.of_nat_succ PosNum.ofNatSucc

/-- `of_nat n` is the `pos_num` corresponding to `n`, except for `of_nat 0 = 1`.
  -/
def ofNat (n : ℕ) : PosNum :=
  ofNatSucc (Nat.pred n)
#align pos_num.of_nat PosNum.ofNat

open Ordering

/-- Ordering of `pos_num`s.
  -/
def cmp : PosNum → PosNum → Ordering
  | 1, 1 => Eq
  | _, 1 => GT.gt
  | 1, _ => lt
  | bit0 a, bit0 b => Cmp a b
  | bit0 a, bit1 b => Ordering.casesOn (Cmp a b) lt lt GT.gt
  | bit1 a, bit0 b => Ordering.casesOn (Cmp a b) lt GT.gt GT.gt
  | bit1 a, bit1 b => Cmp a b
#align pos_num.cmp PosNum.cmp

instance : LT PosNum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

instance : LE PosNum :=
  ⟨fun a b => ¬b < a⟩

instance decidableLt : @DecidableRel PosNum (· < ·)
  | a, b => by dsimp [(· < ·)] <;> infer_instance
#align pos_num.decidable_lt PosNum.decidableLt

instance decidableLe : @DecidableRel PosNum (· ≤ ·)
  | a, b => by dsimp [(· ≤ ·)] <;> infer_instance
#align pos_num.decidable_le PosNum.decidableLe

end PosNum

section

variable {α : Type _} [One α] [Add α]

/-- `cast_pos_num` casts a `pos_num` into any type which has `1` and `+`.
  -/
def castPosNum : PosNum → α
  | 1 => 1
  | PosNum.bit0 a => bit0 (castPosNum a)
  | PosNum.bit1 a => bit1 (castPosNum a)
#align cast_pos_num castPosNum

/-- `cast_num` casts a `num` into any type which has `0`, `1` and `+`.
  -/
def castNum [z : Zero α] : Num → α
  | 0 => 0
  | Num.pos p => castPosNum p
#align cast_num castNum

-- see Note [coercion into rings]
instance (priority := 900) posNumCoe : CoeTC PosNum α :=
  ⟨castPosNum⟩
#align pos_num_coe posNumCoe

-- see Note [coercion into rings]
instance (priority := 900) numNatCoe [z : Zero α] : CoeTC Num α :=
  ⟨castNum⟩
#align num_nat_coe numNatCoe

instance : Repr PosNum :=
  ⟨fun n => repr (n : ℕ)⟩

instance : Repr Num :=
  ⟨fun n => repr (n : ℕ)⟩

end

namespace Num

open PosNum

/-- The successor of a `num` as a `pos_num`.
  -/
def succ' : Num → PosNum
  | 0 => 1
  | Pos p => succ p
#align num.succ' Num.succ'

/-- The successor of a `num` as a `num`.
  -/
def succ (n : Num) : Num :=
  pos (succ' n)
#align num.succ Num.succ

/-- Addition of two `num`s.
  -/
protected def add : Num → Num → Num
  | 0, a => a
  | b, 0 => b
  | Pos a, Pos b => pos (a + b)
#align num.add Num.add

instance : Add Num :=
  ⟨Num.add⟩

/-- `bit0 n` appends a `0` to the end of `n`, where `bit0 n = n0`.
  -/
protected def bit0 : Num → Num
  | 0 => 0
  | Pos n => pos (PosNum.bit0 n)
#align num.bit0 Num.bit0

/-- `bit1 n` appends a `1` to the end of `n`, where `bit1 n = n1`.
  -/
protected def bit1 : Num → Num
  | 0 => 1
  | Pos n => pos (PosNum.bit1 n)
#align num.bit1 Num.bit1

/-- `bit b n` appends the bit `b` to the end of `n`, where `bit tt x = x1` and `bit ff x = x0`.
  -/
def bit (b : Bool) : Num → Num :=
  cond b Num.bit1 Num.bit0
#align num.bit Num.bit

/-- The number of bits required to represent a `num`, as a `num`. `size 0` is defined to be `0`.
  -/
def size : Num → Num
  | 0 => 0
  | Pos n => pos (PosNum.size n)
#align num.size Num.size

/-- The number of bits required to represent a `num`, as a `nat`. `size 0` is defined to be `0`.
  -/
def natSize : Num → Nat
  | 0 => 0
  | Pos n => PosNum.natSize n
#align num.nat_size Num.natSize

/-- Multiplication of two `num`s.
  -/
protected def mul : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | Pos a, Pos b => pos (a * b)
#align num.mul Num.mul

instance : Mul Num :=
  ⟨Num.mul⟩

open Ordering

/-- Ordering of `num`s.
  -/
def cmp : Num → Num → Ordering
  | 0, 0 => Eq
  | _, 0 => GT.gt
  | 0, _ => lt
  | Pos a, Pos b => PosNum.cmp a b
#align num.cmp Num.cmp

instance : LT Num :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

instance : LE Num :=
  ⟨fun a b => ¬b < a⟩

instance decidableLt : @DecidableRel Num (· < ·)
  | a, b => by dsimp [(· < ·)] <;> infer_instance
#align num.decidable_lt Num.decidableLt

instance decidableLe : @DecidableRel Num (· ≤ ·)
  | a, b => by dsimp [(· ≤ ·)] <;> infer_instance
#align num.decidable_le Num.decidableLe

/-- Converts a `num` to a `znum`.
  -/
def toZnum : Num → Znum
  | 0 => 0
  | Pos a => Znum.pos a
#align num.to_znum Num.toZnum

/-- Converts `x : num` to `-x : znum`.
  -/
def toZnumNeg : Num → Znum
  | 0 => 0
  | Pos a => Znum.neg a
#align num.to_znum_neg Num.toZnumNeg

/-- Converts a `nat` to a `num`.
  -/
def ofNat' : ℕ → Num :=
  Nat.binaryRec 0 fun b n => cond b Num.bit1 Num.bit0
#align num.of_nat' Num.ofNat'

end Num

namespace Znum

open PosNum

/-- The negation of a `znum`.
  -/
def zneg : Znum → Znum
  | 0 => 0
  | Pos a => neg a
  | neg a => pos a
#align znum.zneg Znum.zneg

instance : Neg Znum :=
  ⟨zneg⟩

/-- The absolute value of a `znum` as a `num`.
  -/
def abs : Znum → Num
  | 0 => 0
  | Pos a => Num.pos a
  | neg a => Num.pos a
#align znum.abs Znum.abs

/-- The successor of a `znum`.
  -/
def succ : Znum → Znum
  | 0 => 1
  | Pos a => pos (PosNum.succ a)
  | neg a => (PosNum.pred' a).toZnumNeg
#align znum.succ Znum.succ

/-- The predecessor of a `znum`.
  -/
def pred : Znum → Znum
  | 0 => neg 1
  | Pos a => (PosNum.pred' a).toZnum
  | neg a => neg (PosNum.succ a)
#align znum.pred Znum.pred

/-- `bit0 n` appends a `0` to the end of `n`, where `bit0 n = n0`.
  -/
protected def bit0 : Znum → Znum
  | 0 => 0
  | Pos n => pos (PosNum.bit0 n)
  | neg n => neg (PosNum.bit0 n)
#align znum.bit0 Znum.bit0

/-- `bit1 x` appends a `1` to the end of `x`, mapping `x` to `2 * x + 1`.
  -/
protected def bit1 : Znum → Znum
  | 0 => 1
  | Pos n => pos (PosNum.bit1 n)
  | neg n => neg (Num.casesOn (pred' n) 1 PosNum.bit1)
#align znum.bit1 Znum.bit1

/-- `bitm1 x` appends a `1` to the end of `x`, mapping `x` to `2 * x - 1`.
  -/
protected def bitm1 : Znum → Znum
  | 0 => neg 1
  | Pos n => pos (Num.casesOn (pred' n) 1 PosNum.bit1)
  | neg n => neg (PosNum.bit1 n)
#align znum.bitm1 Znum.bitm1

/-- Converts an `int` to a `znum`.
  -/
def ofInt' : ℤ → Znum
  | (n : ℕ) => Num.toZnum (Num.ofNat' n)
  | -[n+1] => Num.toZnumNeg (Num.ofNat' (n + 1))
#align znum.of_int' Znum.ofInt'

end Znum

namespace PosNum

open Znum

/-- Subtraction of two `pos_num`s, producing a `znum`.
  -/
def sub' : PosNum → PosNum → Znum
  | a, 1 => (pred' a).toZnum
  | 1, b => (pred' b).toZnumNeg
  | bit0 a, bit0 b => (sub' a b).bit0
  | bit0 a, bit1 b => (sub' a b).bitm1
  | bit1 a, bit0 b => (sub' a b).bit1
  | bit1 a, bit1 b => (sub' a b).bit0
#align pos_num.sub' PosNum.sub'

/-- Converts a `znum` to `option pos_num`, where it is `some` if the `znum` was positive and `none`
  otherwise.
  -/
def ofZnum' : Znum → Option PosNum
  | Znum.pos p => some p
  | _ => none
#align pos_num.of_znum' PosNum.ofZnum'

/-- Converts a `znum` to a `pos_num`, mapping all out of range values to `1`.
  -/
def ofZnum : Znum → PosNum
  | Znum.pos p => p
  | _ => 1
#align pos_num.of_znum PosNum.ofZnum

/-- Subtraction of `pos_num`s, where if `a < b`, then `a - b = 1`.
  -/
protected def sub (a b : PosNum) : PosNum :=
  match sub' a b with
  | Znum.pos p => p
  | _ => 1
#align pos_num.sub PosNum.sub

instance : Sub PosNum :=
  ⟨PosNum.sub⟩

end PosNum

namespace Num

/-- The predecessor of a `num` as an `option num`, where `ppred 0 = none`
  -/
def ppred : Num → Option Num
  | 0 => none
  | Pos p => some p.pred'
#align num.ppred Num.ppred

/-- The predecessor of a `num` as a `num`, where `pred 0 = 0`.
  -/
def pred : Num → Num
  | 0 => 0
  | Pos p => p.pred'
#align num.pred Num.pred

/-- Divides a `num` by `2`
  -/
def div2 : Num → Num
  | 0 => 0
  | 1 => 0
  | Pos (PosNum.bit0 p) => pos p
  | Pos (PosNum.bit1 p) => pos p
#align num.div2 Num.div2

/-- Converts a `znum` to an `option num`, where `of_znum' p = none` if `p < 0`.
  -/
def ofZnum' : Znum → Option Num
  | 0 => some 0
  | Znum.pos p => some (pos p)
  | Znum.neg p => none
#align num.of_znum' Num.ofZnum'

/-- Converts a `znum` to an `option num`, where `of_znum p = 0` if `p < 0`.
  -/
def ofZnum : Znum → Num
  | Znum.pos p => pos p
  | _ => 0
#align num.of_znum Num.ofZnum

/-- Subtraction of two `num`s, producing a `znum`.
  -/
def sub' : Num → Num → Znum
  | 0, 0 => 0
  | Pos a, 0 => Znum.pos a
  | 0, Pos b => Znum.neg b
  | Pos a, Pos b => a.sub' b
#align num.sub' Num.sub'

/-- Subtraction of two `num`s, producing an `option num`.
  -/
def psub (a b : Num) : Option Num :=
  ofZnum' (sub' a b)
#align num.psub Num.psub

/-- Subtraction of two `num`s, where if `a < b`, `a - b = 0`.
  -/
protected def sub (a b : Num) : Num :=
  ofZnum (sub' a b)
#align num.sub Num.sub

instance : Sub Num :=
  ⟨Num.sub⟩

end Num

namespace Znum

open PosNum

/-- Addition of `znum`s.
  -/
protected def add : Znum → Znum → Znum
  | 0, a => a
  | b, 0 => b
  | Pos a, Pos b => pos (a + b)
  | Pos a, neg b => sub' a b
  | neg a, Pos b => sub' b a
  | neg a, neg b => neg (a + b)
#align znum.add Znum.add

instance : Add Znum :=
  ⟨Znum.add⟩

/-- Multiplication of `znum`s.
  -/
protected def mul : Znum → Znum → Znum
  | 0, a => 0
  | b, 0 => 0
  | Pos a, Pos b => pos (a * b)
  | Pos a, neg b => neg (a * b)
  | neg a, Pos b => neg (a * b)
  | neg a, neg b => pos (a * b)
#align znum.mul Znum.mul

instance : Mul Znum :=
  ⟨Znum.mul⟩

open Ordering

/-- Ordering on `znum`s.
  -/
def cmp : Znum → Znum → Ordering
  | 0, 0 => Eq
  | Pos a, Pos b => PosNum.cmp a b
  | neg a, neg b => PosNum.cmp b a
  | Pos _, _ => GT.gt
  | neg _, _ => lt
  | _, Pos _ => lt
  | _, neg _ => GT.gt
#align znum.cmp Znum.cmp

instance : LT Znum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

instance : LE Znum :=
  ⟨fun a b => ¬b < a⟩

instance decidableLt : @DecidableRel Znum (· < ·)
  | a, b => by dsimp [(· < ·)] <;> infer_instance
#align znum.decidable_lt Znum.decidableLt

instance decidableLe : @DecidableRel Znum (· ≤ ·)
  | a, b => by dsimp [(· ≤ ·)] <;> infer_instance
#align znum.decidable_le Znum.decidableLe

end Znum

namespace PosNum

/-- Auxiliary definition for `pos_num.divmod`. -/
def divmodAux (d : PosNum) (q r : Num) : Num × Num :=
  match Num.ofZnum' (Num.sub' r (Num.pos d)) with
  | some r' => (Num.bit1 q, r')
  | none => (Num.bit0 q, r)
#align pos_num.divmod_aux PosNum.divmodAux

/-- `divmod x y = (y / x, y % x)`.
  -/
def divmod (d : PosNum) : PosNum → Num × Num
  | bit0 n =>
    let (q, r₁) := divmod n
    divmodAux d q (Num.bit0 r₁)
  | bit1 n =>
    let (q, r₁) := divmod n
    divmodAux d q (Num.bit1 r₁)
  | 1 => divmodAux d 0 1
#align pos_num.divmod PosNum.divmod

/-- Division of `pos_num`,
  -/
def div' (n d : PosNum) : Num :=
  (divmod d n).1
#align pos_num.div' PosNum.div'

/-- Modulus of `pos_num`s.
  -/
def mod' (n d : PosNum) : Num :=
  (divmod d n).2
#align pos_num.mod' PosNum.mod'

/-
  private def sqrt_aux1 (b : pos_num) (r n : num) : num × num :=
  match num.of_znum' (n.sub' (r + num.pos b)) with
  | some n' := (r.div2 + num.pos b, n')
  | none := (r.div2, n)
  end

  private def sqrt_aux : pos_num → num → num → num
  | b@(bit0 b') r n := let (r', n') := sqrt_aux1 b r n in sqrt_aux b' r' n'
  | b@(bit1 b') r n := let (r', n') := sqrt_aux1 b r n in sqrt_aux b' r' n'
  | 1           r n := (sqrt_aux1 1 r n).1
  -/
/-

def sqrt_aux : ℕ → ℕ → ℕ → ℕ
| b r n := if b0 : b = 0 then r else
  let b' := shiftr b 2 in
  have b' < b, from sqrt_aux_dec b0,
  match (n - (r + b : ℕ) : ℤ) with
  | (n' : ℕ) := sqrt_aux b' (div2 r + b) n'
  | _ := sqrt_aux b' (div2 r) n
  end

/-- `sqrt n` is the square root of a natural number `n`. If `n` is not a
  perfect square, it returns the largest `k:ℕ` such that `k*k ≤ n`. -/
def sqrt (n : ℕ) : ℕ :=
match size n with
| 0      := 0
| succ s := sqrt_aux (shiftl 1 (bit0 (div2 s))) 0 n
end
-/
end PosNum

namespace Num

/-- Division of `num`s, where `x / 0 = 0`.
  -/
def div : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | Pos n, Pos d => PosNum.div' n d
#align num.div Num.div

/-- Modulus of `num`s.
  -/
def mod : Num → Num → Num
  | 0, _ => 0
  | n, 0 => n
  | Pos n, Pos d => PosNum.mod' n d
#align num.mod Num.mod

instance : Div Num :=
  ⟨Num.div⟩

instance : Mod Num :=
  ⟨Num.mod⟩

/-- Auxiliary definition for `num.gcd`. -/
def gcdAux : Nat → Num → Num → Num
  | 0, a, b => b
  | Nat.succ n, 0, b => b
  | Nat.succ n, a, b => gcd_aux n (b % a) a
#align num.gcd_aux Num.gcdAux

/-- Greatest Common Divisor (GCD) of two `num`s.
  -/
def gcd (a b : Num) : Num :=
  if a ≤ b then gcdAux (a.natSize + b.natSize) a b else gcdAux (b.natSize + a.natSize) b a
#align num.gcd Num.gcd

end Num

namespace Znum

/-- Division of `znum`, where `x / 0 = 0`.
  -/
def div : Znum → Znum → Znum
  | 0, _ => 0
  | _, 0 => 0
  | Pos n, Pos d => Num.toZnum (PosNum.div' n d)
  | Pos n, neg d => Num.toZnumNeg (PosNum.div' n d)
  | neg n, Pos d => neg (PosNum.pred' n / Num.pos d).succ'
  | neg n, neg d => pos (PosNum.pred' n / Num.pos d).succ'
#align znum.div Znum.div

/-- Modulus of `znum`s.
  -/
def mod : Znum → Znum → Znum
  | 0, d => 0
  | Pos n, d => Num.toZnum (Num.pos n % d.abs)
  | neg n, d => d.abs.sub' (PosNum.pred' n % d.abs).succ
#align znum.mod Znum.mod

instance : Div Znum :=
  ⟨Znum.div⟩

instance : Mod Znum :=
  ⟨Znum.mod⟩

/-- Greatest Common Divisor (GCD) of two `znum`s.
  -/
def gcd (a b : Znum) : Num :=
  a.abs.gcd b.abs
#align znum.gcd Znum.gcd

end Znum

section

variable {α : Type _} [Zero α] [One α] [Add α] [Neg α]

/-- `cast_znum` casts a `znum` into any type which has `0`, `1`, `+` and `neg`
  -/
def castZnum : Znum → α
  | 0 => 0
  | Znum.pos p => p
  | Znum.neg p => -p
#align cast_znum castZnum

-- see Note [coercion into rings]
instance (priority := 900) znumCoe : CoeTC Znum α :=
  ⟨castZnum⟩
#align znum_coe znumCoe

instance : Repr Znum :=
  ⟨fun n => repr (n : ℤ)⟩

end


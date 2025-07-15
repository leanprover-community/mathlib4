/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Lean.Linter.Deprecated
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Tactic.TypeStar

/-!
# Binary representation of integers using inductive types

Note: Unlike in Coq, where this representation is preferred because of
the reliance on kernel reduction, in Lean this representation is discouraged
in favor of the "Peano" natural numbers `Nat`, and the purpose of this
collection of theorems is to show the equivalence of the different approaches.
-/

/-- The type of positive binary numbers.

     13 = 1101(base 2) = bit1 (bit0 (bit1 one)) -/
inductive PosNum : Type
  | one : PosNum
  | bit1 : PosNum → PosNum
  | bit0 : PosNum → PosNum
  deriving DecidableEq

instance : One PosNum :=
  ⟨PosNum.one⟩

instance : Inhabited PosNum :=
  ⟨1⟩

/-- The type of nonnegative binary numbers, using `PosNum`.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one))) -/
inductive Num : Type
  | zero : Num
  | pos : PosNum → Num
  deriving DecidableEq

instance : Zero Num :=
  ⟨Num.zero⟩

instance : One Num :=
  ⟨Num.pos 1⟩

instance : Inhabited Num :=
  ⟨0⟩

/-- Representation of integers using trichotomy around zero.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one)))
     -13 = -1101(base 2) = neg (bit1 (bit0 (bit1 one))) -/
inductive ZNum : Type
  | zero : ZNum
  | pos : PosNum → ZNum
  | neg : PosNum → ZNum
  deriving DecidableEq

instance : Zero ZNum :=
  ⟨ZNum.zero⟩

instance : One ZNum :=
  ⟨ZNum.pos 1⟩

instance : Inhabited ZNum :=
  ⟨0⟩

namespace PosNum

/-- `bit b n` appends the bit `b` to the end of `n`, where `bit tt x = x1` and `bit ff x = x0`. -/
def bit (b : Bool) : PosNum → PosNum :=
  cond b bit1 bit0

/-- The successor of a `PosNum`. -/
def succ : PosNum → PosNum
  | 1 => bit0 one
  | bit1 n => bit0 (succ n)
  | bit0 n => bit1 n

/-- Returns a boolean for whether the `PosNum` is `one`. -/
def isOne : PosNum → Bool
  | 1 => true
  | _ => false

/-- Addition of two `PosNum`s. -/
protected def add : PosNum → PosNum → PosNum
  | 1, b => succ b
  | a, 1 => succ a
  | bit0 a, bit0 b => bit0 (PosNum.add a b)
  | bit1 a, bit1 b => bit0 (succ (PosNum.add a b))
  | bit0 a, bit1 b => bit1 (PosNum.add a b)
  | bit1 a, bit0 b => bit1 (PosNum.add a b)

instance : Add PosNum :=
  ⟨PosNum.add⟩

/-- The predecessor of a `PosNum` as a `Num`. -/
def pred' : PosNum → Num
  | 1 => 0
  | bit0 n => Num.pos (Num.casesOn (pred' n) 1 bit1)
  | bit1 n => Num.pos (bit0 n)

/-- The predecessor of a `PosNum` as a `PosNum`. This means that `pred 1 = 1`. -/
def pred (a : PosNum) : PosNum :=
  Num.casesOn (pred' a) 1 id

/-- The number of bits of a `PosNum`, as a `PosNum`. -/
def size : PosNum → PosNum
  | 1 => 1
  | bit0 n => succ (size n)
  | bit1 n => succ (size n)

/-- The number of bits of a `PosNum`, as a `Nat`. -/
def natSize : PosNum → Nat
  | 1 => 1
  | bit0 n => Nat.succ (natSize n)
  | bit1 n => Nat.succ (natSize n)

/-- Multiplication of two `PosNum`s. -/
protected def mul (a : PosNum) : PosNum → PosNum
  | 1 => a
  | bit0 b => bit0 (PosNum.mul a b)
  | bit1 b => bit0 (PosNum.mul a b) + a

instance : Mul PosNum :=
  ⟨PosNum.mul⟩

/-- `ofNatSucc n` is the `PosNum` corresponding to `n + 1`. -/
def ofNatSucc : ℕ → PosNum
  | 0 => 1
  | Nat.succ n => succ (ofNatSucc n)

/-- `ofNat n` is the `PosNum` corresponding to `n`, except for `ofNat 0 = 1`. -/
def ofNat (n : ℕ) : PosNum :=
  ofNatSucc (Nat.pred n)

instance (priority := low) {n : ℕ} : OfNat PosNum (n + 1) where
  ofNat := ofNat (n + 1)

open Ordering

/-- Ordering of `PosNum`s. -/
def cmp : PosNum → PosNum → Ordering
  | 1, 1 => eq
  | _, 1 => gt
  | 1, _ => lt
  | bit0 a, bit0 b => cmp a b
  | bit0 a, bit1 b => Ordering.casesOn (cmp a b) lt lt gt
  | bit1 a, bit0 b => Ordering.casesOn (cmp a b) lt gt gt
  | bit1 a, bit1 b => cmp a b

instance : LT PosNum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

instance : LE PosNum :=
  ⟨fun a b => ¬b < a⟩

instance decidableLT : DecidableLT PosNum
  | a, b => by dsimp [LT.lt]; infer_instance

instance decidableLE : DecidableLE PosNum
  | a, b => by dsimp [LE.le]; infer_instance

end PosNum

section

variable {α : Type*} [One α] [Add α]

/-- `castPosNum` casts a `PosNum` into any type which has `1` and `+`. -/
@[coe]
def castPosNum : PosNum → α
  | 1 => 1
  | PosNum.bit0 a => castPosNum a + castPosNum a
  | PosNum.bit1 a => castPosNum a + castPosNum a + 1

/-- `castNum` casts a `Num` into any type which has `0`, `1` and `+`. -/
@[coe]
def castNum [Zero α] : Num → α
  | 0 => 0
  | Num.pos p => castPosNum p

-- see Note [coercion into rings]
instance (priority := 900) posNumCoe : CoeHTCT PosNum α :=
  ⟨castPosNum⟩

-- see Note [coercion into rings]
instance (priority := 900) numNatCoe [Zero α] : CoeHTCT Num α :=
  ⟨castNum⟩

instance : Repr PosNum :=
  ⟨fun n _ => repr (n : ℕ)⟩

instance : Repr Num :=
  ⟨fun n _ => repr (n : ℕ)⟩

end

namespace Num

open PosNum

/-- The successor of a `Num` as a `PosNum`. -/
def succ' : Num → PosNum
  | 0 => 1
  | pos p => succ p

/-- The successor of a `Num` as a `Num`. -/
def succ (n : Num) : Num :=
  pos (succ' n)

/-- Addition of two `Num`s. -/
protected def add : Num → Num → Num
  | 0, a => a
  | b, 0 => b
  | pos a, pos b => pos (a + b)

instance : Add Num :=
  ⟨Num.add⟩

/-- `bit0 n` appends a `0` to the end of `n`, where `bit0 n = n0`. -/
protected def bit0 : Num → Num
  | 0 => 0
  | pos n => pos (PosNum.bit0 n)

/-- `bit1 n` appends a `1` to the end of `n`, where `bit1 n = n1`. -/
protected def bit1 : Num → Num
  | 0 => 1
  | pos n => pos (PosNum.bit1 n)

/-- `bit b n` appends the bit `b` to the end of `n`, where `bit tt x = x1` and `bit ff x = x0`. -/
def bit (b : Bool) : Num → Num :=
  cond b Num.bit1 Num.bit0

/-- The number of bits required to represent a `Num`, as a `Num`. `size 0` is defined to be `0`. -/
def size : Num → Num
  | 0 => 0
  | pos n => pos (PosNum.size n)

/-- The number of bits required to represent a `Num`, as a `Nat`. `size 0` is defined to be `0`. -/
def natSize : Num → Nat
  | 0 => 0
  | pos n => PosNum.natSize n

/-- Multiplication of two `Num`s. -/
protected def mul : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | pos a, pos b => pos (a * b)

instance : Mul Num :=
  ⟨Num.mul⟩

open Ordering

/-- Ordering of `Num`s. -/
def cmp : Num → Num → Ordering
  | 0, 0 => eq
  | _, 0 => gt
  | 0, _ => lt
  | pos a, pos b => PosNum.cmp a b

instance : LT Num :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

instance : LE Num :=
  ⟨fun a b => ¬b < a⟩

instance decidableLT : DecidableLT Num
  | a, b => by dsimp [LT.lt]; infer_instance

instance decidableLE : DecidableLE Num
  | a, b => by dsimp [LE.le]; infer_instance

/-- Converts a `Num` to a `ZNum`. -/
def toZNum : Num → ZNum
  | 0 => 0
  | pos a => ZNum.pos a

/-- Converts `x : Num` to `-x : ZNum`. -/
def toZNumNeg : Num → ZNum
  | 0 => 0
  | pos a => ZNum.neg a

/-- Converts a `Nat` to a `Num`. -/
def ofNat' : ℕ → Num :=
  Nat.binaryRec 0 (fun b _ => cond b Num.bit1 Num.bit0)

end Num

namespace ZNum

open PosNum

/-- The negation of a `ZNum`. -/
def zNeg : ZNum → ZNum
  | 0 => 0
  | pos a => neg a
  | neg a => pos a

instance : Neg ZNum :=
  ⟨zNeg⟩

/-- The absolute value of a `ZNum` as a `Num`. -/
def abs : ZNum → Num
  | 0 => 0
  | pos a => Num.pos a
  | neg a => Num.pos a

/-- The successor of a `ZNum`. -/
def succ : ZNum → ZNum
  | 0 => 1
  | pos a => pos (PosNum.succ a)
  | neg a => (PosNum.pred' a).toZNumNeg

/-- The predecessor of a `ZNum`. -/
def pred : ZNum → ZNum
  | 0 => neg 1
  | pos a => (PosNum.pred' a).toZNum
  | neg a => neg (PosNum.succ a)

/-- `bit0 n` appends a `0` to the end of `n`, where `bit0 n = n0`. -/
protected def bit0 : ZNum → ZNum
  | 0 => 0
  | pos n => pos (PosNum.bit0 n)
  | neg n => neg (PosNum.bit0 n)

/-- `bit1 x` appends a `1` to the end of `x`, mapping `x` to `2 * x + 1`. -/
protected def bit1 : ZNum → ZNum
  | 0 => 1
  | pos n => pos (PosNum.bit1 n)
  | neg n => neg (Num.casesOn (pred' n) 1 PosNum.bit1)

/-- `bitm1 x` appends a `1` to the end of `x`, mapping `x` to `2 * x - 1`. -/
protected def bitm1 : ZNum → ZNum
  | 0 => neg 1
  | pos n => pos (Num.casesOn (pred' n) 1 PosNum.bit1)
  | neg n => neg (PosNum.bit1 n)

/-- Converts an `Int` to a `ZNum`. -/
def ofInt' : ℤ → ZNum
  | Int.ofNat n => Num.toZNum (Num.ofNat' n)
  | Int.negSucc n => Num.toZNumNeg (Num.ofNat' (n + 1))

end ZNum

namespace PosNum

open ZNum

/-- Subtraction of two `PosNum`s, producing a `ZNum`. -/
def sub' : PosNum → PosNum → ZNum
  | a, 1 => (pred' a).toZNum
  | 1, b => (pred' b).toZNumNeg
  | bit0 a, bit0 b => (sub' a b).bit0
  | bit0 a, bit1 b => (sub' a b).bitm1
  | bit1 a, bit0 b => (sub' a b).bit1
  | bit1 a, bit1 b => (sub' a b).bit0

/-- Converts a `ZNum` to `Option PosNum`, where it is `some` if the `ZNum` was positive and `none`
  otherwise. -/
def ofZNum' : ZNum → Option PosNum
  | ZNum.pos p => some p
  | _ => none

/-- Converts a `ZNum` to a `PosNum`, mapping all out of range values to `1`. -/
def ofZNum : ZNum → PosNum
  | ZNum.pos p => p
  | _ => 1

/-- Subtraction of `PosNum`s, where if `a < b`, then `a - b = 1`. -/
protected def sub (a b : PosNum) : PosNum :=
  match sub' a b with
  | ZNum.pos p => p
  | _ => 1

instance : Sub PosNum :=
  ⟨PosNum.sub⟩

end PosNum

namespace Num

/-- The predecessor of a `Num` as an `Option Num`, where `ppred 0 = none` -/
def ppred : Num → Option Num
  | 0 => none
  | pos p => some p.pred'

/-- The predecessor of a `Num` as a `Num`, where `pred 0 = 0`. -/
def pred : Num → Num
  | 0 => 0
  | pos p => p.pred'

/-- Divides a `Num` by `2` -/
def div2 : Num → Num
  | 0 => 0
  | 1 => 0
  | pos (PosNum.bit0 p) => pos p
  | pos (PosNum.bit1 p) => pos p

/-- Converts a `ZNum` to an `Option Num`, where `ofZNum' p = none` if `p < 0`. -/
def ofZNum' : ZNum → Option Num
  | 0 => some 0
  | ZNum.pos p => some (pos p)
  | ZNum.neg _ => none

/-- Converts a `ZNum` to an `Option Num`, where `ofZNum p = 0` if `p < 0`. -/
def ofZNum : ZNum → Num
  | ZNum.pos p => pos p
  | _ => 0

/-- Subtraction of two `Num`s, producing a `ZNum`. -/
def sub' : Num → Num → ZNum
  | 0, 0 => 0
  | pos a, 0 => ZNum.pos a
  | 0, pos b => ZNum.neg b
  | pos a, pos b => a.sub' b

/-- Subtraction of two `Num`s, producing an `Option Num`. -/
def psub (a b : Num) : Option Num :=
  ofZNum' (sub' a b)

/-- Subtraction of two `Num`s, where if `a < b`, `a - b = 0`. -/
protected def sub (a b : Num) : Num :=
  ofZNum (sub' a b)

instance : Sub Num :=
  ⟨Num.sub⟩

end Num

namespace ZNum

open PosNum

/-- Addition of `ZNum`s. -/
protected def add : ZNum → ZNum → ZNum
  | 0, a => a
  | b, 0 => b
  | pos a, pos b => pos (a + b)
  | pos a, neg b => sub' a b
  | neg a, pos b => sub' b a
  | neg a, neg b => neg (a + b)

instance : Add ZNum :=
  ⟨ZNum.add⟩

/-- Multiplication of `ZNum`s. -/
protected def mul : ZNum → ZNum → ZNum
  | 0, _ => 0
  | _, 0 => 0
  | pos a, pos b => pos (a * b)
  | pos a, neg b => neg (a * b)
  | neg a, pos b => neg (a * b)
  | neg a, neg b => pos (a * b)

instance : Mul ZNum :=
  ⟨ZNum.mul⟩

open Ordering

/-- Ordering on `ZNum`s. -/
def cmp : ZNum → ZNum → Ordering
  | 0, 0 => eq
  | pos a, pos b => PosNum.cmp a b
  | neg a, neg b => PosNum.cmp b a
  | pos _, _ => gt
  | neg _, _ => lt
  | _, pos _ => lt
  | _, neg _ => gt

instance : LT ZNum :=
  ⟨fun a b => cmp a b = Ordering.lt⟩

instance : LE ZNum :=
  ⟨fun a b => ¬b < a⟩

instance decidableLT : DecidableLT ZNum
  | a, b => by dsimp [LT.lt]; infer_instance

instance decidableLE : DecidableLE ZNum
  | a, b => by dsimp [LE.le]; infer_instance

end ZNum

namespace PosNum

/-- Auxiliary definition for `PosNum.divMod`. -/
def divModAux (d : PosNum) (q r : Num) : Num × Num :=
  match Num.ofZNum' (Num.sub' r (Num.pos d)) with
  | some r' => (Num.bit1 q, r')
  | none => (Num.bit0 q, r)

/-- `divMod x y = (y / x, y % x)`. -/
def divMod (d : PosNum) : PosNum → Num × Num
  | bit0 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit0 r₁)
  | bit1 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit1 r₁)
  | 1 => divModAux d 0 1

/-- Division of `PosNum` -/
def div' (n d : PosNum) : Num :=
  (divMod d n).1

/-- Modulus of `PosNum`s. -/
def mod' (n d : PosNum) : Num :=
  (divMod d n).2

/-- Auxiliary definition for `sqrtAux`. -/
private def sqrtAux1 (b : PosNum) (r n : Num) : Num × Num :=
  match Num.ofZNum' (n.sub' (r + Num.pos b)) with
  | some n' => (r.div2 + Num.pos b, n')
  | none => (r.div2, n)

/-- Auxiliary definition for a `sqrt` function which is not currently implemented. -/
private def sqrtAux : PosNum → Num → Num → Num
  | b@(bit0 b') => fun r n => let (r', n') := sqrtAux1 b r n; sqrtAux b' r' n'
  | b@(bit1 b') => fun r n => let (r', n') := sqrtAux1 b r n; sqrtAux b' r' n'
  | 1 => fun r n => (sqrtAux1 1 r n).1

end PosNum

namespace Num

/-- Division of `Num`s, where `x / 0 = 0`. -/
def div : Num → Num → Num
  | 0, _ => 0
  | _, 0 => 0
  | pos n, pos d => PosNum.div' n d

/-- Modulus of `Num`s. -/
def mod : Num → Num → Num
  | 0, _ => 0
  | n, 0 => n
  | pos n, pos d => PosNum.mod' n d

instance : Div Num :=
  ⟨Num.div⟩

instance : Mod Num :=
  ⟨Num.mod⟩

/-- Auxiliary definition for `Num.gcd`. -/
def gcdAux : Nat → Num → Num → Num
  | 0, _, b => b
  | Nat.succ _, 0, b => b
  | Nat.succ n, a, b => gcdAux n (b % a) a

/-- Greatest Common Divisor (GCD) of two `Num`s. -/
def gcd (a b : Num) : Num :=
  if a ≤ b then gcdAux (a.natSize + b.natSize) a b else gcdAux (b.natSize + a.natSize) b a

end Num

namespace ZNum

/-- Division of `ZNum`, where `x / 0 = 0`. -/
def div : ZNum → ZNum → ZNum
  | 0, _ => 0
  | _, 0 => 0
  | pos n, pos d => Num.toZNum (PosNum.div' n d)
  | pos n, neg d => Num.toZNumNeg (PosNum.div' n d)
  | neg n, pos d => neg (PosNum.pred' n / Num.pos d).succ'
  | neg n, neg d => pos (PosNum.pred' n / Num.pos d).succ'

/-- Modulus of `ZNum`s. -/
def mod : ZNum → ZNum → ZNum
  | 0, _ => 0
  | pos n, d => Num.toZNum (Num.pos n % d.abs)
  | neg n, d => d.abs.sub' (PosNum.pred' n % d.abs).succ

instance : Div ZNum :=
  ⟨ZNum.div⟩

instance : Mod ZNum :=
  ⟨ZNum.mod⟩

/-- Greatest Common Divisor (GCD) of two `ZNum`s. -/
def gcd (a b : ZNum) : Num :=
  a.abs.gcd b.abs

end ZNum

section
variable {α : Type*} [Zero α] [One α] [Add α] [Neg α]

/-- `castZNum` casts a `ZNum` into any type which has `0`, `1`, `+` and `neg` -/
@[coe]
def castZNum : ZNum → α
  | 0 => 0
  | ZNum.pos p => p
  | ZNum.neg p => -p

-- see Note [coercion into rings]
instance (priority := 900) znumCoe : CoeHTCT ZNum α :=
  ⟨castZNum⟩

instance : Repr ZNum :=
  ⟨fun n _ => repr (n : ℤ)⟩

end

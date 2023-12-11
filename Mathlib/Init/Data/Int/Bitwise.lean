/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Mathlib.Init.Data.Int.Basic
import Mathlib.Init.Data.Nat.Bitwise

#align_import init.data.int.bitwise from "leanprover-community/lean"@"855e5b74e3a52a40552e8f067169d747d48743fd"

/-!
# Lemmas about bitwise operations on integers.

Possibly only of archaeological significance.
-/

universe u

namespace Int

/-- `div2 n = n/2`-/
def div2 : ℤ → ℤ
  | (n : ℕ) => n.div2
  | -[n +1] => negSucc n.div2
#align int.div2 Int.div2

/-- `bodd n` returns `true` if `n` is odd-/
def bodd : ℤ → Bool
  | (n : ℕ) => n.bodd
  | -[n +1] => not (n.bodd)
#align int.bodd Int.bodd

-- Porting note: `bit0, bit1` deprecated, do we need to adapt `bit`?
set_option linter.deprecated false in
/-- `bit b` appends the digit `b` to the binary representation of
  its integer input. -/
def bit (b : Bool) : ℤ → ℤ :=
  cond b bit1 bit0
#align int.bit Int.bit

/-- `testBit m n` returns whether the `(n+1)ˢᵗ` least significant bit is `1` or `0`-/
def testBit : ℤ → ℕ → Bool
  | (m : ℕ), n => Nat.testBit m n
  | -[m +1], n => !(Nat.testBit m n)
#align int.test_bit Int.testBit

/-- `Int.natBitwise` is an auxiliary definition for `Int.bitwise`. -/
def natBitwise (f : Bool → Bool → Bool) (m n : ℕ) : ℤ :=
  cond (f false false) -[ Nat.bitwise (fun x y => not (f x y)) m n +1] (Nat.bitwise f m n)
#align int.nat_bitwise Int.natBitwise

/-- `Int.bitwise` applies the function `f` to pairs of bits in the same position in
  the binary representations of its inputs. -/
def bitwise (f : Bool → Bool → Bool) : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => natBitwise f m n
  | (m : ℕ), -[n +1] => natBitwise (fun x y => f x (not y)) m n
  | -[m +1], (n : ℕ) => natBitwise (fun x y => f (not x) y) m n
  | -[m +1], -[n +1] => natBitwise (fun x y => f (not x) (not y)) m n
#align int.bitwise Int.bitwise

/-- `lnot` flips all the bits in the binary representation of its input -/
def lnot : ℤ → ℤ
  | (m : ℕ) => -[m +1]
  | -[m +1] => m
#align int.lnot Int.lnot

/--`lor` takes two integers and returns their bitwise `or`-/
def lor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => m ||| n
  | (m : ℕ), -[n +1] => -[Nat.ldiff n m +1]
  | -[m +1], (n : ℕ) => -[Nat.ldiff m n +1]
  | -[m +1], -[n +1] => -[m &&& n +1]
#align int.lor Int.lor

/--`land` takes two integers and returns their bitwise `and`-/
def land : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => m &&& n
  | (m : ℕ), -[n +1] => Nat.ldiff m n
  | -[m +1], (n : ℕ) => Nat.ldiff n m
  | -[m +1], -[n +1] => -[m ||| n +1]
#align int.land Int.land

-- Porting note: I don't know why `Nat.ldiff` got the prime, but I'm matching this change here
/--`ldiff a b` performs bitwise set difference. For each corresponding
  pair of bits taken as booleans, say `aᵢ` and `bᵢ`, it applies the
  boolean operation `aᵢ ∧ bᵢ` to obtain the `iᵗʰ` bit of the result.-/
def ldiff : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.ldiff m n
  | (m : ℕ), -[n +1] => m &&& n
  | -[m +1], (n : ℕ) => -[m ||| n +1]
  | -[m +1], -[n +1] => Nat.ldiff n m
#align int.ldiff Int.ldiff

-- Porting note: I don't know why `Nat.xor'` got the prime, but I'm matching this change here
/--`xor` computes the bitwise `xor` of two natural numbers-/
protected def xor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => (m ^^^ n)
  | (m : ℕ), -[n +1] => -[(m ^^^ n) +1]
  | -[m +1], (n : ℕ) => -[(m ^^^ n) +1]
  | -[m +1], -[n +1] => (m ^^^ n)
#align int.lxor Int.xor

/-- `m <<< n` produces an integer whose binary representation
  is obtained by left-shifting the binary representation of `m` by `n` places -/
instance : ShiftLeft ℤ where
  shiftLeft
  | (m : ℕ), (n : ℕ) => Nat.shiftLeft' false m n
  | (m : ℕ), -[n +1] => m >>> (Nat.succ n)
  | -[m +1], (n : ℕ) => -[Nat.shiftLeft' true m n +1]
  | -[m +1], -[n +1] => -[m >>> (Nat.succ n) +1]
#align int.shiftl ShiftLeft.shiftLeft

/-- `m >>> n` produces an integer whose binary representation
  is obtained by right-shifting the binary representation of `m` by `n` places -/
instance : ShiftRight ℤ where
  shiftRight m n := m <<< (-n)
#align int.shiftr ShiftRight.shiftRight

end Int

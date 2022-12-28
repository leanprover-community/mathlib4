/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! Corresponding mathlib SHA: 6c48d300da03eaa8e374eb31933001090917202f
-/

prelude
import Mathlib.Init.Data.Int.Basic
import Mathlib.Init.Data.Nat.Bitwise

universe u

namespace Int

  def div2 : ℤ → ℤ
  | (n : ℕ) => n.div2
  | -[n +1] => negSucc n.div2
  #align int.div2 Int.div2

  def bodd : ℤ → Bool
  | (n : ℕ) => n.bodd
  | -[n +1] => not (n.bodd)
  #align int.bodd Int.bodd

  -- Porting note: `bit0, bit1` deprecated, do we need to adapt `bit`?
  set_option linter.deprecated false in
  def bit (b : Bool) : ℤ → ℤ :=
    cond b bit1 bit0
  #align int.bit Int.bit

  def testBit : ℤ → ℕ → Bool
  | (m : ℕ), n => Nat.testBit m n
  | -[m +1], n => !(Nat.testBit m n)
  #align int.test_bit Int.testBit

  def natBitwise (f : Bool → Bool → Bool) (m n : ℕ) : ℤ :=
    cond (f false false) -[ Nat.bitwise' (fun x y => not (f x y)) m n +1] (Nat.bitwise' f m n)
  #align int.nat_bitwise Int.natBitwise

  def bitwise (f : Bool → Bool → Bool) : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => natBitwise f m n
  | (m : ℕ), -[n +1] => natBitwise (fun x y => f x (not y)) m n
  | -[m +1], (n : ℕ) => natBitwise (fun x y => f (not x) y) m n
  | -[m +1], -[n +1] => natBitwise (fun x y => f (not x) (not y)) m n
  #align int.bitwise Int.bitwise

  def lnot : ℤ → ℤ
  | (m : ℕ) => -[m +1]
  | -[m +1] => m
  #align int.lnot Int.lnot

  def lor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.lor' m n
  | (m : ℕ), -[n +1] => -[Nat.ldiff' n m +1]
  | -[m +1], (n : ℕ) => -[Nat.ldiff' m n +1]
  | -[m +1], -[n +1] => -[Nat.land' m n +1]
  #align int.lor Int.lor

  def land : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.land' m n
  | (m : ℕ), -[n +1] => Nat.ldiff' m n
  | -[m +1], (n : ℕ) => Nat.ldiff' n m
  | -[m +1], -[n +1] => -[Nat.lor' m n +1]
  #align int.land Int.land

  -- Porting note: I don't know why `Nat.ldiff'` got the prime, but I'm matching this change here
  def ldiff' : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.ldiff' m n
  | (m : ℕ), -[n +1] => Nat.land' m n
  | -[m +1], (n : ℕ) => -[Nat.lor' m n +1]
  | -[m +1], -[n +1] => Nat.ldiff' n m
  #align int.ldiff Int.ldiff'

  -- Porting note: I don't know why `Nat.xor'` got the prime, but I'm matching this change here
  def lxor' : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.lxor' m n
  | (m : ℕ), -[n +1] => -[Nat.lxor' m n +1]
  | -[m +1], (n : ℕ) => -[Nat.lxor' m n +1]
  | -[m +1], -[n +1] => Nat.lxor' m n
  #align int.lxor Int.lxor'

  def shiftl : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.shiftl' false m n
  | (m : ℕ), -[n +1] => Nat.shiftr m (Nat.succ n)
  | -[m +1], (n : ℕ) => -[Nat.shiftl' true m n +1]
  | -[m +1], -[n +1] => -[Nat.shiftr m (Nat.succ n) +1]
  #align int.shiftl Int.shiftl

  def shiftr (m n : ℤ) : ℤ :=
    shiftl m (-n)
  #align int.shiftr Int.shiftr

end Int

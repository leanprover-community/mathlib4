/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init.Data.Nat.Lemmas
import Init.WFTactics
import Mathlib.Data.Bool.Basic
import Mathlib.Init.ZeroOne
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Says
import Mathlib.Tactic.GeneralizeProofs

#align_import init.data.nat.bitwise from "leanprover-community/lean"@"53e8520d8964c7632989880372d91ba0cecbaf00"

/-!
# Lemmas about bitwise operations on natural numbers.

Possibly only of archaeological significance.
-/

set_option autoImplicit true

universe u

-- Once we're in the `Nat` namespace, `xor` will inconveniently resolve to `Nat.xor`.
/-- `bxor` denotes the `xor` function i.e. the exclusive-or function on type `Bool`. -/
local notation "bxor" => _root_.xor

namespace Nat
set_option linter.deprecated false

#align nat.div2 Nat.div2
#align nat.bodd Nat.bodd
#align nat.bodd_zero Nat.bodd_zero
#align nat.bodd_one Nat.bodd_one
#align nat.bodd_two Nat.bodd_two
#align nat.bodd_succ Nat.bodd_succ
#align nat.bodd_add Nat.bodd_add
#align nat.bodd_mul Nat.bodd_mul
#align nat.mod_two_of_bodd Nat.mod_two_of_bodd
#align nat.div2_zero Nat.div2_zero
#align nat.div2_one Nat.div2_one
#align nat.div2_two Nat.div2_two
#align nat.div2_succ Nat.div2_succ

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

#align nat.bodd_add_div2 Nat.div2_add_boddₓ
#align nat.div2_val Nat.div2_val
#align nat.bit Nat.bit

theorem bit0_val (n : Nat) : bit0 n = 2 * n :=
  calc
    n + n = 0 + n + n := by rw [Nat.zero_add]
    _ = n * 2 := rfl
    _ = 2 * n := Nat.mul_comm _ _
#align nat.bit0_val Nat.bit0_val

theorem bit1_val (n : Nat) : bit1 n = 2 * n + 1 :=
  congr_arg succ (bit0_val _)
#align nat.bit1_val Nat.bit1_val

#align nat.bit_val Nat.bit_val
#align nat.bit_decomp Nat.bit_decomp
#align nat.bit_cases_on Nat.bitCasesOn

theorem bit_zero : bit false 0 = 0 :=
  rfl
#align nat.bit_zero Nat.bit_zero

/--`shiftLeft' b m n` performs a left shift of `m` `n` times
 and adds the bit `b` as the least significant bit each time.
 Returns the corresponding natural number-/
def shiftLeft' (b : Bool) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => bit b (shiftLeft' b m n)
#align nat.shiftl' Nat.shiftLeft'

@[simp]
theorem shiftLeft'_false : ∀ n, shiftLeft' false m n = m <<< n
  | 0 => rfl
  | n + 1 => by
    have : 2 * (m * 2^n) = 2^(n+1)*m := by
      rw [Nat.mul_comm, Nat.mul_assoc, ← pow_succ]; simp
    simp [shiftLeft_eq, shiftLeft', bit_val, shiftLeft'_false, this]

/-- Std4 takes the unprimed name for `Nat.shiftLeft_eq m n : m <<< n = m * 2 ^ n`. -/
@[simp]
lemma shiftLeft_eq' (m n : Nat) : shiftLeft m n = m <<< n := rfl

@[simp]
lemma shiftRight_eq (m n : Nat) : shiftRight m n = m >>> n := rfl

#align nat.test_bit Nat.testBit
#align nat.binary_rec Nat.binaryRec

/-- `size n` : Returns the size of a natural number in
bits i.e. the length of its binary representation -/
def size : ℕ → ℕ :=
  binaryRec 0 fun _ _ => succ
#align nat.size Nat.size

/-- `bits n` returns a list of Bools which correspond to the binary representation of n, where
    the head of the list represents the least significant bit -/
def bits : ℕ → List Bool :=
  binaryRec [] fun b _ IH => b :: IH
#align nat.bits Nat.bits

#align nat.bitwise Nat.bitwise

#align nat.lor Nat.lor
#align nat.land Nat.land
#align nat.lxor Nat.xor

/--`ldiff a b` performs bitwise set difference. For each corresponding
  pair of bits taken as booleans, say `aᵢ` and `bᵢ`, it applies the
  boolean operation `aᵢ ∧ ¬bᵢ` to obtain the `iᵗʰ` bit of the result.-/
def ldiff : ℕ → ℕ → ℕ :=
  bitwise fun a b => a && not b
#align nat.ldiff Nat.ldiff

#align nat.binary_rec_zero Nat.binaryRec_zero

/-! bitwise ops -/

#align nat.bodd_bit Nat.bodd_bit
#align nat.div2_bit Nat.div2_bit

theorem shiftLeft'_add (b m n) : ∀ k, shiftLeft' b m (n + k) = shiftLeft' b (shiftLeft' b m n) k
  | 0 => rfl
  | k + 1 => congr_arg (bit b) (shiftLeft'_add b m n k)
#align nat.shiftl'_add Nat.shiftLeft'_add

theorem shiftLeft_add (m n : Nat) : ∀ k, m <<< (n + k) = (m <<< n) <<< k := by
  intro k; simp only [← shiftLeft'_false, shiftLeft'_add]

theorem shiftLeft'_sub (b m) : ∀ {n k}, k ≤ n → shiftLeft' b m (n - k) = (shiftLeft' b m n) >>> k
  | n, 0, _ => rfl
  | n + 1, k + 1, h => by
    rw [succ_sub_succ_eq_sub, shiftLeft', Nat.add_comm, shiftRight_add]
    simp only [shiftLeft'_sub, Nat.le_of_succ_le_succ h, shiftRight_succ, shiftRight_zero]
    simp [← div2_val, div2_bit]
#align nat.shiftl'_sub Nat.shiftLeft'_sub

theorem shiftLeft_sub : ∀ (m : Nat) {n k}, k ≤ n → m <<< (n - k) = (m <<< n) >>> k :=
  fun _ _ _ hk => by simp only [← shiftLeft'_false, shiftLeft'_sub false _ hk]

@[simp]
theorem testBit_zero (b n) : testBit (bit b n) 0 = b :=
  bodd_bit _ _

#align nat.test_bit_zero Nat.testBit_zero

theorem testBit_succ (m b n) : testBit (bit b n) (succ m) = testBit n m := by
  have : bodd (((bit b n) >>> 1) >>> m) = bodd (n >>> m) := by
    simp only [shiftRight_eq_div_pow]
    simp [← div2_val, div2_bit]
  rw [← shiftRight_add, Nat.add_comm] at this
  exact this
#align nat.test_bit_succ Nat.testBit_succ

#noalign nat.bitwise_bit_aux

end Nat

/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init.Data.Nat.Lemmas
import Init.WFTactics
import Mathlib.Data.Bool.Basic
import Mathlib.Init.Data.Bool.Lemmas
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

/-- `boddDiv2 n` returns a 2-tuple of type `(Bool,Nat)`
    where the `Bool` value indicates whether `n` is odd or not
    and the `Nat` value returns `⌊n/2⌋` -/
def boddDiv2 : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | succ n =>
    match boddDiv2 n with
    | (false, m) => (true, m)
    | (true, m) => (false, succ m)
#align nat.bodd_div2 Nat.boddDiv2

/-- `div2 n = ⌊n/2⌋` the greatest integer smaller than `n/2`-/
def div2 (n : ℕ) : ℕ :=
  (boddDiv2 n).2
#align nat.div2 Nat.div2

/-- `bodd n` returns `true` if `n` is odd-/
def bodd (n : ℕ) : Bool :=
  (boddDiv2 n).1
#align nat.bodd Nat.bodd

@[simp]
theorem bodd_zero : bodd 0 = false :=
  rfl
#align nat.bodd_zero Nat.bodd_zero

theorem bodd_one : bodd 1 = true :=
  rfl
#align nat.bodd_one Nat.bodd_one

theorem bodd_two : bodd 2 = false :=
  rfl
#align nat.bodd_two Nat.bodd_two

@[simp]
theorem bodd_succ (n : ℕ) : bodd (succ n) = not (bodd n) := by
  simp only [bodd, boddDiv2]
  let ⟨b,m⟩ := boddDiv2 n
  cases b <;> rfl
#align nat.bodd_succ Nat.bodd_succ

@[simp]
theorem bodd_add (m n : ℕ) : bodd (m + n) = bxor (bodd m) (bodd n) := by
  induction n <;> simp_all [add_succ, Bool.xor_not]
#align nat.bodd_add Nat.bodd_add

@[simp]
theorem bodd_mul (m n : ℕ) : bodd (m * n) = (bodd m && bodd n) := by
  induction' n with n IH
  · simp
  · simp [mul_succ, IH]
    cases bodd m <;> cases bodd n <;> rfl
#align nat.bodd_mul Nat.bodd_mul

theorem mod_two_of_bodd (n : ℕ) : n % 2 = cond (bodd n) 1 0 := by
  have := congr_arg bodd (mod_add_div n 2)
  simp? [not]  at this
       says simp only [bodd_add, bodd_mul, bodd_succ, not, bodd_zero, Bool.false_and,
      Bool.xor_false] at this
  have _ : ∀ b, and false b = false := by
    intro b
    cases b <;> rfl
  have _ : ∀ b, bxor b false = b := by
    intro b
    cases b <;> rfl
  rw [← this]
  cases' mod_two_eq_zero_or_one n with h h <;> rw [h] <;> rfl
#align nat.mod_two_of_bodd Nat.mod_two_of_bodd

@[simp]
theorem div2_zero : div2 0 = 0 :=
  rfl
#align nat.div2_zero Nat.div2_zero

theorem div2_one : div2 1 = 0 :=
  rfl
#align nat.div2_one Nat.div2_one

theorem div2_two : div2 2 = 1 :=
  rfl
#align nat.div2_two Nat.div2_two

@[simp]
theorem div2_succ (n : ℕ) : div2 (succ n) = cond (bodd n) (succ (div2 n)) (div2 n) := by
  simp only [bodd, boddDiv2, div2]
  rcases boddDiv2 n with ⟨_|_, _⟩ <;> simp
#align nat.div2_succ Nat.div2_succ

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | 0 => rfl
  | succ n => by
    simp only [bodd_succ, Bool.cond_not, div2_succ, Nat.mul_comm]
    refine' Eq.trans _ (congr_arg succ (bodd_add_div2 n))
    cases bodd n <;> simp [cond, not]
    · rw [Nat.add_comm, Nat.add_succ]
    · rw [succ_mul, Nat.add_comm 1, Nat.add_succ]
#align nat.bodd_add_div2 Nat.bodd_add_div2

theorem div2_val (n) : div2 n = n / 2 := by
  refine'
    Nat.eq_of_mul_eq_mul_left (by decide)
      (Nat.add_left_cancel (Eq.trans _ (Nat.mod_add_div n 2).symm))
  rw [mod_two_of_bodd, bodd_add_div2]
#align nat.div2_val Nat.div2_val

/-- `bit b` appends the digit `b` to the binary representation of
  its natural number input. -/
def bit (b : Bool) : ℕ → ℕ :=
  cond b bit1 bit0
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

theorem bit_val (b n) : bit b n = 2 * n + cond b 1 0 := by
  cases b
  apply bit0_val
  apply bit1_val
#align nat.bit_val Nat.bit_val

theorem bit_decomp (n : Nat) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (Nat.add_comm _ _).trans <| bodd_add_div2 _
#align nat.bit_decomp Nat.bit_decomp

/-- For a predicate `C : Nat → Sort*`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for any given natural number. -/
def bitCasesOn {C : Nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := bit_decomp n ▸ h _ _
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

lemma binaryRec_decreasing (h : n ≠ 0) : div2 n < n := by
  rw [div2_val]
  apply (div_lt_iff_lt_mul <| succ_pos 1).2
  have := Nat.mul_lt_mul_of_pos_left (lt_succ_self 1)
    (lt_of_le_of_ne n.zero_le h.symm)
  rwa [Nat.mul_one] at this

/-- A recursion principle for `bit` representations of natural numbers.
  For a predicate `C : Nat → Sort*`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for all natural numbers. -/
def binaryRec {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) : ∀ n, C n :=
  fun n =>
    if n0 : n = 0 then by
      simp only [n0]
      exact z
    else by
      let n' := div2 n
      have _x : bit (bodd n) n' = n := by
        apply bit_decomp n
      rw [← _x]
      exact f (bodd n) n' (binaryRec z f n')
  decreasing_by exact binaryRec_decreasing n0
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

@[simp]
theorem binaryRec_zero {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) :
    binaryRec z f 0 = z := by
  rw [binaryRec]
  rfl
#align nat.binary_rec_zero Nat.binaryRec_zero

/-! bitwise ops -/

theorem bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val]
  simp only [Nat.mul_comm, Nat.add_comm, bodd_add, bodd_mul, bodd_succ, bodd_zero, Bool.not_false,
    Bool.not_true, Bool.and_false, Bool.xor_false]
  cases b <;> cases bodd n <;> rfl
#align nat.bodd_bit Nat.bodd_bit

theorem div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add]
  <;> cases b
  <;> exact by decide
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
theorem testBit_zero (b n) : testBit (bit b n) 0 = b := by
  rw [testBit, bit]
  cases b
  · simp [bit0, ← Nat.mul_two]
  · simp only [cond_true, bit1, bit0, shiftRight_zero, and_one_is_mod, bne_iff_ne]
    simp only [← Nat.mul_two]
    rw [Nat.add_mod]
    simp

#align nat.test_bit_zero Nat.testBit_zero

theorem bodd_eq_and_one_ne_zero : ∀ n, bodd n = (n &&& 1 != 0)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by simpa using bodd_eq_and_one_ne_zero n

theorem testBit_succ (m b n) : testBit (bit b n) (succ m) = testBit n m := by
  have : bodd (((bit b n) >>> 1) >>> m) = bodd (n >>> m) := by
    simp only [shiftRight_eq_div_pow]
    simp [← div2_val, div2_bit]
  rw [← shiftRight_add, Nat.add_comm] at this
  simp only [bodd_eq_and_one_ne_zero] at this
  exact this
#align nat.test_bit_succ Nat.testBit_succ

theorem binaryRec_eq {C : Nat → Sort u} {z : C 0} {f : ∀ b n, C n → C (bit b n)}
    (h : f false 0 z = z) (b n) : binaryRec z f (bit b n) = f b n (binaryRec z f n) := by
  rw [binaryRec]
  split <;> rename_i h'
  · generalize binaryRec z f (bit b n) = e
    revert e
    have bf := bodd_bit b n
    have n0 := div2_bit b n
    rw [h'] at bf n0
    simp only [bodd_zero, div2_zero] at bf n0
    subst bf n0
    rw [binaryRec_zero]
    intros
    rw [h]
    rfl
  · simp only; generalize_proofs h
    revert h
    rw [bodd_bit, div2_bit]
    intros; rfl
#align nat.binary_rec_eq Nat.binaryRec_eq
#noalign nat.bitwise_bit_aux

end Nat

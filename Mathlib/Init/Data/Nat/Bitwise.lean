/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module init.data.nat.bitwise
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.Data.Nat.Lemmas
import Init.WFTactics
import Mathlib.Data.Bool.Basic
import Mathlib.Init.Data.Bool.Lemmas
import Mathlib.Init.ZeroOne
import Mathlib.Tactic.Cases
import Mathlib.Tactic.PermuteGoals

/-!
# Lemmas about bitwise operations on natural numbers.

Possibly only of archaeological significance.
-/

universe u

-- Once we're in the `Nat` namespace, `xor` will inconventiently resolve to `Nat.xor`.
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
  induction' n with n IH
  · simp
  · simp [add_succ, IH]
    cases bodd m <;> cases bodd n <;> rfl
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
  simp [not] at this
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
  cases' boddDiv2 n with fst snd
  cases fst
  case mk.false =>
    simp
  case mk.true =>
    simp

#align nat.div2_succ Nat.div2_succ

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | 0 => rfl
  | succ n => by
    simp
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

/-- For a predicate `C : Nat → Sort _`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for any given natural number. -/
def bitCasesOn {C : Nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := bit_decomp n ▸ h _ _
#align nat.bit_cases_on Nat.bitCasesOn

theorem bit_zero : bit false 0 = 0 :=
  rfl
#align nat.bit_zero Nat.bit_zero

/--`shiftl' b m n` performs a left shift of `m` `n` times
 and adds the bit `b` as the least significant bit each time.
 Returns the corresponding natural number-/
def shiftl' (b : Bool) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => bit b (shiftl' b m n)
#align nat.shiftl' Nat.shiftl'

/-- `shiftl m n` produces a natural number whose binary representation
  is obtained by left-shifting the binary representation of `m` by `n` places -/
def shiftl : ℕ → ℕ → ℕ :=
  shiftl' false
#align nat.shiftl Nat.shiftl

@[simp]
theorem shiftl_zero (m) : shiftl m 0 = m :=
  rfl
#align nat.shiftl_zero Nat.shiftl_zero

@[simp]
theorem shiftl_succ (m n) : shiftl m (n + 1) = bit0 (shiftl m n) :=
  rfl
#align nat.shiftl_succ Nat.shiftl_succ

/--`shiftr n m` performs returns the `m`-step right shift operation on `n` and
returns the resultant number. This is equivalent to performing `⌊n/2ᵐ⌋`-/
def shiftr : ℕ → ℕ → ℕ
  | m, 0 => m
  | m, n + 1 => div2 (shiftr m n)
#align nat.shiftr Nat.shiftr

theorem shiftr_zero : ∀ n, shiftr 0 n = 0 := by
  intro n
  induction' n with n IH
  case zero =>
    rw [shiftr]
  case succ =>
    rw [shiftr, div2, IH]
    rfl

/-- `testBit m n` returns whether the `(n+1)ˢᵗ` least significant bit is `1` or `0`-/
def testBit (m n : ℕ) : Bool :=
  bodd (shiftr m n)
#align nat.test_bit Nat.testBit


lemma binaryRec_decreasing (h : n ≠ 0) : div2 n < n := by
  rw [div2_val]
  apply (div_lt_iff_lt_mul <| succ_pos 1).2
  have := Nat.mul_lt_mul_of_pos_left (lt_succ_self 1)
    (lt_of_le_of_ne n.zero_le h.symm)
  rwa [Nat.mul_one] at this

/-- A recursion principle for `bit` representations of natural numbers.
  For a predicate `C : Nat → Sort _`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for all natural numbers. -/
def binaryRec {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) : ∀ n, C n :=
  fun n =>
    if n0 : n = 0 then
      by
        simp [n0]
        exact z
    else by
      let n' := div2 n
      have _x : bit (bodd n) n' = n := by
        apply bit_decomp n
      rw [←_x]
      exact f (bodd n) n' (binaryRec z f n')
  decreasing_by exact binaryRec_decreasing n0

#align nat.binary_rec Nat.binaryRec

/-- `size n` : Returns the size of a natural number in
bits i.e. the length of its binary representation -/
def size : ℕ → ℕ :=
  binaryRec 0 fun _ _ => succ
#align nat.size Nat.size

/-- `bits n` returns a list of Bools which correspond to the binary representation of n-/
def bits : ℕ → List Bool :=
  binaryRec [] fun b _ IH => b :: IH
#align nat.bits Nat.bits

-- Porting note: There is a `Nat.bitwise` in Lean 4 core,
-- but it is different from the one in mathlib3, so we just port blindly here.
/-- `Nat.bitwise'` (different from `Nat.bitwise` in Lean 4 core)
  applies the function `f` to pairs of bits in the same position in
  the binary representations of its inputs. -/
def bitwise' (f : Bool → Bool → Bool) : ℕ → ℕ → ℕ :=
  binaryRec (fun n => cond (f false true) n 0) fun a m Ia =>
    binaryRec (cond (f true false) (bit a m) 0) fun b n _ => bit (f a b) (Ia n)
#align nat.bitwise Nat.bitwise'

/--`lor'` takes two natural numbers and returns their bitwise `or`-/
def lor' : ℕ → ℕ → ℕ :=
  bitwise' or
#align nat.lor Nat.lor'

/--`land'` takes two naturals numbers and returns their `and`-/
def land' : ℕ → ℕ → ℕ :=
  bitwise' and
#align nat.land Nat.land'

/--`ldiff' a b` performs bitwise set difference. For each corresponding
  pair of bits taken as booleans, say `aᵢ` and `bᵢ`, it applies the
  boolean operation `aᵢ  ∧ bᵢ` to obtain the `iᵗʰ` bit of the result.-/
def ldiff' : ℕ → ℕ → ℕ :=
  bitwise' fun a b => a && not b
#align nat.ldiff Nat.ldiff'

/--`lxor'` computes the bitwise `xor` of two natural numbers-/
def lxor' : ℕ → ℕ → ℕ :=
  bitwise' bxor
#align nat.lxor Nat.lxor'

@[simp]
theorem binaryRec_zero {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) :
    binaryRec z f 0 = z := by
  rw [binaryRec]
  rfl
#align nat.binary_rec_zero Nat.binaryRec_zero

/-! bitwise ops -/

theorem bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val]
  simp
  cases b <;> cases bodd n <;> rfl
#align nat.bodd_bit Nat.bodd_bit

theorem div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add]
  <;> cases b
  <;> exact by decide
#align nat.div2_bit Nat.div2_bit

theorem shiftl'_add (b m n) : ∀ k, shiftl' b m (n + k) = shiftl' b (shiftl' b m n) k
  | 0 => rfl
  | k + 1 => congr_arg (bit b) (shiftl'_add b m n k)
#align nat.shiftl'_add Nat.shiftl'_add

theorem shiftl_add : ∀ m n k, shiftl m (n + k) = shiftl (shiftl m n) k :=
  shiftl'_add _
#align nat.shiftl_add Nat.shiftl_add

theorem shiftr_add (m n) : ∀ k, shiftr m (n + k) = shiftr (shiftr m n) k
  | 0 => rfl
  | k + 1 => congr_arg div2 (shiftr_add m n k)
#align nat.shiftr_add Nat.shiftr_add

theorem shiftl'_sub (b m) : ∀ {n k}, k ≤ n → shiftl' b m (n - k) = shiftr (shiftl' b m n) k
  | n, 0, _ => rfl
  | n + 1, k + 1, h => by
    simp [shiftl']
    rw [Nat.add_comm, shiftr_add]
    simp [shiftr, div2_bit]
    simp [shiftl'_sub, (Nat.le_of_succ_le_succ h)]
#align nat.shiftl'_sub Nat.shiftl'_sub

theorem shiftl_sub : ∀ (m) {n k}, k ≤ n → shiftl m (n - k) = shiftr (shiftl m n) k :=
  shiftl'_sub _
#align nat.shiftl_sub Nat.shiftl_sub

@[simp]
theorem testBit_zero (b n) : testBit (bit b n) 0 = b :=
  bodd_bit _ _
#align nat.test_bit_zero Nat.testBit_zero

theorem testBit_succ (m b n) : testBit (bit b n) (succ m) = testBit n m := by
  have : bodd (shiftr (shiftr (bit b n) 1) m) = bodd (shiftr n m) := by
    dsimp [shiftr]
    rw [div2_bit]
  rw [← shiftr_add, Nat.add_comm] at this
  exact this
#align nat.test_bit_succ Nat.testBit_succ

theorem binaryRec_eq {C : Nat → Sort u} {z : C 0} {f : ∀ b n, C n → C (bit b n)}
    (h : f false 0 z = z) (b n) : binaryRec z f (bit b n) = f b n (binaryRec z f n) := by
  rw [binaryRec]
  by_cases h : bit b n = 0
  -- Note: this renames the original `h : f false 0 z = z` to `h'` and leaves `h : bit b n = 0`
  case pos h' =>
    simp [dif_pos h]
    generalize binaryRec z f (bit b n) = e
    revert e
    have bf := bodd_bit b n
    have n0 := div2_bit b n
    rw [h] at bf n0
    simp at bf n0
    subst bf n0
    rw [binaryRec_zero]
    intros
    rw [h']
    rfl
  case neg h' =>
    simp [dif_neg h]
    generalize @id (C (bit b n) = C (bit (bodd (bit b n)) (div2 (bit b n))))
      (Eq.symm (bit_decomp (bit b n)) ▸ Eq.refl (C (bit b n))) = e
    revert e
    rw [bodd_bit, div2_bit]
    intros ; rfl
#align nat.binary_rec_eq Nat.binaryRec_eq

theorem bitwise'_bit_aux {f : Bool → Bool → Bool} (h : f false false = false) :
    (@binaryRec (fun _ => ℕ) (cond (f true false) (bit false 0) 0) fun b n _ =>
        bit (f false b) (cond (f false true) n 0)) =
      fun n : ℕ => cond (f false true) n 0 := by
  funext n
  apply bitCasesOn n
  intro b n
  rw [binaryRec_eq]
  · cases b
    <;> try rw [h]
    <;> induction' fft : f false true
    <;> simp [cond]
    cases f false true
    case h.true.false => simp
    case h.true.true => simp
  · rw [h, show cond (f false true) 0 0 = 0 by cases f false true <;> rfl,
        show cond (f true false) (bit false 0) 0 = 0 by cases f true false <;> rfl]
    rfl
#align nat.bitwise_bit_aux Nat.bitwise'_bit_aux


-- Porting Note : This was a @[simp] lemma in mathlib3
theorem bitwise'_zero_left (f : Bool → Bool → Bool) (n) :
    bitwise' f 0 n = cond (f false true) n 0 := by
  unfold bitwise'; rw [binaryRec_zero]

#align nat.bitwise_zero_left Nat.bitwise'_zero_left

@[simp]
theorem bitwise'_zero_right (f : Bool → Bool → Bool) (h : f false false = false) (m) :
    bitwise' f m 0 = cond (f true false) m 0 := by
  unfold bitwise'; apply bitCasesOn m; intros; rw [binaryRec_eq, binaryRec_zero];
    exact bitwise'_bit_aux h

#align nat.bitwise_zero_right Nat.bitwise'_zero_right

@[simp]
theorem bitwise'_zero (f : Bool → Bool → Bool) : bitwise' f 0 0 = 0 := by
  rw [bitwise'_zero_left]
  cases f false true <;> rfl
#align nat.bitwise_zero Nat.bitwise'_zero

@[simp]
theorem bitwise'_bit {f : Bool → Bool → Bool} (h : f false false = false) (a m b n) :
    bitwise' f (bit a m) (bit b n) = bit (f a b) (bitwise' f m n) := by
  unfold bitwise'
  rw [binaryRec_eq, binaryRec_eq]
  · induction' ftf : f true false
    rw [show f a false = false by cases a <;> assumption]
    apply @congr_arg _ _ _ 0 (bit false)
    swap
    rw [show f a false = a by cases a <;> assumption]
    apply congr_arg (bit a)
    all_goals
    { apply bitCasesOn m
      intro a m
      rw [binaryRec_eq, binaryRec_zero]
      · rfl
      · rw [← bitwise'_bit_aux h, ftf] }
  · exact bitwise'_bit_aux h
#align nat.bitwise_bit Nat.bitwise'_bit

theorem bitwise'_swap {f : Bool → Bool → Bool} (h : f false false = false) :
    bitwise' (Function.swap f) = Function.swap (bitwise' f) := by
  funext m n; revert n
  dsimp [Function.swap]
  apply binaryRec _ _ m <;> intro n
  · rw [bitwise'_zero_left, bitwise'_zero_right]
    exact h
  · intros a ih m'
    apply bitCasesOn m'; intro b n'
    rw [bitwise'_bit, bitwise'_bit, ih] <;> exact h
#align nat.bitwise_swap Nat.bitwise'_swap

-- Porting note:
-- If someone wants to merge `bitwise` and `bitwise'`
-- (and similarly `lor` / `lor'` and `land` / `land'`)
-- they could start by proving the next theorem:
-- lemma bitwise_eq_bitwise' (f : Bool → Bool → Bool) :
--     bitwise f = bitwise' f := by
--   sorry

-- @[simp]
-- theorem bitwise_bit {f : Bool → Bool → Bool} (h : f false false = false) (a m b n) :
--     bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
--   simp only [bitwise_eq_bitwise', bitwise'_bit h]

@[simp]
theorem lor'_bit : ∀ a m b n, lor' (bit a m) (bit b n) = bit (a || b) (lor' m n) :=
  bitwise'_bit rfl
#align nat.lor_bit Nat.lor'_bit

@[simp]
theorem land'_bit : ∀ a m b n, land' (bit a m) (bit b n) = bit (a && b) (land' m n) :=
  bitwise'_bit rfl
#align nat.land_bit Nat.land'_bit

@[simp]
theorem ldiff'_bit : ∀ a m b n, ldiff' (bit a m) (bit b n) = bit (a && not b) (ldiff' m n) :=
  bitwise'_bit rfl
#align nat.ldiff_bit Nat.ldiff'_bit

@[simp]
theorem lxor'_bit : ∀ a m b n, lxor' (bit a m) (bit b n) = bit (bxor a b) (lxor' m n) :=
  bitwise'_bit rfl
#align nat.lxor_bit Nat.lxor'_bit

@[simp]
theorem testBit_bitwise' {f : Bool → Bool → Bool} (h : f false false = false) (m n k) :
    testBit (bitwise' f m n) k = f (testBit m k) (testBit n k) := by
  revert m n; induction' k with k IH <;>
  intros m n <;>
  apply bitCasesOn m <;> intros a m' <;>
  apply bitCasesOn n <;> intros b n' <;>
  rw [bitwise'_bit h]
  · simp [testBit_zero]
  · simp [testBit_succ, IH]
#align nat.test_bit_bitwise Nat.testBit_bitwise'

@[simp]
theorem testBit_lor' : ∀ m n k, testBit (lor' m n) k = (testBit m k || testBit n k) :=
  testBit_bitwise' rfl
#align nat.test_bit_lor Nat.testBit_lor'

@[simp]
theorem testBit_land' : ∀ m n k, testBit (land' m n) k = (testBit m k && testBit n k) :=
  testBit_bitwise' rfl
#align nat.test_bit_land Nat.testBit_land'

@[simp]
theorem testBit_ldiff' : ∀ m n k, testBit (ldiff' m n) k = (testBit m k && not (testBit n k)) :=
  testBit_bitwise' rfl
#align nat.test_bit_ldiff Nat.testBit_ldiff'

@[simp]
theorem testBit_lxor' : ∀ m n k, testBit (lxor' m n) k = bxor (testBit m k) (testBit n k) :=
  testBit_bitwise' rfl
#align nat.test_bit_lxor Nat.testBit_lxor'

end Nat

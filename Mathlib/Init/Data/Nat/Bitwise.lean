/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

! This file was ported from Lean 3 source module init.data.nat.bitwise
! leanprover-community/lean commit 53e8520d8964c7632989880372d91ba0cecbaf00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.Data.Nat.Lemmas
import Init.WFTactics

-- Imported for Boolean `xor`
import Mathlib.Data.Bool.Basic
import Mathlib.Init.Data.Bool.Lemmas

-- Imported for `bit0` and `bit1`
import Mathlib.Init.ZeroOne

-- Imported for cases'
import Mathlib.Tactic.Cases

universe u

-- The following line helps override the default behaviour, wherein
-- lean equates xor with Nat.xor
-- bxor points to Mathlib.Data.Bool.Basic.xor
--- Author : Shreyas Srinivas
abbrev bxor := xor

namespace Nat
set_option linter.deprecated false

def boddDiv2 : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | succ n =>
    match boddDiv2 n with
    | (false, m) => (true, m)
    | (true, m) => (false, succ m)
#align nat.bodd_div2 Nat.boddDiv2

def div2 (n : ℕ) : ℕ :=
  (boddDiv2 n).2
#align nat.div2 Nat.div2

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
  -- Cite : Kevin Buzzard
  -- URL: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/help.20with.20.60unfold.60/near/316776867
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
    intros
    rename_i b
    cases b
    case false => rfl
    case true => rfl
  have _ : ∀ b, bxor b false = b := by
    intros
    rename_i b'
    cases b'
    case false => rfl
    case true => rfl
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
  cases boddDiv2 n
  rename_i fst snd
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

def bitCasesOn {C : Nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := by
  rw [← bit_decomp n]
  apply h
#align nat.bit_cases_on Nat.bitCasesOn

theorem bit_zero : bit false 0 = 0 :=
  rfl
#align nat.bit_zero Nat.bit_zero

def shiftl' (b : Bool) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => bit b (shiftl' b m n)
#align nat.shiftl' Nat.shiftl'

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

def shiftr : ℕ → ℕ → ℕ
  | m, 0 => m
  | m, n + 1 => div2 (shiftr m n)
#align nat.shiftr Nat.shiftr

theorem shiftr_zero : ∀ n, shiftr 0 n = 0 := by
  intros
  rename_i n
  induction' n with n IH
  case zero =>
    rw [shiftr]
  case succ =>
    rw[shiftr]
    rw [div2]
    rw [IH]
    rfl

def testBit (m n : ℕ) : Bool :=
  bodd (shiftr m n)
#align nat.test_bit Nat.testBit

def binaryRec {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) : ∀ n, C n :=
    fun n =>
      if n0 : n = 0 then
        by
          simp [n0]
          exact z
      else by
        let n' := div2 n
        have : n' < n := by
          change div2 n < n; rw [div2_val]
          apply (div_lt_iff_lt_mul <| succ_pos 1).2
          have := Nat.mul_lt_mul_of_pos_left (lt_succ_self 1) (lt_of_le_of_ne n.zero_le (Ne.symm n0))
          rwa [Nat.mul_one] at this
        have _x : bit (bodd n) n' = n := by
          apply bit_decomp n
        rw [←_x]
        exact f (bodd n) n' (binaryRec z f n')

#align nat.binaryRec Nat.binaryRec

def size : ℕ → ℕ :=
  binaryRec 0 fun _ _ => succ
#align nat.size Nat.size

def bits : ℕ → List Bool :=
  binaryRec [] fun b _ IH => b :: IH
#align nat.bits Nat.bits

--#print Nat.bitwise
/-
def bitwise (f : Bool → Bool → Bool) : ℕ → ℕ → ℕ :=
  binaryRec (fun n => cond (f false true) n 0) fun a m Ia =>
    binaryRec (cond (f true false) (bit a m) 0) fun b n _ => bit (f a b) (Ia n)
#align nat.bitwise Nat.bitwise
-/

--#print Nat.lor
/-
def lor : ℕ → ℕ → ℕ :=
  bitwise or
#align nat.lor Nat.lor
-/

-- #print Nat.land
/-
def land : ℕ → ℕ → ℕ :=
  bitwise and
#align nat.land Nat.land
-/

def ldiff : ℕ → ℕ → ℕ :=
  bitwise fun a b => a && not b
#align nat.ldiff Nat.ldiff

def lxor : ℕ → ℕ → ℕ :=
  bitwise bxor
#align nat.lxor Nat.lxor

@[simp]
theorem binary_rec_zero {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) :
    binaryRec z f 0 = z := by
  rw [binaryRec]
  rfl
#align nat.binary_rec_zero Nat.binary_rec_zero

/-! bitwise ops -/


theorem bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val]
  simp
  cases b <;> cases bodd n <;> rfl
#align nat.bodd_bit Nat.bodd_bit

theorem div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add] <;> cases b <;>
    exact by decide
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
theorem test_bit_zero (b n) : testBit (bit b n) 0 = b :=
  bodd_bit _ _
#align nat.test_bit_zero Nat.test_bit_zero

theorem test_bit_succ (m b n) : testBit (bit b n) (succ m) = testBit n m := by
  have : bodd (shiftr (shiftr (bit b n) 1) m) = bodd (shiftr n m) := by
    dsimp [shiftr]
    rw [div2_bit]
  rw [← shiftr_add, Nat.add_comm] at this
  exact this
#align nat.test_bit_succ Nat.test_bit_succ

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:145:2: warning: unsupported: with_cases -/
theorem binary_rec_eq {C : Nat → Sort u} {z : C 0} {f : ∀ b n, C n → C (bit b n)}
    (h : f false 0 z = z) (b n) : binaryRec z f (bit b n) = f b n (binaryRec z f n) := by
  rw [binaryRec]
  by_cases bit b n = 0
  case pos h' =>
    simp [dif_pos h']
    generalize binaryRec z f (bit b n) = e
    revert e
    have bf := bodd_bit b n
    have n0 := div2_bit b n
    rw [h] at bf n0
    simp at bf n0
    rw [← bf, ← n0]
    rw [binary_rec_zero]
    intros
    rw [h']
    rfl
  case neg h' =>
    simp only [h']
    simp only [dif_neg h]
    have b₁: bodd (bit b n) = b := by
      rw[bodd_bit]
    have d₁ : div2 (bit b n) = n := by
      rw[div2_bit]
    have pC₁: C (bit (bodd (bit b n)) (div2 (bit b n))) = C (bit b n) := by
      rw[b₁, d₁]
    have pf : f b n = f (bodd (bit b n)) (div2 (bit b n)) := by
      rw[b₁,d₁]
    simp only [pf]
    /-simp only [h']

    rw [Eq.mpr]
    have b₁: bodd (bit b n) = b := by
      rw[bodd_bit]
    have d₁ : div2 (bit b n) = n := by
      rw[div2_bit]

    rw [b₁, d₁]-/
#align nat.binary_rec_eq Nat.binary_rec_eq

theorem bitwise_bit_aux {f : Bool → Bool → Bool} (h : f false false = false) :
    (@binaryRec (fun _ => ℕ) (cond (f true false) (bit false 0) 0) fun b n _ =>
        bit (f false b) (cond (f false true) n 0)) =
      fun n : ℕ => cond (f false true) n 0 :=
  by
  funext n
  apply bitCasesOn n
  intro b n
  rw [binary_rec_eq]
  · cases b
    <;> try rw [h]
    <;> induction' fft : f false true
    <;> simp [cond]
    cases f false true
    case h.true.false => simp
    case h.true.true => simp
  ·
    rw [h, show cond (f false true) 0 0 = 0 by cases f false true <;> rfl,
        show cond (f true false) (bit false 0) 0 = 0 by cases f true false <;> rfl]
    rfl
#align nat.bitwise_bit_aux Nat.bitwise_bit_aux

@[simp]
theorem bitwise_zero_left (f : Bool → Bool → Bool) (n) : bitwise f 0 n = cond (f false true) n 0 :=
  by
    rw [bitwise]
    simp
    cases (f false true) <;> rfl

#align nat.bitwise_zero_left Nat.bitwise_zero_left

@[simp]
theorem bitwise_zero_right (f : Bool → Bool → Bool) (_ : f false false = false) (m) :
    bitwise f m 0 = cond (f true false) m 0 := by
      unfold bitwise
      apply bitCasesOn m
      simp
      cases f true false
      <;> simp
      apply And.intro
      case true.left =>
        have proof_left : ∀ (n : ℕ), (if bit false n = 0 then 0 else bit false n) = bit false n :=
          (λ n =>
            by
              cases bit false n <;> simp)
        exact proof_left
      case true.right =>
        have proof_right : ∀ (n : ℕ), (if bit true n = 0 then 0 else bit true n) = bit true n :=
          (λ n =>
            by
              cases bit true n <;> simp)
        exact proof_right

#align nat.bitwise_zero_right Nat.bitwise_zero_right

@[simp]
theorem bitwise_zero (f : Bool → Bool → Bool) : bitwise f 0 0 = 0 := by
  rw [bitwise_zero_left]
  cases f false true <;> rfl
#align nat.bitwise_zero Nat.bitwise_zero

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.swap -/
@[simp]
theorem bitwise_bit {f : Bool → Bool → Bool} (h : f false false = false) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  unfold bitwise
  simp only [binary_rec_eq]
  cases bit a m <;> simp
    case zero => simp
    case succ => simp
  /-· induction' ftf : f true false
    dsimp [cond]
    cases bit a m <;> simp-/
    /-rw [show f a false = false by cases a <;> assumption]
    apply @congr_arg _ _ _ 0 (bit false)
    run_tac
      tactic.swap
    rw [show f a ff = a by cases a <;> assumption]
    apply congr_arg (bit a)
    all_goals
      apply bitCasesOn m; intro a m
      rw [binary_rec_eq, binary_rec_zero]
      rw [← bitwise_bit_aux h, ftf]; rfl

  · exact bitwise_bit_aux h -/
#align nat.bitwise_bit Nat.bitwise_bit

theorem bitwise_swap {f : Bool → Bool → Bool} (h : f false false = false) :
    bitwise (Function.swap f) = Function.swap (bitwise f) := by
  funext m n; revert n
  dsimp [Function.swap]
  apply binaryRec _ (fun a m' IH => _) m <;> intro n
  · rw [bitwise_zero_left, bitwise_zero_right]
    exact h
  apply bitCasesOn m <;> intro b n'
  rw [bitwise_bit, bitwise_bit, IH] <;> exact h
#align nat.bitwise_swap Nat.bitwise_swap

@[simp]
theorem lor_bit : ∀ a m b n, lor (bit a m) (bit b n) = bit (a || b) (lor m n) :=
  bitwise_bit rfl
#align nat.lor_bit Nat.lor_bit

@[simp]
theorem land_bit : ∀ a m b n, land (bit a m) (bit b n) = bit (a && b) (land m n) :=
  bitwise_bit rfl
#align nat.land_bit Nat.land_bit

@[simp]
theorem ldiff_bit : ∀ a m b n, ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) :=
  bitwise_bit rfl
#align nat.ldiff_bit Nat.ldiff_bit

@[simp]
theorem lxor_bit : ∀ a m b n, lxor (bit a m) (bit b n) = bit (bxor a b) (lxor m n) :=
  bitwise_bit rfl
#align nat.lxor_bit Nat.lxor_bit

@[simp]
theorem test_bit_bitwise {f : Bool → Bool → Bool} (h : f false false = false) (m n k) :
    testBit (bitwise f m n) k = f (testBit m k) (testBit n k) := by
  revert m n
  induction' k with k IH
  intro m n <;> apply bitCasesOn m
  intro a m' <;>
  apply bitCasesOn n
  intro b n'
  rw [bitwise_bit h]
  · simp [test_bit_zero]
  · intros
    rename_i m n
    rw [bitwise]
    cases m <;> simp
    cases n <;> simp
    case succ.zero.zero =>
      rw [testBit]
      rw [shiftr_zero]
      rw [bodd, boddDiv2]
      rw [h]
    case succ.zero.succ =>
      simp only [test_bit_succ]
      have test_bit_zero_zero: ∀ k, testBit 0 k = false := by
        intro k
        unfold testBit
        rw [shiftr_zero]
        rw [bodd, boddDiv2]
      rw[test_bit_zero_zero]
      rename_i n
      cases testBit (succ n) (succ k) <;> simp [h]
      case false =>
        cases f false true
        simp
        try rw [test_bit_zero_zero]
        simp
        rfl
      case true =>
        cases f false true <;> simp
        try rw [test_bit_zero_zero]
        rfl

#align nat.test_bit_bitwise Nat.test_bit_bitwise

@[simp]
theorem test_bit_lor : ∀ m n k, testBit (lor m n) k = (testBit m k || testBit n k) :=
  test_bit_bitwise rfl
#align nat.test_bit_lor Nat.test_bit_lor

@[simp]
theorem test_bit_land : ∀ m n k, testBit (land m n) k = (testBit m k && testBit n k) :=
  test_bit_bitwise rfl
#align nat.test_bit_land Nat.test_bit_land

@[simp]
theorem test_bit_ldiff : ∀ m n k, testBit (ldiff m n) k = (testBit m k && not (testBit n k)) :=
  test_bit_bitwise rfl
#align nat.test_bit_ldiff Nat.test_bit_ldiff

@[simp]
theorem test_bit_lxor : ∀ m n k, testBit (lxor m n) k = bxor (testBit m k) (testBit n k) :=
  test_bit_bitwise rfl
#align nat.test_bit_lxor Nat.test_bit_lxor

end Nat

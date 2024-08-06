/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.Nat.Defs
import Mathlib.Init.Data.List.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GeneralizeProofs
import Mathlib.Tactic.Says

/-!
# Additional properties of binary recursion on `Nat`

This file documents additional properties of binary recursion,
which allows us to more easily work with operations which do depend
on the number of leading zeros in the binary representation of `n`.
For example, we can more easily work with `Nat.bits` and `Nat.size`.

See also: `Nat.bitwise`, `Nat.pow` (for various lemmas about `size` and `shiftLeft`/`shiftRight`),
and `Nat.digits`.
-/

-- Once we're in the `Nat` namespace, `xor` will inconveniently resolve to `Nat.xor`.
/-- `bxor` denotes the `xor` function i.e. the exclusive-or function on type `Bool`. -/
local notation "bxor" => _root_.xor

namespace Nat
universe u
variable {m n : ℕ}

/-- `boddDiv2 n` returns a 2-tuple of type `(Bool, Nat)` where the `Bool` value indicates whether
`n` is odd or not and the `Nat` value returns `⌊n/2⌋` -/
@[deprecated (since := "2024-06-09")] def boddDiv2 : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | succ n =>
    match boddDiv2 n with
    | (false, m) => (true, m)
    | (true, m) => (false, succ m)

/-- `div2 n = ⌊n/2⌋` the greatest integer smaller than `n/2`-/
def div2 (n : ℕ) : ℕ := n >>> 1

theorem div2_val (n) : div2 n = n / 2 := rfl

/-- `bodd n` returns `true` if `n` is odd-/
def bodd (n : ℕ) : Bool := 1 &&& n != 0

@[simp] lemma bodd_zero : bodd 0 = false := rfl

lemma bodd_one : bodd 1 = true := rfl

lemma bodd_two : bodd 2 = false := rfl

@[simp]
lemma bodd_succ (n : ℕ) : bodd (succ n) = not (bodd n) := by
  simp only [bodd, succ_eq_add_one, one_and_eq_mod_two]
  cases mod_two_eq_zero_or_one n with | _ h => simp [h, add_mod]

@[simp]
lemma bodd_add (m n : ℕ) : bodd (m + n) = bxor (bodd m) (bodd n) := by
  induction n
  case zero => simp
  case succ n ih => simp [← Nat.add_assoc, Bool.xor_not, ih]

@[simp]
lemma bodd_mul (m n : ℕ) : bodd (m * n) = (bodd m && bodd n) := by
  induction' n with n IH
  · simp
  · simp only [mul_succ, bodd_add, IH, bodd_succ]
    cases bodd m <;> cases bodd n <;> rfl

lemma bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val]
  simp only [Nat.mul_comm, Nat.add_comm, bodd_add, bodd_mul, bodd_succ, bodd_zero, Bool.not_false,
    Bool.not_true, Bool.and_false, Bool.xor_false]
  cases b <;> cases bodd n <;> rfl

lemma mod_two_of_bodd (n : ℕ) : n % 2 = cond (bodd n) 1 0 := by
  have := congr_arg bodd (mod_add_div n 2)
  simp? [not] at this says
    simp only [bodd_add, bodd_mul, bodd_succ, not, bodd_zero, Bool.false_and, Bool.bne_false]
      at this
  have _ : ∀ b, and false b = false := by
    intro b
    cases b <;> rfl
  have _ : ∀ b, bxor b false = b := by
    intro b
    cases b <;> rfl
  rw [← this]
  cases' mod_two_eq_zero_or_one n with h h <;> rw [h] <;> rfl

theorem div2_add_bodd (n : Nat) : 2 * div2 n + cond (bodd n) 1 0 = n := by
  rw [← mod_two_of_bodd, div2_val, Nat.div_add_mod]

@[simp] lemma div2_zero : div2 0 = 0 := rfl

lemma div2_one : div2 1 = 0 := rfl

lemma div2_two : div2 2 = 1 := rfl

lemma div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add]
  <;> cases b
  <;> decide

@[simp]
lemma div2_succ (n : ℕ) : div2 (succ n) = cond (bodd n) (succ (div2 n)) (div2 n) := by
  cases n using bitCasesOn with
  | h b n => cases b <;> simp [bit_val, div2_val, succ_div]

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

lemma bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | 0 => rfl
  | succ n => by
    simp only [bodd_succ, Bool.cond_not, div2_succ, Nat.mul_comm]
    refine Eq.trans ?_ (congr_arg succ (bodd_add_div2 n))
    cases bodd n
    · simp
    · simp; omega

lemma bit_decomp (n : Nat) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (Nat.add_comm _ _).trans <| bodd_add_div2 _

theorem binaryRec_of_ne_zero {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) {n}
    (h : n ≠ 0) :
    binaryRec z f n = n.bit_decomp ▸ f n.bodd n.div2 (binaryRec z f n.div2) := by
  rw [binaryRec, dif_neg h, eqRec_eq_cast, eqRec_eq_cast]; rfl

lemma bit_zero : bit false 0 = 0 :=
  rfl

/-- `shiftLeft' b m n` performs a left shift of `m` `n` times
 and adds the bit `b` as the least significant bit each time.
 Returns the corresponding natural number-/
def shiftLeft' (b : Bool) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => bit b (shiftLeft' b m n)

@[simp]
lemma shiftLeft'_false : ∀ n, shiftLeft' false m n = m <<< n
  | 0 => rfl
  | n + 1 => by
    have : 2 * (m * 2^n) = 2^(n+1)*m := by
      rw [Nat.mul_comm, Nat.mul_assoc, ← Nat.pow_succ]; simp
    simp [shiftLeft_eq, shiftLeft', bit_val, shiftLeft'_false, this]

/-- Lean takes the unprimed name for `Nat.shiftLeft_eq m n : m <<< n = m * 2 ^ n`. -/
@[simp] lemma shiftLeft_eq' (m n : Nat) : shiftLeft m n = m <<< n := rfl
@[simp] lemma shiftRight_eq (m n : Nat) : shiftRight m n = m >>> n := rfl

/-- `size n` : Returns the size of a natural number in
bits i.e. the length of its binary representation -/
def size : ℕ → ℕ :=
  binaryRec 0 fun _ _ => succ

/-- `bits n` returns a list of Bools which correspond to the binary representation of n, where
    the head of the list represents the least significant bit -/
def bits : ℕ → List Bool :=
  binaryRec [] fun b _ IH => b :: IH

/-- `ldiff a b` performs bitwise set difference. For each corresponding
  pair of bits taken as booleans, say `aᵢ` and `bᵢ`, it applies the
  boolean operation `aᵢ ∧ ¬bᵢ` to obtain the `iᵗʰ` bit of the result. -/
def ldiff : ℕ → ℕ → ℕ :=
  bitwise fun a b => a && not b

/-! bitwise ops -/

lemma shiftLeft'_add (b m n) : ∀ k, shiftLeft' b m (n + k) = shiftLeft' b (shiftLeft' b m n) k
  | 0 => rfl
  | k + 1 => congr_arg (bit b) (shiftLeft'_add b m n k)

lemma shiftLeft'_sub (b m) : ∀ {n k}, k ≤ n → shiftLeft' b m (n - k) = (shiftLeft' b m n) >>> k
  | n, 0, _ => rfl
  | n + 1, k + 1, h => by
    rw [succ_sub_succ_eq_sub, shiftLeft', Nat.add_comm, shiftRight_add]
    simp only [shiftLeft'_sub, Nat.le_of_succ_le_succ h, shiftRight_succ, shiftRight_zero]
    simp [← div2_val, div2_bit]

lemma shiftLeft_sub : ∀ (m : Nat) {n k}, k ≤ n → m <<< (n - k) = (m <<< n) >>> k :=
  fun _ _ _ hk => by simp only [← shiftLeft'_false, shiftLeft'_sub false _ hk]

lemma bodd_eq_one_and_ne_zero : ∀ n, bodd n = (1 &&& n != 0)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by simpa using bodd_eq_one_and_ne_zero n

lemma testBit_bit_succ (m b n) : testBit (bit b n) (succ m) = testBit n m := by
  have : bodd (((bit b n) >>> 1) >>> m) = bodd (n >>> m) := by
    simp only [shiftRight_eq_div_pow]
    simp [← div2_val, div2_bit]
  rw [← shiftRight_add, Nat.add_comm] at this
  simp only [bodd_eq_one_and_ne_zero] at this
  exact this

/-! ### `bit0` and `bit1` -/

theorem bit_add : ∀ (b : Bool) (n m : ℕ), bit b (n + m) = bit false n + bit b m
  | true,  _, _ => by dsimp [bit]; omega
  | false, _, _ => by dsimp [bit]; omega

theorem bit_add' : ∀ (b : Bool) (n m : ℕ), bit b (n + m) = bit b n + bit false m
  | true,  _, _ => by dsimp [bit]; omega
  | false, _, _ => by dsimp [bit]; omega

theorem bit_ne_zero (b) {n} (h : n ≠ 0) : bit b n ≠ 0 :=
  bit_eq_zero_iff.not.mpr (h ·.1)

@[simp]
theorem bitCasesOn_bit0 {C : ℕ → Sort u} (H : ∀ b n, C (bit b n)) (n : ℕ) :
    bitCasesOn (2 * n) H = H false n :=
  bitCasesOn_bit H false n

@[simp]
theorem bitCasesOn_bit1 {C : ℕ → Sort u} (H : ∀ b n, C (bit b n)) (n : ℕ) :
    bitCasesOn (2 * n + 1) H = H true n :=
  bitCasesOn_bit H true n

theorem bit_cases_on_injective {C : ℕ → Sort u} :
    Function.Injective fun H : ∀ b n, C (bit b n) => fun n => bitCasesOn n H := by
  intro H₁ H₂ h
  ext b n
  simpa only [bitCasesOn_bit] using congr_fun h (bit b n)

@[simp]
theorem bit_cases_on_inj {C : ℕ → Sort u} (H₁ H₂ : ∀ b n, C (bit b n)) :
    ((fun n => bitCasesOn n H₁) = fun n => bitCasesOn n H₂) ↔ H₁ = H₂ :=
  bit_cases_on_injective.eq_iff

lemma bit_le : ∀ (b : Bool) {m n : ℕ}, m ≤ n → bit b m ≤ bit b n
  | true, _, _, h => by dsimp [bit]; omega
  | false, _, _, h => by dsimp [bit]; omega

lemma bit_lt_bit (a b) (h : m < n) : bit a m < bit b n := calc
  bit a m < 2 * n   := by cases a <;> dsimp [bit] <;> omega
        _ ≤ bit b n := by cases b <;> dsimp [bit] <;> omega

@[deprecated (since := "2024-06-09")] alias binaryRec_eq' := Nat.binaryRec_eq

@[simp]
theorem zero_bits : bits 0 = [] := by simp [Nat.bits]

@[simp]
theorem bits_append_bit (n : ℕ) (b : Bool) (hn : n = 0 → b = true) :
    (bit b n).bits = b :: n.bits := by
  rw [Nat.bits, Nat.bits, binaryRec_eq]
  simpa

@[simp]
theorem bit0_bits (n : ℕ) (hn : n ≠ 0) : (2 * n).bits = false :: n.bits :=
  bits_append_bit n false fun hn' => absurd hn' hn

@[simp]
theorem bit1_bits (n : ℕ) : (2 * n + 1).bits = true :: n.bits :=
  bits_append_bit n true fun _ => rfl

@[simp]
theorem one_bits : Nat.bits 1 = [true] := by
  convert bit1_bits 0

-- TODO Find somewhere this can live.
-- example : bits 3423 = [true, true, true, true, true, false, true, false, true, false, true, true]
-- := by norm_num

theorem bodd_eq_bits_head (n : ℕ) : n.bodd = n.bits.headI := by
  induction' n using Nat.binaryRec' with b n h _; · simp
  simp [bodd_bit, bits_append_bit _ _ h]

theorem div2_bits_eq_tail (n : ℕ) : n.div2.bits = n.bits.tail := by
  induction' n using Nat.binaryRec' with b n h _; · simp
  simp [div2_bit, bits_append_bit _ _ h]

end Nat

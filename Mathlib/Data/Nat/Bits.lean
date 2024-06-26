/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathlib.Init.Data.List.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GeneralizeProofs
import Mathlib.Tactic.Says

#align_import data.nat.bits from "leanprover-community/mathlib"@"d012cd09a9b256d870751284dd6a29882b0be105"

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

-- As this file is all about `bit0` and `bit1`,
-- we turn off the deprecated linter for the whole file.
set_option linter.deprecated false

namespace Nat
universe u
variable {m n : ℕ}

/-- `boddDiv2 n` returns a 2-tuple of type `(Bool, Nat)` where the `Bool` value indicates whether
`n` is odd or not and the `Nat` value returns `⌊n/2⌋` -/
def boddDiv2 : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | succ n =>
    match boddDiv2 n with
    | (false, m) => (true, m)
    | (true, m) => (false, succ m)
#align nat.bodd_div2 Nat.boddDiv2

/-- `div2 n = ⌊n/2⌋` the greatest integer smaller than `n/2`-/
def div2 (n : ℕ) : ℕ := (boddDiv2 n).2
#align nat.div2 Nat.div2

/-- `bodd n` returns `true` if `n` is odd-/
def bodd (n : ℕ) : Bool := (boddDiv2 n).1
#align nat.bodd Nat.bodd

@[simp] lemma bodd_zero : bodd 0 = false := rfl
#align nat.bodd_zero Nat.bodd_zero

lemma bodd_one : bodd 1 = true := rfl
#align nat.bodd_one Nat.bodd_one

lemma bodd_two : bodd 2 = false := rfl
#align nat.bodd_two Nat.bodd_two

@[simp]
lemma bodd_succ (n : ℕ) : bodd (succ n) = not (bodd n) := by
  simp only [bodd, boddDiv2]
  let ⟨b,m⟩ := boddDiv2 n
  cases b <;> rfl
#align nat.bodd_succ Nat.bodd_succ

@[simp]
lemma bodd_add (m n : ℕ) : bodd (m + n) = bxor (bodd m) (bodd n) := by
  induction n
  case zero => simp
  case succ n ih => simp [← Nat.add_assoc, Bool.xor_not, ih]
#align nat.bodd_add Nat.bodd_add

@[simp]
lemma bodd_mul (m n : ℕ) : bodd (m * n) = (bodd m && bodd n) := by
  induction' n with n IH
  · simp
  · simp only [mul_succ, bodd_add, IH, bodd_succ]
    cases bodd m <;> cases bodd n <;> rfl
#align nat.bodd_mul Nat.bodd_mul

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
#align nat.mod_two_of_bodd Nat.mod_two_of_bodd

@[simp] lemma div2_zero : div2 0 = 0 := rfl
#align nat.div2_zero Nat.div2_zero

lemma div2_one : div2 1 = 0 := rfl
#align nat.div2_one Nat.div2_one

lemma div2_two : div2 2 = 1 := rfl
#align nat.div2_two Nat.div2_two

@[simp]
lemma div2_succ (n : ℕ) : div2 (succ n) = cond (bodd n) (succ (div2 n)) (div2 n) := by
  simp only [bodd, boddDiv2, div2]
  rcases boddDiv2 n with ⟨_|_, _⟩ <;> simp
#align nat.div2_succ Nat.div2_succ

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

lemma bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | 0 => rfl
  | succ n => by
    simp only [bodd_succ, Bool.cond_not, div2_succ, Nat.mul_comm]
    refine Eq.trans ?_ (congr_arg succ (bodd_add_div2 n))
    cases bodd n
    · simp
    · simp; omega
#align nat.bodd_add_div2 Nat.bodd_add_div2

lemma div2_val (n) : div2 n = n / 2 := by
  refine Nat.eq_of_mul_eq_mul_left (by decide)
    (Nat.add_left_cancel (Eq.trans ?_ (Nat.mod_add_div n 2).symm))
  rw [mod_two_of_bodd, bodd_add_div2]
#align nat.div2_val Nat.div2_val

/-- `bit b` appends the digit `b` to the binary representation of its natural number input. -/
def bit (b : Bool) : ℕ → ℕ := cond b bit1 bit0
#align nat.bit Nat.bit

lemma bit0_val (n : Nat) : bit0 n = 2 * n :=
  calc
    n + n = 0 + n + n := by rw [Nat.zero_add]
    _ = n * 2 := rfl
    _ = 2 * n := Nat.mul_comm _ _
#align nat.bit0_val Nat.bit0_val

lemma bit1_val (n : Nat) : bit1 n = 2 * n + 1 := congr_arg succ (bit0_val _)
#align nat.bit1_val Nat.bit1_val

lemma bit_val (b n) : bit b n = 2 * n + cond b 1 0 := by
  cases b
  · apply bit0_val
  · apply bit1_val
#align nat.bit_val Nat.bit_val

lemma bit_decomp (n : Nat) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (Nat.add_comm _ _).trans <| bodd_add_div2 _
#align nat.bit_decomp Nat.bit_decomp

/-- For a predicate `C : Nat → Sort*`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for any given natural number. -/
def bitCasesOn {C : Nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := bit_decomp n ▸ h _ _
#align nat.bit_cases_on Nat.bitCasesOn

lemma bit_zero : bit false 0 = 0 :=
  rfl
#align nat.bit_zero Nat.bit_zero

/-- `shiftLeft' b m n` performs a left shift of `m` `n` times
 and adds the bit `b` as the least significant bit each time.
 Returns the corresponding natural number-/
def shiftLeft' (b : Bool) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => bit b (shiftLeft' b m n)
#align nat.shiftl' Nat.shiftLeft'

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

/-- `ldiff a b` performs bitwise set difference. For each corresponding
  pair of bits taken as booleans, say `aᵢ` and `bᵢ`, it applies the
  boolean operation `aᵢ ∧ ¬bᵢ` to obtain the `iᵗʰ` bit of the result. -/
def ldiff : ℕ → ℕ → ℕ :=
  bitwise fun a b => a && not b
#align nat.ldiff Nat.ldiff

@[simp]
lemma binaryRec_zero {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) :
    binaryRec z f 0 = z := by
  rw [binaryRec]
  rfl
#align nat.binary_rec_zero Nat.binaryRec_zero

/-! bitwise ops -/

lemma bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val]
  simp only [Nat.mul_comm, Nat.add_comm, bodd_add, bodd_mul, bodd_succ, bodd_zero, Bool.not_false,
    Bool.not_true, Bool.and_false, Bool.xor_false]
  cases b <;> cases bodd n <;> rfl
#align nat.bodd_bit Nat.bodd_bit

lemma div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add]
  <;> cases b
  <;> decide
#align nat.div2_bit Nat.div2_bit

lemma shiftLeft'_add (b m n) : ∀ k, shiftLeft' b m (n + k) = shiftLeft' b (shiftLeft' b m n) k
  | 0 => rfl
  | k + 1 => congr_arg (bit b) (shiftLeft'_add b m n k)
#align nat.shiftl'_add Nat.shiftLeft'_add

lemma shiftLeft'_sub (b m) : ∀ {n k}, k ≤ n → shiftLeft' b m (n - k) = (shiftLeft' b m n) >>> k
  | n, 0, _ => rfl
  | n + 1, k + 1, h => by
    rw [succ_sub_succ_eq_sub, shiftLeft', Nat.add_comm, shiftRight_add]
    simp only [shiftLeft'_sub, Nat.le_of_succ_le_succ h, shiftRight_succ, shiftRight_zero]
    simp [← div2_val, div2_bit]
#align nat.shiftl'_sub Nat.shiftLeft'_sub

lemma shiftLeft_sub : ∀ (m : Nat) {n k}, k ≤ n → m <<< (n - k) = (m <<< n) >>> k :=
  fun _ _ _ hk => by simp only [← shiftLeft'_false, shiftLeft'_sub false _ hk]

-- Not a `simp` lemma, as later `simp` will be able to prove this.
lemma testBit_bit_zero (b n) : testBit (bit b n) 0 = b := by
  rw [testBit, bit]
  cases b
  · simp [bit0, ← Nat.mul_two]
  · simp [bit0, bit1, ← Nat.mul_two]

#align nat.test_bit_zero Nat.testBit_zero

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
#align nat.test_bit_succ Nat.testBit_succ

lemma binaryRec_eq {C : Nat → Sort u} {z : C 0} {f : ∀ b n, C n → C (bit b n)}
    (h : f false 0 z = z) (b n) : binaryRec z f (bit b n) = f b n (binaryRec z f n) := by
  rw [binaryRec]
  split_ifs with h'
  · generalize binaryRec z f (bit b n) = e
    revert e
    have bf := bodd_bit b n
    have n0 := div2_bit b n
    rw [h'] at bf n0
    simp only [bodd_zero, div2_zero] at bf n0
    subst bf n0
    rw [binaryRec_zero]
    intros
    rw [h, eq_mpr_eq_cast, cast_eq]
  · simp only; generalize_proofs h
    revert h
    rw [bodd_bit, div2_bit]
    intros; simp only [eq_mpr_eq_cast, cast_eq]
#align nat.binary_rec_eq Nat.binaryRec_eq
#noalign nat.bitwise_bit_aux

/-! ### `boddDiv2_eq` and `bodd` -/


@[simp]
theorem boddDiv2_eq (n : ℕ) : boddDiv2 n = (bodd n, div2 n) := rfl
#align nat.bodd_div2_eq Nat.boddDiv2_eq

@[simp]
theorem bodd_bit0 (n) : bodd (bit0 n) = false :=
  bodd_bit false n
#align nat.bodd_bit0 Nat.bodd_bit0

@[simp]
theorem bodd_bit1 (n) : bodd (bit1 n) = true :=
  bodd_bit true n
#align nat.bodd_bit1 Nat.bodd_bit1

@[simp]
theorem div2_bit0 (n) : div2 (bit0 n) = n :=
  div2_bit false n
#align nat.div2_bit0 Nat.div2_bit0

@[simp]
theorem div2_bit1 (n) : div2 (bit1 n) = n :=
  div2_bit true n
#align nat.div2_bit1 Nat.div2_bit1

/-! ### `bit0` and `bit1` -/

-- There is no need to prove `bit0_eq_zero : bit0 n = 0 ↔ n = 0`
-- as this is true for any `[Semiring R] [NoZeroDivisors R] [CharZero R]`
-- However the lemmas `bit0_eq_bit0`, `bit1_eq_bit1`, `bit1_eq_one`, `one_eq_bit1`
-- need `[Ring R] [NoZeroDivisors R] [CharZero R]` in general,
-- so we prove `ℕ` specialized versions here.
@[simp]
theorem bit0_eq_bit0 {m n : ℕ} : bit0 m = bit0 n ↔ m = n :=
  ⟨Nat.bit0_inj, fun h => by subst h; rfl⟩
#align nat.bit0_eq_bit0 Nat.bit0_eq_bit0

@[simp]
theorem bit1_eq_bit1 {m n : ℕ} : bit1 m = bit1 n ↔ m = n :=
  ⟨Nat.bit1_inj, fun h => by subst h; rfl⟩
#align nat.bit1_eq_bit1 Nat.bit1_eq_bit1

@[simp]
theorem bit1_eq_one {n : ℕ} : bit1 n = 1 ↔ n = 0 :=
  ⟨@Nat.bit1_inj n 0, fun h => by subst h; rfl⟩
#align nat.bit1_eq_one Nat.bit1_eq_one

@[simp]
theorem one_eq_bit1 {n : ℕ} : 1 = bit1 n ↔ n = 0 :=
  ⟨fun h => (@Nat.bit1_inj 0 n h).symm, fun h => by subst h; rfl⟩
#align nat.one_eq_bit1 Nat.one_eq_bit1

theorem bit_add : ∀ (b : Bool) (n m : ℕ), bit b (n + m) = bit false n + bit b m
  | true, _, _ => (congr_arg (· + 1) <| add_add_add_comm _ _ _ _ : _).trans (add_assoc _ _ _)
  | false, _, _ => add_add_add_comm _ _ _ _
#align nat.bit_add Nat.bit_add

theorem bit_add' : ∀ (b : Bool) (n m : ℕ), bit b (n + m) = bit b n + bit false m
  | true, _, _ => (congr_arg (· + 1) <| add_add_add_comm _ _ _ _ : _).trans (add_right_comm _ _ _)
  | false, _, _ => add_add_add_comm _ _ _ _
#align nat.bit_add' Nat.bit_add'

theorem bit_ne_zero (b) {n} (h : n ≠ 0) : bit b n ≠ 0 := by
  cases b <;> [exact Nat.bit0_ne_zero h; exact Nat.bit1_ne_zero _]
#align nat.bit_ne_zero Nat.bit_ne_zero

theorem bit0_mod_two : bit0 n % 2 = 0 := by
  rw [Nat.mod_two_of_bodd]
  simp
#align nat.bit0_mod_two Nat.bit0_mod_two

theorem bit1_mod_two : bit1 n % 2 = 1 := by
  rw [Nat.mod_two_of_bodd]
  simp
#align nat.bit1_mod_two Nat.bit1_mod_two

theorem pos_of_bit0_pos {n : ℕ} (h : 0 < bit0 n) : 0 < n := by
  cases n
  · cases h
  · apply succ_pos
#align nat.pos_of_bit0_pos Nat.pos_of_bit0_pos

@[simp]
theorem bitCasesOn_bit {C : ℕ → Sort u} (H : ∀ b n, C (bit b n)) (b : Bool) (n : ℕ) :
    bitCasesOn (bit b n) H = H b n :=
  eq_of_heq <| (eq_rec_heq _ _).trans <| by rw [bodd_bit, div2_bit]
#align nat.bit_cases_on_bit Nat.bitCasesOn_bit

@[simp]
theorem bitCasesOn_bit0 {C : ℕ → Sort u} (H : ∀ b n, C (bit b n)) (n : ℕ) :
    bitCasesOn (bit0 n) H = H false n :=
  bitCasesOn_bit H false n
#align nat.bit_cases_on_bit0 Nat.bitCasesOn_bit0

@[simp]
theorem bitCasesOn_bit1 {C : ℕ → Sort u} (H : ∀ b n, C (bit b n)) (n : ℕ) :
    bitCasesOn (bit1 n) H = H true n :=
  bitCasesOn_bit H true n
#align nat.bit_cases_on_bit1 Nat.bitCasesOn_bit1

theorem bit_cases_on_injective {C : ℕ → Sort u} :
    Function.Injective fun H : ∀ b n, C (bit b n) => fun n => bitCasesOn n H := by
  intro H₁ H₂ h
  ext b n
  simpa only [bitCasesOn_bit] using congr_fun h (bit b n)
#align nat.bit_cases_on_injective Nat.bit_cases_on_injective

@[simp]
theorem bit_cases_on_inj {C : ℕ → Sort u} (H₁ H₂ : ∀ b n, C (bit b n)) :
    ((fun n => bitCasesOn n H₁) = fun n => bitCasesOn n H₂) ↔ H₁ = H₂ :=
  bit_cases_on_injective.eq_iff
#align nat.bit_cases_on_inj Nat.bit_cases_on_inj

protected theorem bit0_eq_zero {n : ℕ} : bit0 n = 0 ↔ n = 0 :=
  ⟨Nat.eq_zero_of_add_eq_zero_left, fun h => by simp [h]⟩
#align nat.bit0_eq_zero Nat.bit0_eq_zero

theorem bit_eq_zero_iff {n : ℕ} {b : Bool} : bit b n = 0 ↔ n = 0 ∧ b = false := by
  constructor
  · cases b <;> simp [Nat.bit, Nat.bit0_eq_zero, Nat.bit1_ne_zero]
  · rintro ⟨rfl, rfl⟩
    rfl
#align nat.bit_eq_zero_iff Nat.bit_eq_zero_iff

protected lemma bit0_le (h : n ≤ m) : bit0 n ≤ bit0 m :=
  add_le_add h h
#align nat.bit0_le Nat.bit0_le

protected lemma bit1_le {n m : ℕ} (h : n ≤ m) : bit1 n ≤ bit1 m :=
  succ_le_succ (add_le_add h h)
#align nat.bit1_le Nat.bit1_le

lemma bit_le : ∀ (b : Bool) {m n : ℕ}, m ≤ n → bit b m ≤ bit b n
  | true, _, _, h => Nat.bit1_le h
  | false, _, _, h => Nat.bit0_le h
#align nat.bit_le Nat.bit_le

lemma bit0_le_bit : ∀ (b) {m n : ℕ}, m ≤ n → bit0 m ≤ bit b n
  | true, _, _, h => le_of_lt <| Nat.bit0_lt_bit1 h
  | false, _, _, h => Nat.bit0_le h
#align nat.bit0_le_bit Nat.bit0_le_bit

lemma bit_le_bit1 : ∀ (b) {m n : ℕ}, m ≤ n → bit b m ≤ bit1 n
  | false, _, _, h => le_of_lt <| Nat.bit0_lt_bit1 h
  | true, _, _, h => Nat.bit1_le h
#align nat.bit_le_bit1 Nat.bit_le_bit1

lemma bit_lt_bit0 : ∀ (b) {m n : ℕ}, m < n → bit b m < bit0 n
  | true, _, _, h => Nat.bit1_lt_bit0 h
  | false, _, _, h => Nat.bit0_lt h
#align nat.bit_lt_bit0 Nat.bit_lt_bit0

protected lemma bit0_lt_bit0 : bit0 m < bit0 n ↔ m < n := by unfold bit0; omega

lemma bit_lt_bit (a b) (h : m < n) : bit a m < bit b n :=
  lt_of_lt_of_le (bit_lt_bit0 _ h) (bit0_le_bit _ (le_refl _))
#align nat.bit_lt_bit Nat.bit_lt_bit

@[simp]
lemma bit0_le_bit1_iff : bit0 m ≤ bit1 n ↔ m ≤ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ le_of_lt (Nat.bit0_lt_bit1 h)⟩
  rwa [← Nat.lt_succ_iff, n.bit1_eq_succ_bit0, ← n.bit0_succ_eq, Nat.bit0_lt_bit0, Nat.lt_succ_iff]
    at h
#align nat.bit0_le_bit1_iff Nat.bit0_le_bit1_iff

@[simp]
lemma bit0_lt_bit1_iff : bit0 m < bit1 n ↔ m ≤ n :=
  ⟨fun h => bit0_le_bit1_iff.1 (le_of_lt h), Nat.bit0_lt_bit1⟩
#align nat.bit0_lt_bit1_iff Nat.bit0_lt_bit1_iff

@[simp]
lemma bit1_le_bit0_iff : bit1 m ≤ bit0 n ↔ m < n :=
  ⟨fun h ↦ by rwa [m.bit1_eq_succ_bit0, Nat.succ_le_iff, Nat.bit0_lt_bit0] at h,
     fun h ↦ le_of_lt (Nat.bit1_lt_bit0 h)⟩
#align nat.bit1_le_bit0_iff Nat.bit1_le_bit0_iff

@[simp]
lemma bit1_lt_bit0_iff : bit1 m < bit0 n ↔ m < n :=
  ⟨fun h ↦ bit1_le_bit0_iff.1 (le_of_lt h), Nat.bit1_lt_bit0⟩
#align nat.bit1_lt_bit0_iff Nat.bit1_lt_bit0_iff

-- Porting note: temporarily porting only needed portions
/-
@[simp]
theorem one_le_bit0_iff : 1 ≤ bit0 n ↔ 0 < n := by
  convert bit1_le_bit0_iff
  rfl
#align nat.one_le_bit0_iff Nat.one_le_bit0_iff

@[simp]
theorem one_lt_bit0_iff : 1 < bit0 n ↔ 1 ≤ n := by
  convert bit1_lt_bit0_iff
  rfl
#align nat.one_lt_bit0_iff Nat.one_lt_bit0_iff

@[simp]
theorem bit_le_bit_iff : ∀ {b : Bool}, bit b m ≤ bit b n ↔ m ≤ n
  | false => bit0_le_bit0
  | true => bit1_le_bit1
#align nat.bit_le_bit_iff Nat.bit_le_bit_iff

@[simp]
theorem bit_lt_bit_iff : ∀ {b : Bool}, bit b m < bit b n ↔ m < n
  | false => bit0_lt_bit0
  | true => bit1_lt_bit1
#align nat.bit_lt_bit_iff Nat.bit_lt_bit_iff

@[simp]
theorem bit_le_bit1_iff : ∀ {b : Bool}, bit b m ≤ bit1 n ↔ m ≤ n
  | false => bit0_le_bit1_iff
  | true => bit1_le_bit1
#align nat.bit_le_bit1_iff Nat.bit_le_bit1_iff
-/

/--
The same as `binaryRec_eq`,
but that one unfortunately requires `f` to be the identity when appending `false` to `0`.
Here, we allow you to explicitly say that that case is not happening,
i.e. supplying `n = 0 → b = true`. -/
theorem binaryRec_eq' {C : ℕ → Sort*} {z : C 0} {f : ∀ b n, C n → C (bit b n)} (b n)
    (h : f false 0 z = z ∨ (n = 0 → b = true)) :
    binaryRec z f (bit b n) = f b n (binaryRec z f n) := by
  rw [binaryRec]
  split_ifs with h'
  · rcases bit_eq_zero_iff.mp h' with ⟨rfl, rfl⟩
    rw [binaryRec_zero]
    simp only [imp_false, or_false_iff, eq_self_iff_true, not_true] at h
    exact h.symm
  · dsimp only []
    generalize_proofs e
    revert e
    rw [bodd_bit, div2_bit]
    intros
    rfl
#align nat.binary_rec_eq' Nat.binaryRec_eq'

/-- The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true`-/
@[elab_as_elim]
def binaryRec' {C : ℕ → Sort*} (z : C 0) (f : ∀ b n, (n = 0 → b = true) → C n → C (bit b n)) :
    ∀ n, C n :=
  binaryRec z fun b n ih =>
    if h : n = 0 → b = true then f b n h ih
    else by
      convert z
      rw [bit_eq_zero_iff]
      simpa using h
#align nat.binary_rec' Nat.binaryRec'

/-- The same as `binaryRec`, but special casing both 0 and 1 as base cases -/
@[elab_as_elim]
def binaryRecFromOne {C : ℕ → Sort*} (z₀ : C 0) (z₁ : C 1) (f : ∀ b n, n ≠ 0 → C n → C (bit b n)) :
    ∀ n, C n :=
  binaryRec' z₀ fun b n h ih =>
    if h' : n = 0 then by
      rw [h', h h']
      exact z₁
    else f b n h' ih
#align nat.binary_rec_from_one Nat.binaryRecFromOne

@[simp]
theorem zero_bits : bits 0 = [] := by simp [Nat.bits]
#align nat.zero_bits Nat.zero_bits

@[simp]
theorem bits_append_bit (n : ℕ) (b : Bool) (hn : n = 0 → b = true) :
    (bit b n).bits = b :: n.bits := by
  rw [Nat.bits, binaryRec_eq']
  simpa
#align nat.bits_append_bit Nat.bits_append_bit

@[simp]
theorem bit0_bits (n : ℕ) (hn : n ≠ 0) : (bit0 n).bits = false :: n.bits :=
  bits_append_bit n false fun hn' => absurd hn' hn
#align nat.bit0_bits Nat.bit0_bits

@[simp]
theorem bit1_bits (n : ℕ) : (bit1 n).bits = true :: n.bits :=
  bits_append_bit n true fun _ => rfl
#align nat.bit1_bits Nat.bit1_bits

@[simp]
theorem one_bits : Nat.bits 1 = [true] := by
  convert bit1_bits 0
#align nat.one_bits Nat.one_bits

-- TODO Find somewhere this can live.
-- example : bits 3423 = [true, true, true, true, true, false, true, false, true, false, true, true]
-- := by norm_num

theorem bodd_eq_bits_head (n : ℕ) : n.bodd = n.bits.headI := by
  induction' n using Nat.binaryRec' with b n h _; · simp
  simp [bodd_bit, bits_append_bit _ _ h]
#align nat.bodd_eq_bits_head Nat.bodd_eq_bits_head

theorem div2_bits_eq_tail (n : ℕ) : n.div2.bits = n.bits.tail := by
  induction' n using Nat.binaryRec' with b n h _; · simp
  simp [div2_bit, bits_append_bit _ _ h]
#align nat.div2_bits_eq_tail Nat.div2_bits_eq_tail

end Nat

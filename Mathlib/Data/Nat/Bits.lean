/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathlib.Init.Data.Nat.Bitwise
import Mathlib.Init.Data.List.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Convert

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

-- As this file is all about `bit0` and `bit1`,
-- we turn off the deprecated linter for the whole file.
set_option linter.deprecated false

namespace Nat
universe u
variable {m n : ℕ}

/-! ### `boddDiv2_eq` and `bodd` -/


@[simp]
theorem boddDiv2_eq (n : ℕ) : boddDiv2 n = (bodd n, div2 n) := by
  unfold bodd div2; cases boddDiv2 n; rfl
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
  | true => bit1_add
  | false => bit0_add
#align nat.bit_add Nat.bit_add

theorem bit_add' : ∀ (b : Bool) (n m : ℕ), bit b (n + m) = bit b n + bit false m
  | true => bit1_add'
  | false => bit0_add
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

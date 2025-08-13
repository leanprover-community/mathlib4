/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Alex Keizer
-/
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bits
import Mathlib.Order.Basic
import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Common

/-!
# Bitwise operations on natural numbers

In the first half of this file, we provide theorems for reasoning about natural numbers from their
bitwise properties. In the second half of this file, we show properties of the bitwise operations
`lor`, `land` and `xor`, which are defined in core.

## Main results
* `eq_of_testBit_eq`: two natural numbers are equal if they have equal bits at every position.
* `exists_most_significant_bit`: if `n ≠ 0`, then there is some position `i` that contains the most
  significant `1`-bit of `n`.
* `lt_of_testBit`: if `n` and `m` are numbers and `i` is a position such that the `i`-th bit of
  of `n` is zero, the `i`-th bit of `m` is one, and all more significant bits are equal, then
  `n < m`.

## Future work

There is another way to express bitwise properties of natural number: `digits 2`. The two ways
should be connected.

## Keywords

bitwise, and, or, xor
-/

open Function

namespace Nat

section
variable {f : Bool → Bool → Bool}

@[simp]
lemma bitwise_zero_left (m : Nat) : bitwise f 0 m = if f false true then m else 0 := by
  simp [bitwise]

@[simp]
lemma bitwise_zero_right (n : Nat) : bitwise f n 0 = if f true false then n else 0 := by
  unfold bitwise
  simp only [ite_self, Nat.zero_div, ite_true, ite_eq_right_iff]
  rintro ⟨⟩
  split_ifs <;> rfl

lemma bitwise_zero : bitwise f 0 0 = 0 := by
  simp only [bitwise_zero_right, ite_self]

lemma bitwise_of_ne_zero {n m : Nat} (hn : n ≠ 0) (hm : m ≠ 0) :
    bitwise f n m = bit (f (bodd n) (bodd m)) (bitwise f (n / 2) (m / 2)) := by
  conv_lhs => unfold bitwise
  have mod_two_iff_bod x : (x % 2 = 1 : Bool) = bodd x := by
    simp only [mod_two_of_bodd]; cases bodd x <;> rfl
  simp only [hn, hm, mod_two_iff_bod, ite_false, bit, two_mul, Bool.cond_eq_ite]

theorem binaryRec_of_ne_zero {C : Nat → Sort*} (z : C 0) (f : ∀ b n, C n → C (bit b n)) {n}
    (h : n ≠ 0) :
    binaryRec z f n = bit_decomp n ▸ f (bodd n) (div2 n) (binaryRec z f (div2 n)) := by
  cases n using bitCasesOn with
  | h b n =>
    rw [binaryRec_eq _ _ (by right; simpa [bit_eq_zero_iff] using h)]
    generalize_proofs h; revert h
    rw [bodd_bit, div2_bit]
    simp

@[simp]
lemma bitwise_bit {f : Bool → Bool → Bool} (h : f false false = false := by rfl) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  conv_lhs => unfold bitwise
  simp only [bit, Bool.cond_eq_ite]
  have h4 x : (x + x + 1) / 2 = x := by rw [← two_mul, add_comm]; simp [add_mul_div_left]
  cases a <;> cases b <;> simp <;> split_ifs
    <;> simp_all +decide [two_mul]

lemma bit_mod_two_eq_zero_iff (a x) :
    bit a x % 2 = 0 ↔ !a := by
  simp

lemma bit_mod_two_eq_one_iff (a x) :
    bit a x % 2 = 1 ↔ a := by
  simp

@[simp]
theorem lor_bit : ∀ a m b n, bit a m ||| bit b n = bit (a || b) (m ||| n) :=
  bitwise_bit

@[simp]
theorem land_bit : ∀ a m b n, bit a m &&& bit b n = bit (a && b) (m &&& n) :=
  bitwise_bit

@[simp]
theorem ldiff_bit : ∀ a m b n, ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) :=
  bitwise_bit

@[simp]
theorem xor_bit : ∀ a m b n, bit a m ^^^ bit b n = bit (bne a b) (m ^^^ n) :=
  bitwise_bit

attribute [simp] Nat.testBit_bitwise

theorem testBit_lor : ∀ m n k, testBit (m ||| n) k = (testBit m k || testBit n k) :=
  testBit_bitwise rfl

theorem testBit_land : ∀ m n k, testBit (m &&& n) k = (testBit m k && testBit n k) :=
  testBit_bitwise rfl

@[simp]
theorem testBit_ldiff : ∀ m n k, testBit (ldiff m n) k = (testBit m k && not (testBit n k)) :=
  testBit_bitwise rfl

attribute [simp] testBit_xor

end

@[simp]
theorem bit_false : bit false = (2 * ·) :=
  rfl

@[simp]
theorem bit_true : bit true = (2 * · + 1) :=
  rfl

@[simp]
theorem bit_false_apply (n) : bit false n = (2 * n) :=
  rfl

@[simp]
theorem bit_true_apply (n) : bit true n = (2 * n + 1) :=
  rfl

theorem bit_ne_zero_iff {n : ℕ} {b : Bool} : n.bit b ≠ 0 ↔ n = 0 → b = true := by
  simp

/-- An alternative for `bitwise_bit` which replaces the `f false false = false` assumption
with assumptions that neither `bit a m` nor `bit b n` are `0`
(albeit, phrased as the implications `m = 0 → a = true` and `n = 0 → b = true`) -/
lemma bitwise_bit' {f : Bool → Bool → Bool} (a : Bool) (m : Nat) (b : Bool) (n : Nat)
    (ham : m = 0 → a = true) (hbn : n = 0 → b = true) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  conv_lhs => unfold bitwise
  rw [← bit_ne_zero_iff] at ham hbn
  simp only [ham, hbn, bit_mod_two_eq_one_iff, Bool.decide_coe, ← div2_val, div2_bit,
    ite_false]
  conv_rhs => simp only [bit, two_mul, Bool.cond_eq_ite]

lemma bitwise_eq_binaryRec (f : Bool → Bool → Bool) :
    bitwise f =
    binaryRec (fun n => cond (f false true) n 0) fun a m Ia =>
      binaryRec (cond (f true false) (bit a m) 0) fun b n _ => bit (f a b) (Ia n) := by
  funext x y
  induction x using binaryRec' generalizing y with
  | z => simp only [bitwise_zero_left, binaryRec_zero, Bool.cond_eq_ite]
  | f xb x hxb ih =>
    rw [← bit_ne_zero_iff] at hxb
    simp_rw [binaryRec_of_ne_zero _ _ hxb, bodd_bit, div2_bit, eq_rec_constant]
    induction y using binaryRec' with
    | z => simp only [bitwise_zero_right, binaryRec_zero, Bool.cond_eq_ite]
    | f yb y hyb =>
      rw [← bit_ne_zero_iff] at hyb
      simp_rw [binaryRec_of_ne_zero _ _ hyb, bitwise_of_ne_zero hxb hyb, bodd_bit, ← div2_val,
        div2_bit, eq_rec_constant, ih]

theorem zero_of_testBit_eq_false {n : ℕ} (h : ∀ i, testBit n i = false) : n = 0 := by
  induction n using Nat.binaryRec with | z => rfl | f b n hn => ?_
  have : b = false := by simpa using h 0
  rw [this, bit_false, hn fun i => by rw [← h (i + 1), testBit_bit_succ]]

theorem testBit_eq_false_of_lt {n i} (h : n < 2 ^ i) : n.testBit i = false := by
  simp [testBit, shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

/-- The ith bit is the ith element of `n.bits`. -/
theorem testBit_eq_inth (n i : ℕ) : n.testBit i = n.bits.getI i := by
  induction i generalizing n with
  | zero =>
    simp only [testBit, shiftRight_zero, one_and_eq_mod_two, mod_two_of_bodd,
      bodd_eq_bits_head, List.getI_zero_eq_headI]
    cases List.headI (bits n) <;> rfl
  | succ i ih =>
    conv_lhs => rw [← bit_decomp n]
    rw [testBit_bit_succ, ih n.div2, div2_bits_eq_tail]
    cases n.bits <;> simp

theorem exists_most_significant_bit {n : ℕ} (h : n ≠ 0) :
    ∃ i, testBit n i = true ∧ ∀ j, i < j → testBit n j = false := by
  induction n using Nat.binaryRec with | z => exact False.elim (h rfl) | f b n hn => ?_
  by_cases h' : n = 0
  · subst h'
    rw [show b = true by
        revert h
        cases b <;> simp]
    refine ⟨0, ⟨by rw [testBit_bit_zero], fun j hj => ?_⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (ne_of_gt hj)
    rw [testBit_bit_succ, zero_testBit]
  · obtain ⟨k, ⟨hk, hk'⟩⟩ := hn h'
    refine ⟨k + 1, ⟨by rw [testBit_bit_succ, hk], fun j hj => ?_⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (show j ≠ 0 by intro x; subst x; simp at hj)
    exact (testBit_bit_succ _ _ _).trans (hk' _ (lt_of_succ_lt_succ hj))

theorem lt_of_testBit {n m : ℕ} (i : ℕ) (hn : testBit n i = false) (hm : testBit m i = true)
    (hnm : ∀ j, i < j → testBit n j = testBit m j) : n < m := by
  induction n using Nat.binaryRec generalizing i m with
  | z =>
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp at hm
  | f b n hn' =>
    induction m using Nat.binaryRec generalizing i with
    | z => exact False.elim (Bool.false_ne_true ((zero_testBit i).symm.trans hm))
    | f b' m hm' =>
      by_cases hi : i = 0
      · subst hi
        simp only [testBit_bit_zero] at hn hm
        have : n = m :=
          eq_of_testBit_eq fun i => by convert hnm (i + 1) (Nat.zero_lt_succ _) using 1
          <;> rw [testBit_bit_succ]
        rw [hn, hm, this, bit_false, bit_true]
        exact Nat.lt_succ_self _
      · obtain ⟨i', rfl⟩ := exists_eq_succ_of_ne_zero hi
        simp only [testBit_bit_succ] at hn hm
        have := hn' _ hn hm fun j hj => by
          convert hnm j.succ (succ_lt_succ hj) using 1 <;> rw [testBit_bit_succ]
        exact bit_lt_bit b b' this

theorem bitwise_swap {f : Bool → Bool → Bool} :
    bitwise (Function.swap f) = Function.swap (bitwise f) := by
  funext m n
  simp only [Function.swap]
  induction m using Nat.strongRecOn generalizing n with | ind m ih => ?_
  rcases m with - | m
  <;> rcases n with - | n
  <;> try rw [bitwise_zero_left, bitwise_zero_right]
  · specialize ih ((m+1) / 2) (div_lt_self' ..)
    simp [bitwise_of_ne_zero, ih]

/-- If `f` is a commutative operation on bools such that `f false false = false`, then `bitwise f`
is also commutative. -/
theorem bitwise_comm {f : Bool → Bool → Bool} (hf : ∀ b b', f b b' = f b' b) (n m : ℕ) :
    bitwise f n m = bitwise f m n :=
  suffices bitwise f = swap (bitwise f) by conv_lhs => rw [this]
  calc
    bitwise f = bitwise (swap f) := congr_arg _ <| funext fun _ => funext <| hf _
    _ = swap (bitwise f) := bitwise_swap

theorem lor_comm (n m : ℕ) : n ||| m = m ||| n :=
  bitwise_comm Bool.or_comm n m

theorem land_comm (n m : ℕ) : n &&& m = m &&& n :=
  bitwise_comm Bool.and_comm n m

lemma and_two_pow (n i : ℕ) : n &&& 2 ^ i = (n.testBit i).toNat * 2 ^ i := by
  refine eq_of_testBit_eq fun j => ?_
  obtain rfl | hij := Decidable.eq_or_ne i j <;> cases h : n.testBit i
  · simp [h]
  · simp [h]
  · simp [testBit_two_pow_of_ne hij]
  · simp [testBit_two_pow_of_ne hij]

lemma two_pow_and (n i : ℕ) : 2 ^ i &&& n = 2 ^ i * (n.testBit i).toNat := by
  rw [mul_comm, land_comm, and_two_pow]

/-- Proving associativity of bitwise operations in general essentially boils down to a huge case
    distinction, so it is shorter to use this tactic instead of proving it in the general case. -/
macro "bitwise_assoc_tac" : tactic => set_option hygiene false in `(tactic| (
  induction n using Nat.binaryRec generalizing m k with | z => simp | f b n hn => ?_
  induction m using Nat.binaryRec with | z => simp | f b' m hm => ?_
  induction k using Nat.binaryRec <;>
    simp [hn, Bool.or_assoc, Bool.and_assoc, Bool.bne_eq_xor]))

theorem land_assoc (n m k : ℕ) : (n &&& m) &&& k = n &&& (m &&& k) := by bitwise_assoc_tac

theorem lor_assoc (n m k : ℕ) : (n ||| m) ||| k = n ||| (m ||| k) := by bitwise_assoc_tac

-- These lemmas match `mul_inv_cancel_right` and `mul_inv_cancel_left`.
theorem xor_cancel_right (n m : ℕ) : (m ^^^ n) ^^^ n = m := by
  rw [Nat.xor_assoc, Nat.xor_self, xor_zero]

theorem xor_cancel_left (n m : ℕ) : n ^^^ (n ^^^ m) = m := by
  rw [← Nat.xor_assoc, Nat.xor_self, zero_xor]

theorem xor_right_injective {n : ℕ} : Function.Injective (HXor.hXor n : ℕ → ℕ) := fun m m' h => by
  rw [← xor_cancel_left n m, ← xor_cancel_left n m', h]

theorem xor_left_injective {n : ℕ} : Function.Injective fun m => m ^^^ n :=
  fun m m' (h : m ^^^ n = m' ^^^ n) => by
  rw [← xor_cancel_right n m, ← xor_cancel_right n m', h]

@[simp]
theorem xor_right_inj {n m m' : ℕ} : n ^^^ m = n ^^^ m' ↔ m = m' :=
  xor_right_injective.eq_iff

@[simp]
theorem xor_left_inj {n m m' : ℕ} : m ^^^ n = m' ^^^ n ↔ m = m' :=
  xor_left_injective.eq_iff

@[simp]
theorem xor_eq_zero {n m : ℕ} : n ^^^ m = 0 ↔ n = m := by
  rw [← Nat.xor_self n, xor_right_inj, eq_comm]

theorem xor_ne_zero {n m : ℕ} : n ^^^ m ≠ 0 ↔ n ≠ m :=
  xor_eq_zero.not

theorem xor_trichotomy {a b c : ℕ} (h : a ^^^ b ^^^ c ≠ 0) :
    b ^^^ c < a ∨ c ^^^ a < b ∨ a ^^^ b < c := by
  set v := a ^^^ b ^^^ c with hv
  -- The xor of any two of `a`, `b`, `c` is the xor of `v` and the third.
  have hab : a ^^^ b = c ^^^ v := by
    rw [Nat.xor_comm c, xor_cancel_right]
  have hbc : b ^^^ c = a ^^^ v := by
    rw [← Nat.xor_assoc, xor_cancel_left]
  have hca : c ^^^ a = b ^^^ v := by
    rw [hv, Nat.xor_assoc, Nat.xor_comm a, ← Nat.xor_assoc, xor_cancel_left]
  -- If `i` is the position of the most significant bit of `v`, then at least one of `a`, `b`, `c`
  -- has a one bit at position `i`.
  obtain ⟨i, ⟨hi, hi'⟩⟩ := exists_most_significant_bit h
  have : testBit a i ∨ testBit b i ∨ testBit c i := by
    contrapose! hi
    simp_rw [Bool.eq_false_eq_not_eq_true] at hi ⊢
    rw [testBit_xor, testBit_xor, hi.1, hi.2.1, hi.2.2]
    rfl
  -- If, say, `a` has a one bit at position `i`, then `a xor v` has a zero bit at position `i`, but
  -- the same bits as `a` in positions greater than `j`, so `a xor v < a`.
  obtain h | h | h := this
  on_goal 1 => left; rw [hbc]
  on_goal 2 => right; left; rw [hca]
  on_goal 3 => right; right; rw [hab]
  all_goals
    refine lt_of_testBit i ?_ h fun j hj => ?_
    · rw [testBit_xor, h, hi]
      rfl
    · simp only [testBit_xor, hi' _ hj, Bool.bne_false]

theorem lt_xor_cases {a b c : ℕ} (h : a < b ^^^ c) : a ^^^ c < b ∨ a ^^^ b < c := by
  obtain ha | hb | hc := xor_trichotomy <| Nat.xor_assoc _ _ _ ▸ xor_ne_zero.2 h.ne
  exacts [(h.asymm ha).elim, Or.inl <| Nat.xor_comm _ _ ▸ hb, Or.inr hc]

@[simp]
theorem xor_mod_two_eq {m n : ℕ} : (m ^^^ n) % 2 = (m + n) % 2 := by
  by_cases h : (m + n) % 2 = 0
  · simp only [h, mod_two_eq_zero_iff_testBit_zero, testBit_zero, xor_mod_two_eq_one, decide_not,
      Bool.decide_iff_dist, Bool.not_eq_false', beq_iff_eq, decide_eq_decide]
    omega
  · simp only [mod_two_ne_zero] at h
    simp only [h, xor_mod_two_eq_one]
    omega

@[simp]
theorem even_xor {m n : ℕ} : Even (m ^^^ n) ↔ (Even m ↔ Even n) := by
  simp only [even_iff, xor_mod_two_eq]
  omega

@[simp] theorem bit_lt_two_pow_succ_iff {b x n} : bit b x < 2 ^ (n + 1) ↔ x < 2 ^ n := by
  cases b <;> simp <;> omega

lemma shiftLeft_lt {x n m : ℕ} (h : x < 2 ^ n) : x <<< m < 2 ^ (n + m) := by
  simp only [Nat.pow_add, shiftLeft_eq, Nat.mul_lt_mul_right (Nat.two_pow_pos _), h]

/-- Note that the LHS is the expression used within `Std.BitVec.append`, hence the name. -/
lemma append_lt {x y n m} (hx : x < 2 ^ n) (hy : y < 2 ^ m) : y <<< n ||| x < 2 ^ (n + m) := by
  apply bitwise_lt_two_pow
  · rw [add_comm]; apply shiftLeft_lt hy
  · apply lt_of_lt_of_le hx <| Nat.pow_le_pow_right (le_succ _) (le_add_right _ _)

end Nat

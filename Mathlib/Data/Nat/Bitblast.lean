/-
Copyright (c) 2023 Harun Khan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Abdalrhman M Mohamed
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Bool.Basic

/-!
# Bitblasting for Bitvectors

A bitvector is defined in BitVec as a natural number modulo 2^w (i.e. `Fin` of length 2^w). 
Many operators on bitvectors are defined as the corresponding operations on `Fin`. 
For example, less than is defined as the less than of the underlying naturals. Similarly, addition 
is defined as addition of the underlying naturals modulo 2^w (i.e. `Fin.add`). 
The bitvector operations were defined from the 
[`QF_BV` logic](https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV) of SMT-LIBv2.

In this file, we define bitblast versions for these operations and show that they correspond 
to bitvector operations in BitVec.

## Main Results

* `mod_two_pow_succ` expresses a number modulo `2^(i+1)` in terms of its value modulo 2^i. 
This allows for induction on the most significant bit in a very clean way. This will be used 
extensively in the proofs of `bitadd` and `bitmul` where induction on the most significant bit 
is easier.  
* `of_lt_of_testBit`: if `x < y` then there exists a bit `i` such that 
`x.testBit i = false` and `y.testBit i = true`.
* `toNat_testBit`: the `testBit` of `toNat` is the function at that index. 
This used extensively in the proof of each of the bitblast operations.
* `testBit_add`: the `testBit` of the sum of two bitvectors is equal to the bitwise
xor of the `testBit` of the two bitvectors and the `testBit` of their carry.

## Notation
* `^^`: boolean `xor`

## References
See [`QF_BV` logic](https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV) for more operations.
-/

infix:30 " ^^ " => xor

namespace Nat

lemma bit_toNat (b : Bool) : bit b 0 = b.toNat := by cases' b <;> simp

theorem two_pow_pos (n : Nat) : 0 < 2^n := Nat.pos_pow_of_pos _ (by decide)

theorem two_pow_succ (n : Nat) : 2^(n + 1) = 2^n + 2^n := by simp [pow_succ, mul_two] 

lemma lt_succ_two_pow (h: b ≤ 1) (hm : m < 2^i) : 2^i * b + m < 2^(i + 1) := by 
  rw [two_pow_succ]
  exact add_lt_add_of_le_of_lt (mul_le_of_le_one_right' h) hm

lemma toNat_le_one (b: Bool) : b.toNat ≤ 1 := by cases' b <;> simp

@[simp] lemma bif_eq_toNat : cond b 1 0 = b.toNat := by simp [cond, Bool.toNat]

lemma shiftr_eq_testBit : Nat.shiftr n i % 2 = (n.testBit i).toNat := by 
  simp [Nat.testBit, Nat.mod_two_of_bodd]

lemma div_add_mod_two_pow (m n : Nat) : n = 2^m * Nat.shiftr n m + n % (2^m):= by 
  simp_rw [Nat.shiftr_eq_div_pow, Nat.div_add_mod]

/-- Useful for induction on the most significant bit-/
theorem mod_two_pow_succ (n i : Nat) : n % 2^(i+1) = 2^i * (Nat.testBit n i).toNat + n % (2^i):= by 
  have h1 := div_add_mod_two_pow i n
  have h3 := div_add_mod (Nat.shiftr n i) 2
  rw [← h3, mul_add, ← mul_assoc, ← pow_succ, shiftr_eq_testBit] at h1
  have := lt_succ_two_pow (toNat_le_one (n.testBit i)) (mod_lt n (NeZero.pos (2^i)))
  simp [(Nat.div_mod_unique (two_pow_pos (i + 1))).mpr ⟨add_rotate _ _ (n % (2^i)) ▸ h1.symm, this⟩]

lemma bit_lt (h: bit b n < bit b' m) : n < m ∨ (n = m ∧ b = false ∧ b'= true) := by 
  cases' b <;> cases' b' <;> revert h
  <;> simp [le_iff_lt_or_eq]

/-- Bitblast unsigned less than-/
def bitult (n m w : Nat) := loop n m (w - 1) 
where
  loop (n m : Nat) : Nat →  Prop
    | 0     => ¬ n.testBit 0  ∧ m.testBit 0
    | i + 1 => (¬ n.testBit (i + 1) ∧ m.testBit (i + 1)) 
               ∨ (¬ (n.testBit (i + 1) ∧ ¬ m.testBit (i + 1)) ∧ loop n m i)

theorem testBit_of_lt (h: n < m) : ∃ i, Nat.testBit n i = false ∧ 
  Nat.testBit m i = true ∧ ∀ j, i < j → Nat.testBit m j = Nat.testBit n j := by
  induction' n using Nat.binaryRec with b n ih generalizing m
  · have ⟨i, _, _⟩ := exists_most_significant_bit (ne_of_lt h).symm
    use i; simpa [*]
  · rw [← bit_decomp m] at h ⊢
    cases' bit_lt h with h3 h3
    · have ⟨i, iH⟩ := ih h3
      use Nat.succ i; simp only [testBit_succ]
      exact ⟨iH.1, iH.2.1, by 
             intros j hj; cases' j with j
             · simp at hj
             · simp [testBit_succ, iH.2.2 j (by linarith)]⟩
    · use 0; simp only [testBit_zero]
      exact ⟨ h3.2.1, h3.2.2, by intros j hj
                                 have ⟨j', hj⟩ := exists_eq_add_of_le' hj
                                 simp[hj, testBit_succ, h3.1]⟩ 

theorem testBit_false_of_lt (h: n < 2^i) (h1: i ≤ j) : n.testBit j = false:= by 
  simp [testBit, shiftr_eq_div_pow, 
        Nat.div_eq_zero (lt_of_lt_of_le h (pow_le_pow_of_le_right (by decide) h1))]

theorem lt_of_testBit_true (h: n.testBit i = true) (hn : n < 2^w) : i < w := by
  by_contra'; simp [testBit_false_of_lt hn this] at h

theorem bitult_of_ult (hm: m < 2^w) (h1: n < m) : bitult n m w := by
  have ⟨i, hi1, hi2, hi3⟩ := testBit_of_lt h1
  suffices goal: ∀ j, i + 1 ≤ j → bitult n m j from goal w (lt_of_testBit_true hi2 hm)
  apply le_induction
  · cases' i <;> simp [bitult, bitult.loop, hi1, hi2]
  · intros j hj ih
    have ⟨j', hj'⟩ := exists_eq_add_of_le' (le_of_add_le_right hj)
    simp only [bitult, bitult.loop, hj', succ_sub_one j'] at ih ⊢ 
    simp [ih, hi3 (j' + 1) (by linarith)]

theorem bodd_eq_iff : bodd n = bodd m ↔ n % 2 = m % 2 := by
  cases' hn : bodd n <;> cases' hm : bodd m 
  <;> simp [mod_two_of_bodd, hn, hm]

theorem testBit_translate (h: i < w) : Nat.testBit (2^w * b + n) i = Nat.testBit n i := by
  simp only [testBit, shiftr_eq_div_pow, bodd_eq_iff]
  rw [Nat.add_div_of_dvd_right (by simp [Dvd.dvd.mul_right, pow_dvd_pow, le_of_lt h]), add_mod]
  have h1: (2^w / 2^i) % 2 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero]
    use 2^(w - (i + 1))
    rw [Nat.pow_div (by linarith) (by decide), mul_comm, ← pow_succ 2 _, succ_eq_add_one]
    simp [← Nat.sub_add_comm, succ_le_of_lt h]
  simp [mul_comm, Nat.mul_div_assoc b (pow_dvd_pow 2 (le_of_lt h)), mul_mod, h1]

theorem testBit_translate' (h: n < 2^w) : Nat.testBit (2^w * b.toNat + n) w = b:= by
  simp only [Nat.testBit, Nat.shiftr_eq_div_pow]
  rw [Nat.add_div_of_dvd_right (Dvd.intro _ rfl), Nat.div_eq_zero h, add_zero]
  cases' b <;> simp 

@[simp] lemma toNat_true : true.toNat = 1 := rfl

theorem testBit_translate_one (h : i < w) : 
  Nat.testBit (2^w + n) i = Nat.testBit n i := mul_one (2^w) ▸ (testBit_translate h)

theorem testBit_translate_one' (h : n < 2^w) : Nat.testBit (2^w + n) w = true :=
  mul_one (2^w) ▸ toNat_true ▸ (@testBit_translate' n w true h)

@[simp] lemma testBit_bool : testBit b.toNat 0 = b := by cases' b <;> simp

/-- Generic method to create a natural number by tail-recursively appending 
bits. This is an alternative to using `List` altogether.-/
def toNat (f : Nat → Bool) (z : Nat) : Nat → Nat
  | 0 => z.bit (f 0)
  | i + 1 => toNat f (z.bit (f (i + 1))) i

theorem toNat_succ : toNat f z i = 2^(i + 1) * z + toNat f 0 i := by
  induction' i with i ih generalizing z
  · simp [toNat, bit_val]
  · simp only [toNat, @ih (bit (f (i + 1)) 0), @ih (bit (f (i + 1)) z)]
    rw [bit_val, mul_add, ← mul_assoc, ← pow_succ]
    simp [bit_val, add_assoc] 

theorem toNat_lt : toNat f 0 i < 2^(i + 1) := by
  induction' i with i ih
  · simp [toNat, bit_val, lt_succ, toNat_le_one]
  · simp only [toNat]
    rw [toNat_succ]
    cases' (f (i + 1)) <;> simp [ih, two_pow_succ] at * <;> linarith

/-- The `ith` bit of `toNat` is the function at `i`.-/
theorem toNat_testBit (h1: i ≤ j): (toNat f 0 j).testBit i = f i := by
  induction' j with j ih generalizing i
  · simp [nonpos_iff_eq_zero.mp h1, toNat, bit_val]
  · cases' lt_or_eq_of_le h1 with h1 h1
    · rw [← ih (show i ≤ j by linarith), toNat, toNat_succ, testBit_translate h1]
    · rw [h1, toNat, toNat_succ, bit_toNat, testBit_translate' (toNat_lt)]

/-- Carry function for binary addition.-/
def bitcarry (n m : Nat) : Nat → Bool
  | 0     => false
  | i + 1 => (n.testBit i && m.testBit i) || ((n.testBit i ^^ m.testBit i) && bitcarry n m i)

/-- Binary addition-/
@[simp] def bitadd (n m i : Nat) := 
  toNat (λ j => (n.testBit j ^^ m.testBit j) ^^ bitcarry n m j) 0 i

lemma unfold_carry (n m i : Nat) : (bitcarry n m (i + 1)).toNat = 
  ((Nat.testBit n i && Nat.testBit m i) || 
  ((Nat.testBit n i ^^ Nat.testBit m i) && bitcarry n m i)).toNat := by 
  simp [bitcarry]

lemma bitadd_eq_add_base : n % (2^(i + 1)) + m % (2^(i + 1)) = 
  bitadd n m i + 2^(i + 1) * (bitcarry n m (i + 1)).toNat := by
  induction' i with i hi
  · simp only [bitcarry, bitadd, toNat]
    cases' hn: Nat.bodd n  <;> cases' hm: Nat.bodd m
    <;> simp [mod_two_of_bodd, testBit, hn, hm, shiftr]
  · rw [mod_two_pow_succ n, mod_two_pow_succ m]
    rw [add_assoc, add_comm _ (m % 2^(i + 1)), ← add_assoc (n % 2^(i + 1))]
    rw [hi, unfold_carry n m (succ i), two_pow_succ (succ i)]
    cases' hn : Nat.testBit n (i + 1) <;> cases' hm : Nat.testBit m (i + 1) 
    <;> cases' hc : bitcarry n m (i + 1) 
    <;> simp [Bool.toNat, @toNat_succ _ 1 i, two_pow_succ, hn, hm, hc, toNat]
    <;> ring

theorem bitadd_eq_add : bitadd n m i = (n + m) % 2^(i + 1) := by
  rw [Nat.add_mod, bitadd_eq_add_base]
  cases' i with i i
  · cases' h0: Nat.testBit n 0 ^^ (Nat.testBit m 0 ^^ bitcarry n m 0)
    <;> simp [toNat, h0]
  · simp [bitadd, Nat.mod_eq_of_lt toNat_lt]

theorem testBit_add : (n + m).testBit i = ((n.testBit i ^^ m.testBit i) ^^ bitcarry n m i):= by
  have := lt_of_lt_of_le 
          (lt_trans (lt_two_pow (n + m)) (pow_lt_pow_succ (by decide) (n + m))) 
          (pow_le_pow_of_le_right (show 0 < 2 by decide) (@le_add_self _ _ _ i))
  rw [← Nat.mod_eq_of_lt this, ← add_assoc, ← bitadd_eq_add]
  simp [toNat_testBit (show i ≤ i + (n + m) by linarith)]

end Nat
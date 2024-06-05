/-
Copyright (c) 2022 Niels Voss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.Filter.Cofinite

#align_import number_theory.fermat_psp from "leanprover-community/mathlib"@"c0439b4877c24a117bfdd9e32faf62eee9b115eb"

/-!
# Fermat Pseudoprimes

In this file we define Fermat pseudoprimes: composite numbers that pass the Fermat primality test.
A natural number `n` passes the Fermat primality test to base `b` (and is therefore deemed a
"probable prime") if `n` divides `b ^ (n - 1) - 1`. `n` is a Fermat pseudoprime to base `b` if `n`
is a composite number that passes the Fermat primality test to base `b` and is coprime with `b`.

Fermat pseudoprimes can also be seen as composite numbers for which Fermat's little theorem holds
true.

Numbers which are Fermat pseudoprimes to all bases are known as Carmichael numbers (not yet defined
in this file).

## Main Results

The main definitions for this file are

- `Nat.ProbablePrime`: A number `n` is a probable prime to base `b` if it passes the Fermat
  primality test; that is, if `n` divides `b ^ (n - 1) - 1`
- `Nat.FermatPsp`: A number `n` is a pseudoprime to base `b` if it is a probable prime to base `b`,
  is composite, and is coprime with `b` (this last condition is automatically true if `n` divides
  `b ^ (n - 1) - 1`, but some sources include it in the definition).

Note that all composite numbers are pseudoprimes to base 0 and 1, and that the definition of
`Nat.ProbablePrime` in this file implies that all numbers are probable primes to bases 0 and 1, and
that 0 and 1 are probable primes to any base.

The main theorems are
- `Nat.exists_infinite_pseudoprimes`: there are infinite pseudoprimes to any base `b ≥ 1`
-/

namespace Nat

/--
`n` is a probable prime to base `b` if `n` passes the Fermat primality test; that is, `n` divides
`b ^ (n - 1) - 1`.
This definition implies that all numbers are probable primes to base 0 or 1, and that 0 and 1 are
probable primes to any base.
-/
def ProbablePrime (n b : ℕ) : Prop :=
  n ∣ b ^ (n - 1) - 1
#align fermat_psp.probable_prime Nat.ProbablePrime

/--
`n` is a Fermat pseudoprime to base `b` if `n` is a probable prime to base `b` and is composite. By
this definition, all composite natural numbers are pseudoprimes to base 0 and 1. This definition
also permits `n` to be less than `b`, so that 4 is a pseudoprime to base 5, for example.
-/
def FermatPsp (n b : ℕ) : Prop :=
  ProbablePrime n b ∧ ¬n.Prime ∧ 1 < n
#align fermat_psp Nat.FermatPsp

instance decidableProbablePrime (n b : ℕ) : Decidable (ProbablePrime n b) :=
  Nat.decidable_dvd _ _
#align fermat_psp.decidable_probable_prime Nat.decidableProbablePrime

instance decidablePsp (n b : ℕ) : Decidable (FermatPsp n b) :=
  And.decidable
#align fermat_psp.decidable_psp Nat.decidablePsp

/-- If `n` passes the Fermat primality test to base `b`, then `n` is coprime with `b`, assuming that
`n` and `b` are both positive.
-/
theorem coprime_of_probablePrime {n b : ℕ} (h : ProbablePrime n b) (h₁ : 1 ≤ n) (h₂ : 1 ≤ b) :
    Nat.Coprime n b := by
  by_cases h₃ : 2 ≤ n
  · -- To prove that `n` is coprime with `b`, we need to show that for all prime factors of `n`,
    -- we can derive a contradiction if `n` divides `b`.
    apply Nat.coprime_of_dvd
    -- If `k` is a prime number that divides both `n` and `b`, then we know that `n = m * k` and
    -- `b = j * k` for some natural numbers `m` and `j`. We substitute these into the hypothesis.
    rintro k hk ⟨m, rfl⟩ ⟨j, rfl⟩
    -- Because prime numbers do not divide 1, it suffices to show that `k ∣ 1` to prove a
    -- contradiction
    apply Nat.Prime.not_dvd_one hk
    -- Since `n` divides `b ^ (n - 1) - 1`, `k` also divides `b ^ (n - 1) - 1`
    replace h := dvd_of_mul_right_dvd h
    -- Because `k` divides `b ^ (n - 1) - 1`, if we can show that `k` also divides `b ^ (n - 1)`,
    -- then we know `k` divides 1.
    rw [Nat.dvd_add_iff_right h, Nat.sub_add_cancel (Nat.one_le_pow _ _ h₂)]
    -- Since `k` divides `b`, `k` also divides any power of `b` except `b ^ 0`. Therefore, it
    -- suffices to show that `n - 1` isn't zero. However, we know that `n - 1` isn't zero because we
    -- assumed `2 ≤ n` when doing `by_cases`.
    refine dvd_of_mul_right_dvd (dvd_pow_self (k * j) ?_)
    omega
  -- If `n = 1`, then it follows trivially that `n` is coprime with `b`.
  · rw [show n = 1 by omega]
    norm_num
#align fermat_psp.coprime_of_probable_prime Nat.coprime_of_probablePrime

theorem probablePrime_iff_modEq (n : ℕ) {b : ℕ} (h : 1 ≤ b) :
    ProbablePrime n b ↔ b ^ (n - 1) ≡ 1 [MOD n] := by
  have : 1 ≤ b ^ (n - 1) := one_le_pow_of_one_le h (n - 1)
  -- For exact mod_cast
  rw [Nat.ModEq.comm]
  constructor
  · intro h₁
    apply Nat.modEq_of_dvd
    exact mod_cast h₁
  · intro h₁
    exact mod_cast Nat.ModEq.dvd h₁
#align fermat_psp.probable_prime_iff_modeq Nat.probablePrime_iff_modEq

/-- If `n` is a Fermat pseudoprime to base `b`, then `n` is coprime with `b`, assuming that `b` is
positive.

This lemma is a small wrapper based on `coprime_of_probablePrime`
-/
theorem coprime_of_fermatPsp {n b : ℕ} (h : FermatPsp n b) (h₁ : 1 ≤ b) : Nat.Coprime n b := by
  rcases h with ⟨hp, _, hn₂⟩
  exact coprime_of_probablePrime hp (by omega) h₁
#align fermat_psp.coprime_of_fermat_psp Nat.coprime_of_fermatPsp

/-- All composite numbers are Fermat pseudoprimes to base 1.
-/
theorem fermatPsp_base_one {n : ℕ} (h₁ : 1 < n) (h₂ : ¬n.Prime) : FermatPsp n 1 := by
  refine ⟨show n ∣ 1 ^ (n - 1) - 1 from ?_, h₂, h₁⟩
  exact show 0 = 1 ^ (n - 1) - 1 by
    set_option tactic.skipAssignedInstances false in norm_num ▸ dvd_zero n
#align fermat_psp.base_one Nat.fermatPsp_base_one

-- Lemmas that are needed to prove statements in this file, but aren't directly related to Fermat
-- pseudoprimes
section HelperLemmas

private theorem a_id_helper {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : 2 ≤ (a ^ b - 1) / (a - 1) := by
  change 1 < _
  have h₁ : a - 1 ∣ a ^ b - 1 := by simpa only [one_pow] using nat_sub_dvd_pow_sub_pow a 1 b
  rw [Nat.lt_div_iff_mul_lt h₁, mul_one, tsub_lt_tsub_iff_right (Nat.le_of_succ_le ha)]
  exact lt_self_pow (Nat.lt_of_succ_le ha) hb

private theorem b_id_helper {a b : ℕ} (ha : 2 ≤ a) (hb : 2 < b) : 2 ≤ (a ^ b + 1) / (a + 1) := by
  rw [Nat.le_div_iff_mul_le (Nat.zero_lt_succ _)]
  apply Nat.succ_le_succ
  calc
    2 * a + 1 ≤ a ^ 2 * a := by nlinarith
    _ = a ^ 3 := by rw [Nat.pow_succ a 2]
    _ ≤ a ^ b := pow_le_pow_right (Nat.le_of_succ_le ha) hb

private theorem AB_id_helper (b p : ℕ) (_ : 2 ≤ b) (hp : Odd p) :
    (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1)) = (b ^ (2 * p) - 1) / (b ^ 2 - 1) := by
  have q₁ : b - 1 ∣ b ^ p - 1 := by simpa only [one_pow] using nat_sub_dvd_pow_sub_pow b 1 p
  have q₂ : b + 1 ∣ b ^ p + 1 := by simpa only [one_pow] using hp.nat_add_dvd_pow_add_pow b 1
  convert Nat.div_mul_div_comm q₁ q₂ using 2 <;> rw [mul_comm (_ - 1), ← Nat.sq_sub_sq]
  ring_nf

/-- Used in the proof of `psp_from_prime_psp`
-/
private theorem bp_helper {b p : ℕ} (hb : 0 < b) (hp : 1 ≤ p) :
    b ^ (2 * p) - 1 - (b ^ 2 - 1) = b * (b ^ (p - 1) - 1) * (b ^ p + b) :=
  have hi_bsquared : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  calc
    b ^ (2 * p) - 1 - (b ^ 2 - 1) = b ^ (2 * p) - (1 + (b ^ 2 - 1)) := by rw [Nat.sub_sub]
    _ = b ^ (2 * p) - (1 + b ^ 2 - 1) := by rw [Nat.add_sub_assoc hi_bsquared]
    _ = b ^ (2 * p) - b ^ 2 := by rw [Nat.add_sub_cancel_left]
    _ = b ^ (p * 2) - b ^ 2 := by rw [mul_comm]
    _ = (b ^ p) ^ 2 - b ^ 2 := by rw [pow_mul]
    _ = (b ^ p + b) * (b ^ p - b) := by rw [Nat.sq_sub_sq]
    _ = (b ^ p - b) * (b ^ p + b) := by rw [mul_comm]
    _ = (b ^ (p - 1 + 1) - b) * (b ^ p + b) := by rw [Nat.sub_add_cancel hp]
    _ = (b * b ^ (p - 1) - b) * (b ^ p + b) := by rw [pow_succ']
    _ = (b * b ^ (p - 1) - b * 1) * (b ^ p + b) := by rw [mul_one]
    _ = b * (b ^ (p - 1) - 1) * (b ^ p + b) := by rw [Nat.mul_sub_left_distrib]

end HelperLemmas

/-- Given a prime `p` which does not divide `b * (b ^ 2 - 1)`, we can produce a number `n` which is
larger than `p` and pseudoprime to base `b`. We do this by defining
`n = ((b ^ p - 1) / (b - 1)) * ((b ^ p + 1) / (b + 1))`

The primary purpose of this definition is to help prove `exists_infinite_pseudoprimes`. For a proof
that `n` is actually pseudoprime to base `b`, see `psp_from_prime_psp`, and for a proof that `n` is
greater than `p`, see `psp_from_prime_gt_p`.

This lemma is intended to be used when `2 ≤ b`, `2 < p`, `p` is prime, and `¬p ∣ b * (b ^ 2 - 1)`,
because those are the hypotheses for `psp_from_prime_psp`.
-/
private def psp_from_prime (b : ℕ) (p : ℕ) : ℕ :=
  (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1))

/--
This is a proof that the number produced using `psp_from_prime` is actually pseudoprime to base `b`.
The primary purpose of this lemma is to help prove `exists_infinite_pseudoprimes`.

We use <https://primes.utm.edu/notes/proofs/a_pseudoprimes.html> as a rough outline of the proof.
-/
private theorem psp_from_prime_psp {b : ℕ} (b_ge_two : 2 ≤ b) {p : ℕ} (p_prime : p.Prime)
    (p_gt_two : 2 < p) (not_dvd : ¬p ∣ b * (b ^ 2 - 1)) : FermatPsp (psp_from_prime b p) b := by
  unfold psp_from_prime
  set A := (b ^ p - 1) / (b - 1)
  set B := (b ^ p + 1) / (b + 1)
  -- Inequalities
  have hi_A : 1 < A := a_id_helper (Nat.succ_le_iff.mp b_ge_two) (Nat.Prime.one_lt p_prime)
  have hi_B : 1 < B := b_id_helper (Nat.succ_le_iff.mp b_ge_two) p_gt_two
  have hi_AB : 1 < A * B := one_lt_mul'' hi_A hi_B
  have hi_b : 0 < b := by omega
  have hi_p : 1 ≤ p := Nat.one_le_of_lt p_gt_two
  have hi_bsquared : 0 < b ^ 2 - 1 := by
    -- Porting note: was `by nlinarith [Nat.one_le_pow 2 b hi_b]`
    have h0 := mul_le_mul b_ge_two b_ge_two zero_le_two hi_b.le
    have h1 : 1 < 2 * 2 := by omega
    have := tsub_pos_of_lt (h1.trans_le h0)
    rwa [pow_two]
  have hi_bpowtwop : 1 ≤ b ^ (2 * p) := Nat.one_le_pow (2 * p) b hi_b
  have hi_bpowpsubone : 1 ≤ b ^ (p - 1) := Nat.one_le_pow (p - 1) b hi_b
  -- Other useful facts
  have p_odd : Odd p := p_prime.odd_of_ne_two p_gt_two.ne.symm
  have AB_not_prime : ¬Nat.Prime (A * B) := Nat.not_prime_mul hi_A.ne' hi_B.ne'
  have AB_id : A * B = (b ^ (2 * p) - 1) / (b ^ 2 - 1) := AB_id_helper _ _ b_ge_two p_odd
  have hd : b ^ 2 - 1 ∣ b ^ (2 * p) - 1 := by
    simpa only [one_pow, pow_mul] using nat_sub_dvd_pow_sub_pow _ 1 p
  -- We know that `A * B` is not prime, and that `1 < A * B`. Since two conditions of being
  -- pseudoprime are satisfied, we only need to show that `A * B` is probable prime to base `b`
  refine ⟨?_, AB_not_prime, hi_AB⟩
  -- Used to prove that `2 * p * (b ^ 2 - 1) ∣ (b ^ 2 - 1) * (A * B - 1)`.
  have ha₁ : (b ^ 2 - 1) * (A * B - 1) = b * (b ^ (p - 1) - 1) * (b ^ p + b) := by
    apply_fun fun x => x * (b ^ 2 - 1) at AB_id
    rw [Nat.div_mul_cancel hd] at AB_id
    apply_fun fun x => x - (b ^ 2 - 1) at AB_id
    nth_rw 2 [← one_mul (b ^ 2 - 1)] at AB_id
    rw [← Nat.mul_sub_right_distrib, mul_comm] at AB_id
    rw [AB_id]
    exact bp_helper hi_b hi_p
  -- If `b` is even, then `b^p` is also even, so `2 ∣ b^p + b`
  -- If `b` is odd, then `b^p` is also odd, so `2 ∣ b^p + b`
  have ha₂ : 2 ∣ b ^ p + b := by
    -- Porting note: golfed
    rw [← even_iff_two_dvd, Nat.even_add, Nat.even_pow' p_prime.ne_zero]
  -- Since `b` isn't divisible by `p`, `b` is coprime with `p`. we can use Fermat's Little Theorem
  -- to prove this.
  have ha₃ : p ∣ b ^ (p - 1) - 1 := by
    have : ¬p ∣ b := mt (fun h : p ∣ b => dvd_mul_of_dvd_left h _) not_dvd
    have : p.Coprime b := Or.resolve_right (Nat.coprime_or_dvd_of_prime p_prime b) this
    have : IsCoprime (b : ℤ) ↑p := this.symm.isCoprime
    have : ↑b ^ (p - 1) ≡ 1 [ZMOD ↑p] := Int.ModEq.pow_card_sub_one_eq_one p_prime this
    have : ↑p ∣ ↑b ^ (p - 1) - ↑1 := mod_cast Int.ModEq.dvd (Int.ModEq.symm this)
    exact mod_cast this
  -- Because `p - 1` is even, there is a `c` such that `2 * c = p - 1`. `nat_sub_dvd_pow_sub_pow`
  -- implies that `b ^ c - 1 ∣ (b ^ c) ^ 2 - 1`, and `(b ^ c) ^ 2 = b ^ (p - 1)`.
  have ha₄ : b ^ 2 - 1 ∣ b ^ (p - 1) - 1 := by
    cases' p_odd with k hk
    have : 2 ∣ p - 1 := ⟨k, by simp [hk]⟩
    cases' this with c hc
    have : b ^ 2 - 1 ∣ (b ^ 2) ^ c - 1 := by
      simpa only [one_pow] using nat_sub_dvd_pow_sub_pow _ 1 c
    have : b ^ 2 - 1 ∣ b ^ (2 * c) - 1 := by rwa [← pow_mul] at this
    rwa [← hc] at this
  -- Used to prove that `2 * p` divides `A * B - 1`
  have ha₅ : 2 * p * (b ^ 2 - 1) ∣ (b ^ 2 - 1) * (A * B - 1) := by
    suffices q : 2 * p * (b ^ 2 - 1) ∣ b * (b ^ (p - 1) - 1) * (b ^ p + b) by rwa [ha₁]
    -- We already proved that `b ^ 2 - 1 ∣ b ^ (p - 1) - 1`.
    -- Since `2 ∣ b ^ p + b` and `p ∣ b ^ p + b`, if we show that 2 and p are coprime, then we
    -- know that `2 * p ∣ b ^ p + b`
    have q₁ : Nat.Coprime p (b ^ 2 - 1) :=
      haveI q₂ : ¬p ∣ b ^ 2 - 1 := by
        rw [mul_comm] at not_dvd
        exact mt (fun h : p ∣ b ^ 2 - 1 => dvd_mul_of_dvd_left h _) not_dvd
      (Nat.Prime.coprime_iff_not_dvd p_prime).mpr q₂
    have q₂ : p * (b ^ 2 - 1) ∣ b ^ (p - 1) - 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd q₁ ha₃ ha₄
    have q₃ : p * (b ^ 2 - 1) * 2 ∣ (b ^ (p - 1) - 1) * (b ^ p + b) := mul_dvd_mul q₂ ha₂
    have q₄ : p * (b ^ 2 - 1) * 2 ∣ b * ((b ^ (p - 1) - 1) * (b ^ p + b)) :=
      dvd_mul_of_dvd_right q₃ _
    rwa [mul_assoc, mul_comm, mul_assoc b]
  have ha₆ : 2 * p ∣ A * B - 1 := by
    rw [mul_comm] at ha₅
    exact Nat.dvd_of_mul_dvd_mul_left hi_bsquared ha₅
  -- `A * B` divides `b ^ (2 * p) - 1` because `A * B * (b ^ 2 - 1) = b ^ (2 * p) - 1`.
  -- This can be proven by multiplying both sides of `AB_id` by `b ^ 2 - 1`.
  have ha₇ : A * B ∣ b ^ (2 * p) - 1 := by
    use b ^ 2 - 1
    have : A * B * (b ^ 2 - 1) = (b ^ (2 * p) - 1) / (b ^ 2 - 1) * (b ^ 2 - 1) :=
      congr_arg (fun x : ℕ => x * (b ^ 2 - 1)) AB_id
    simpa only [add_comm, Nat.div_mul_cancel hd, Nat.sub_add_cancel hi_bpowtwop] using this.symm
  -- Since `2 * p ∣ A * B - 1`, there is a number `q` such that `2 * p * q = A * B - 1`.
  -- By `nat_sub_dvd_pow_sub_pow`, we know that `b ^ (2 * p) - 1 ∣ b ^ (2 * p * q) - 1`.
  -- This means that `b ^ (2 * p) - 1 ∣ b ^ (A * B - 1) - 1`.
  cases' ha₆ with q hq
  have ha₈ : b ^ (2 * p) - 1 ∣ b ^ (A * B - 1) - 1 := by
    simpa only [one_pow, pow_mul, hq] using nat_sub_dvd_pow_sub_pow _ 1 q
  -- We have proved that `A * B ∣ b ^ (2 * p) - 1` and `b ^ (2 * p) - 1 ∣ b ^ (A * B - 1) - 1`.
  -- Therefore, `A * B ∣ b ^ (A * B - 1) - 1`.
  exact dvd_trans ha₇ ha₈

/--
This is a proof that the number produced using `psp_from_prime` is greater than the prime `p` used
to create it. The primary purpose of this lemma is to help prove `exists_infinite_pseudoprimes`.
-/
private theorem psp_from_prime_gt_p {b : ℕ} (b_ge_two : 2 ≤ b) {p : ℕ} (p_prime : p.Prime)
    (p_gt_two : 2 < p) : p < psp_from_prime b p := by
  unfold psp_from_prime
  set A := (b ^ p - 1) / (b - 1)
  set B := (b ^ p + 1) / (b + 1)
  rw [show A * B = (b ^ (2 * p) - 1) / (b ^ 2 - 1) from
      AB_id_helper _ _ b_ge_two (p_prime.odd_of_ne_two p_gt_two.ne.symm)]
  have AB_dvd : b ^ 2 - 1 ∣ b ^ (2 * p) - 1 := by
    simpa only [one_pow, pow_mul] using nat_sub_dvd_pow_sub_pow _ 1 p
  suffices h : p * (b ^ 2 - 1) < b ^ (2 * p) - 1 by
    have h₁ : p * (b ^ 2 - 1) / (b ^ 2 - 1) < (b ^ (2 * p) - 1) / (b ^ 2 - 1) :=
      Nat.div_lt_div_of_lt_of_dvd AB_dvd h
    have h₂ : 0 < b ^ 2 - 1 := by
      linarith [show 3 ≤ b ^ 2 - 1 from le_tsub_of_add_le_left (show 4 ≤ b ^ 2 by nlinarith)]
    rwa [Nat.mul_div_cancel _ h₂] at h₁
  rw [Nat.mul_sub_left_distrib, mul_one, pow_mul]
  conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ p by omega)]
  rw [Nat.pow_succ (b ^ 2)]
  suffices h : p * b ^ 2 < (b ^ 2) ^ (p - 1) * b ^ 2 by
    apply gt_of_ge_of_gt
    · exact tsub_le_tsub_left (one_le_of_lt p_gt_two) ((b ^ 2) ^ (p - 1) * b ^ 2)
    · have : p ≤ p * b ^ 2 := Nat.le_mul_of_pos_right _ (show 0 < b ^ 2 by nlinarith)
      exact tsub_lt_tsub_right_of_le this h
  suffices h : p < (b ^ 2) ^ (p - 1) by
    have : 4 ≤ b ^ 2 := by nlinarith
    have : 0 < b ^ 2 := by omega
    exact mul_lt_mul_of_pos_right h this
  rw [← pow_mul, Nat.mul_sub_left_distrib, mul_one]
  have : 2 ≤ 2 * p - 2 := le_tsub_of_add_le_left (show 4 ≤ 2 * p by omega)
  have : 2 + p ≤ 2 * p := by omega
  have : p ≤ 2 * p - 2 := le_tsub_of_add_le_left this
  exact this.trans_lt (lt_pow_self b_ge_two _)

/-- For all positive bases, there exist infinite **Fermat pseudoprimes** to that base.
Given in this form: for all numbers `b ≥ 1` and `m`, there exists a pseudoprime `n` to base `b` such
that `m ≤ n`. This form is similar to `Nat.exists_infinite_primes`.
-/
theorem exists_infinite_pseudoprimes {b : ℕ} (h : 1 ≤ b) (m : ℕ) :
    ∃ n : ℕ, FermatPsp n b ∧ m ≤ n := by
  by_cases b_ge_two : 2 ≤ b
  -- If `2 ≤ b`, then because there exist infinite prime numbers, there is a prime number p with
  -- `m ≤ p` and `¬p ∣ b*(b^2 - 1)`. We pick a prime number `b*(b^2 - 1) + 1 + m ≤ p` because we
  -- automatically know that `p` is greater than m and that it does not divide `b*(b^2 - 1)`
  -- (because `p` can't divide a number less than `p`).
  -- From `p`, we can use the lemmas we proved earlier to show that
  -- `((b^p - 1)/(b - 1)) * ((b^p + 1)/(b + 1))` is a pseudoprime to base `b`.
  · have h := Nat.exists_infinite_primes (b * (b ^ 2 - 1) + 1 + m)
    cases' h with p hp
    cases' hp with hp₁ hp₂
    have h₁ : 0 < b := pos_of_gt (Nat.succ_le_iff.mp b_ge_two)
    have h₂ : 4 ≤ b ^ 2 := pow_le_pow_left' b_ge_two 2
    have h₃ : 0 < b ^ 2 - 1 := tsub_pos_of_lt (gt_of_ge_of_gt h₂ (by norm_num))
    have h₄ : 0 < b * (b ^ 2 - 1) := mul_pos h₁ h₃
    have h₅ : b * (b ^ 2 - 1) < p := by omega
    have h₆ : ¬p ∣ b * (b ^ 2 - 1) := Nat.not_dvd_of_pos_of_lt h₄ h₅
    have h₇ : b ≤ b * (b ^ 2 - 1) := Nat.le_mul_of_pos_right _ h₃
    have h₈ : 2 ≤ b * (b ^ 2 - 1) := le_trans b_ge_two h₇
    have h₉ : 2 < p := gt_of_gt_of_ge h₅ h₈
    have h₁₀ := psp_from_prime_gt_p b_ge_two hp₂ h₉
    use psp_from_prime b p
    constructor
    · exact psp_from_prime_psp b_ge_two hp₂ h₉ h₆
    · exact le_trans (show m ≤ p by omega) (le_of_lt h₁₀)
  -- If `¬2 ≤ b`, then `b = 1`. Since all composite numbers are pseudoprimes to base 1, we can pick
  -- any composite number greater than m. We choose `2 * (m + 2)` because it is greater than `m` and
  -- is composite for all natural numbers `m`.
  · have h₁ : b = 1 := by omega
    rw [h₁]
    use 2 * (m + 2)
    have : ¬Nat.Prime (2 * (m + 2)) := Nat.not_prime_mul (by omega) (by omega)
    exact ⟨fermatPsp_base_one (by omega) this, by omega⟩
#align fermat_psp.exists_infinite_pseudoprimes Nat.exists_infinite_pseudoprimes

theorem frequently_atTop_fermatPsp {b : ℕ} (h : 1 ≤ b) : ∃ᶠ n in Filter.atTop, FermatPsp n b := by
  -- Based on the proof of `Nat.frequently_atTop_modEq_one`
  refine Filter.frequently_atTop.2 fun n => ?_
  obtain ⟨p, hp⟩ := exists_infinite_pseudoprimes h n
  exact ⟨p, hp.2, hp.1⟩
#align fermat_psp.frequently_at_top_fermat_psp Nat.frequently_atTop_fermatPsp

/-- Infinite set variant of `Nat.exists_infinite_pseudoprimes`
-/
theorem infinite_setOf_pseudoprimes {b : ℕ} (h : 1 ≤ b) :
    Set.Infinite { n : ℕ | FermatPsp n b } :=
  Nat.frequently_atTop_iff_infinite.mp (frequently_atTop_fermatPsp h)
#align fermat_psp.infinite_set_of_prime_modeq_one Nat.infinite_setOf_pseudoprimes

end Nat

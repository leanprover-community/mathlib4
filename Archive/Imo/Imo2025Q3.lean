/-
Copyright (c) 2025 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.Simproc.Factors

/-!
# IMO 2025 Q3

Let `ℕ+` denote the set of positive integers. A function `f : ℕ+ → ℕ+` is said to be bonza if
`f a ∣ b ^ a - (f b) ^ (f a)` for all positive integers `a` and `b`.
Determine the smallest real constant `c` such that `f n ≤ c * n` for all bonza functions `f` and
all positive integers `n`.

## Solution

We follow solution from https://web.evanchen.cc/exams/IMO-2025-notes.pdf.

We first plug in `a = b = n` to get the basic constraint `∀ n, f n ∣ n ^ n`. Next, one shows that
unless `f` is the identity, every odd prime must satisfy `f p = 1`. From here, any odd prime divisor
of `f n` is ruled out by taking `a = n, b = p`, so `f n` is always a power of `2`.
Finally, evaluating `a = n, b = 3` gives `f n ∣ 3 ^ n - 1`, and according to the LTE lemma, we have
`padicValNat 2 (3 ^ n - 1) = padicValNat 2 n + 2` for `Even n`. Therefore,
`f(n) ≤ 2 ^ (padicValNat 2 n + 2) ≤ 4 * n`, so `c=4` works.

A matching construction is `f n = 1` for `Odd n`, `f 4 = 16`, and `f n = 2` for other `Even n`,
which attains the bound, showing the optimal answer is `c = 4`.
-/

open Nat Int

namespace Imo2025Q3

/-- Define bonza functions -/
def IsBonza : (ℕ → ℕ) → Prop := fun (f : ℕ → ℕ) ↦
  (∀ a b : ℕ, 0 < a → 0 < b → (f a : ℤ) ∣ (b : ℤ) ^ a - (f b : ℤ) ^ (f a)) ∧ ∀ n, 0 < n → 0 < f n

namespace IsBonza

variable {f : ℕ → ℕ}

/-- For each bonza function `f`, we have `f n ∣ n ^ n` -/
lemma apply_dvd_pow (hf : IsBonza f) {n : ℕ} (hn : 0 < n) : f n ∣ n ^ n := by
  have : (f n : ℤ) ∣ (f n : ℤ) ^ f n := (f n : ℤ).dvd_refl.pow (ne_zero_of_lt (hf.2 n hn))
  have : (f n : ℤ) ∣ (n : ℤ) ^ n := (dvd_iff_dvd_of_dvd_sub (hf.1 n n hn hn)).mpr this
  rwa [← natCast_pow n n, ofNat_dvd] at this

lemma apply_prime_eq_one_or_dvd_self_sub_apply (hf : IsBonza f) {p : ℕ} (hp : p.Prime) :
    f p = 1 ∨ (∀ b > (0 : ℕ), (p : ℤ) ∣ (b : ℤ) - ((f b) : ℤ)) := by
  have : f p ∣ p ^ p := hf.apply_dvd_pow hp.pos
  obtain ⟨k, _, eq⟩ : ∃ k, k ≤ p ∧ f p = p ^ k := (Nat.dvd_prime_pow hp).mp this
  by_cases ch : k = 0
  · left
    rwa [ch, pow_zero] at eq
  · right
    intro b hb
    have : (p : ℤ) ∣ (b : ℤ) ^ p - (f b) ^ f p := by calc
      _ ∣ (f p : ℤ) := by simp [eq, ch]
      _ ∣ _ := hf.1 p b hp.pos hb
    have : (b : ℤ) ≡ (f b : ℤ) [ZMOD p] := by calc
      _ ≡ (b : ℤ) ^ p [ZMOD p] := (ModEq.pow_prime_eq_self hp b).symm
      _ ≡ (f b) ^ f p [ZMOD p] := (Int.modEq_iff_dvd.mpr this).symm
      _ ≡ _ [ZMOD p] := by
        rw [eq]
        nth_rw 2 [← pow_one (f b : ℤ)]
        exact ModEq.pow_eq_pow hp (p.sub_one_dvd_pow_sub_one k) (one_le_pow k p hp.pos)
          (by norm_num) (f b)
    rwa [modEq_comm, Int.modEq_iff_dvd] at this

/-- For each bonza function `f`, then `f p = 1` for sufficient big prime `p` -/
theorem not_id_apply_prime_of_gt_eq_one (hf : IsBonza f) (hnf : ¬ ∀ x > (0 : ℕ), f x = x) :
    ∃ N, ∀ p > N, p.Prime → f p = 1 := by
  obtain ⟨b, hb, neq⟩ : ∃ b, 0 < b ∧ f b ≠ b := Set.not_subset.mp hnf
  use ((b : ℤ) - (f b : ℤ)).natAbs
  intro p _ pp
  have : f p = 1 ∨ (p : ℤ) ∣ (b : ℤ) - (f b : ℤ) :=
    Or.casesOn (hf.apply_prime_eq_one_or_dvd_self_sub_apply pp) (by grind) (by grind)
  rcases this with ch | ch
  · exact ch
  · have : p ≤ ((b : ℤ) - (f b : ℤ)).natAbs := natAbs_le_of_dvd_ne_zero ch (by grind)
    linarith

theorem apply_prime_gt_two_eq_one (hf : IsBonza f) (hnf : ¬ ∀ x > (0 : ℕ), f x = x) :
    ∀ p > 2, p.Prime → f p = 1 := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ p > N, p.Prime → f p = 1 :=
    hf.not_id_apply_prime_of_gt_eq_one hnf
  have apply_dvd_pow_sub {a p : ℕ} (ha : 0 < a) (pp : p.Prime) (hp : N < p) :
      (f a : ℤ) ∣ p ^ a - 1 := by
    simpa [hN p hp pp, Nat.cast_one, one_pow] using hf.1 a p ha (by lia)
  intro q hq qp
  obtain ⟨k, ha1, ha2⟩ : ∃ k, k ≤ q ∧ f q = q ^ k :=
    (dvd_prime_pow qp).mp (hf.apply_dvd_pow (zero_lt_of_lt hq))
  by_cases ch : k = 0
  · simpa [ch] using ha2
  · have {p : ℕ} (pp : p.Prime) (hp : N < p) : (q : ℤ) ∣ p ^ q - 1 := by calc
      _ ∣ (f q : ℤ) := by simp [ha2, natCast_pow q k, ch]
      _ ∣ _ := apply_dvd_pow_sub (zero_lt_of_lt hq) pp hp
    obtain ⟨p, hp⟩ : ∃ p > N, p.Prime ∧ p ≡ -1 [ZMOD q] :=
      forall_exists_prime_gt_and_zmodEq N (by lia) isCoprime_one_left.neg_left
    have : 1 ≡ -1 [ZMOD q] := by calc
      _ ≡ p ^ q [ZMOD q] := by grind [Int.modEq_iff_dvd]
      _ ≡ p [ZMOD q] := ModEq.pow_prime_eq_self qp p
      _ ≡ _ [ZMOD q] := hp.2.2
    rw [modEq_comm, Int.modEq_iff_dvd] at this
    have : (q : ℤ).natAbs ≤ (1 - (-1) : ℤ).natAbs := natAbs_le_of_dvd_ne_zero this (by norm_num)
    lia

/-- Therefore, if a bonza function is not identity, then every `f x` is a pow of two -/
lemma not_id_two_pow (hf : IsBonza f) (hnf : ¬ ∀ x > (0 : ℕ), f x = x) :
    ∀ n, 0 < n → ∃ a, f n = 2 ^ a := fun n hn ↦
  have {p} (pp : p.Prime) (hp : p ∣ f n) : p = 2 := by
    by_contra nh
    have dvd : (p : ℤ) ∣ p ^ n - 1 := by calc
      _ ∣ (f n : ℤ) := ofNat_dvd.mpr hp
      _ ∣ _ := by
        have := hf.1 n p hn pp.pos
        have p_gt_two : 2 < p := lt_of_le_of_ne pp.two_le (fun a ↦ nh (id (Eq.symm a)))
        rwa [hf.apply_prime_gt_two_eq_one hnf p p_gt_two pp, Nat.cast_one, one_pow] at this
    have : (p : ℤ) ∣ p ^ n := dvd_pow (Int.dvd_refl p) (ne_zero_of_lt hn)
    exact (pp.not_dvd_one) (ofNat_dvd.mp ((Int.dvd_iff_dvd_of_dvd_sub dvd).mp this))
  ⟨(f n).primeFactorsList.length, eq_prime_pow_of_unique_prime_dvd (ne_zero_of_lt (hf.2 n hn)) this⟩

end IsBonza

/-- An example of a bonza function achieving the maximum number of values of `c`. -/
def fExample : ℕ → ℕ := fun x ↦
  if ¬ 2 ∣ x then 1
  else if x = 2 then 4
  else 2 ^ (padicValNat 2 x + 2)

namespace fExample

lemma dvd_pow_sub {a b : ℕ} {x : ℤ} (hb : 2 ∣ b) (ha : a ≥ 4) (hx : 2 ∣ x) :
    2 ^ (padicValNat 2 a + 2) ∣ (b : ℤ) ^ a - x ^ 2 ^ (padicValNat 2 a + 2) := by
  refine dvd_sub ?_ ?_
  · exact (pow_dvd_pow 2 (padicValNat_add_le_self (hp := fact_prime_two) (by lia))).trans
      (pow_dvd_pow_of_dvd (ofNat_dvd_right.mpr hb) a)
  · calc
    _ ∣ (2 : ℤ) ^ 2 ^ (padicValNat 2 a + 2) := by
      refine pow_dvd_pow 2 ?_
      calc
      _ < 2 ^ (padicValNat 2 a + 1) := Nat.lt_two_pow_self
      _ ≤ _ := by simp [Nat.pow_le_pow_iff_right le.refl]
    _ ∣ _ := pow_dvd_pow_of_dvd hx (2 ^ (padicValNat 2 a + 2))

/-- To verify the example is a bonza function -/
lemma isBonza : IsBonza fExample := by
  constructor
  · intro a b ha hb
    by_cases ch1 : ¬ 2 ∣ a
    · simp [fExample, ch1]
    by_cases ch2 : a = 2
    · simp only [fExample, ch2, dvd_refl, not_true_eq_false, ↓reduceIte, Nat.cast_ofNat,
        Nat.two_dvd_ne_zero, Nat.cast_ite, Nat.cast_one, Nat.cast_pow, ite_pow, one_pow,
        Int.reducePow]
      split_ifs with hb1 hb2
      · grind [sq_mod_four_eq_one_of_odd]
      · simp [hb2]
      · refine dvd_sub ?_ ?_
        · have : 2 ∣ (b : ℤ) := by grind
          simpa using pow_dvd_pow_of_dvd this 2
        · exact Dvd.dvd.pow ⟨2 ^ padicValNat 2 b, by ring⟩ (zero_ne_add_one 3).symm
    · simp only [fExample, ch1, ↓reduceIte, ch2, Nat.cast_pow, Nat.cast_ofNat, Nat.two_dvd_ne_zero,
        Nat.cast_ite, Nat.cast_one, ite_pow, one_pow]
      split_ifs with hb1 hb2
      · by_cases lt : b = 1
        · simp [lt]
        have : (padicValNat 2 a + 2) ≤ padicValInt 2 (b ^ a - 1) := by
          rw [← Int.natCast_pow_pred b a hb]
          exact padicValNat.pow_two_sub_one_ge (by lia) (two_dvd_ne_zero.mpr hb1) (by lia)
            (even_iff.mpr (by simpa using ch1))
        exact Int.dvd_trans (pow_dvd_pow 2 this) (padicValInt_dvd ((b : ℤ) ^ a - 1))
      · grind [dvd_pow_sub]
      · grind [dvd_pow_sub]
  · grind [fExample, Nat.two_pow_pos]

theorem apply_le {f : ℕ → ℕ} (hf : IsBonza f) {n : ℕ} (hn : 0 < n) : f n ≤ 4 * n := by
  by_cases hnf : ∀ x > (0 : ℕ), f x = x
  · simpa [hnf n hn] using by lia
  · obtain ⟨k, hk⟩ := hf.not_id_two_pow hnf n hn
    rcases n.even_or_odd with ch | ch
    · have apply_dvd_three_pow_sub_one : f n ∣ 3 ^ n - 1 := by
        have eq1 : f 3 = 1 := hf.apply_prime_gt_two_eq_one hnf 3 (by norm_num) prime_three
        have eq2 : (3 : ℤ) ^ n - 1 = (3 ^ n - 1 : ℕ) := by
          grind [natCast_pred_of_pos, pos_of_neZero]
        have := hf.1 n 3 hn (by norm_num)
        rwa [Nat.cast_ofNat, eq1, Nat.cast_one, one_pow, eq2, ofNat_dvd] at this
      rw [hk] at apply_dvd_three_pow_sub_one
      calc
        _ ≤ 2 ^ padicValNat 2 (3 ^ n - 1) := by
          rwa [hk, Nat.pow_le_pow_iff_right le.refl, ← padicValNat_dvd_iff_le
            (by grind [one_lt_pow])]
        _ = 4 * 2 ^ padicValNat 2 n := by
          have : padicValNat 2 (3 ^ n - 1) + 1 = 3 + padicValNat 2 n := by
            simpa [← factorization_def _ prime_two, ← primeFactorsList_count_eq] using
              padicValNat.pow_two_sub_one (show 1 < 3 by simp) (by simp) (by lia) ch
          have : padicValNat 2 (3 ^ n - 1) = 2 + padicValNat 2 n := by lia
          rw [congrArg (HPow.hPow 2) this, Nat.pow_add]
        _ ≤ _ := mul_le_mul_left 4 (le_of_dvd hn pow_padicValNat_dvd)
    · have : k = 0 := by
        by_contra! nh
        have : Odd (f n) := ch.pow.of_dvd_nat (hf.apply_dvd_pow hn)
        rw [hk, odd_pow_iff nh] at this
        contradiction
      simpa [hk, this] using by lia

end fExample

theorem result : IsLeast {c : ℝ | ∀ f : ℕ → ℕ, IsBonza f → ∀ n, 0 < n → f n ≤ c * n} 4 := by
  constructor
  · intro f hf n hn
    have : 4 * (n : ℝ) = (4 * n : ℕ) := by simp
    rw [this, Nat.cast_le]
    exact fExample.apply_le hf hn
  · intro c hc
    have : 16 ≤ c * 4 := by
      simpa [fExample, ← factorization_def _ prime_two, ← primeFactorsList_count_eq] using
        hc fExample fExample.isBonza 4
    linarith

end Imo2025Q3

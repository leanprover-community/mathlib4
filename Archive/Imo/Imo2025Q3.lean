/-
Copyright (c) 2025 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.Simproc.Factors

open Nat Int

/- Let $\mathbb{N}+$ denote the set of positive integers. A function $f: \mathbb{N}+ \rightarrow
\mathbb{N}+$ is said to be bonza if $f(a)$ divides $b^a-f(b)^{f(a)}$ for all positive integers $a$
and $b$. Determine the smallest real constant $c$ such that $f(n) \leq c n$ for all bonza functions
$f$ and all positive integers $n$.
-/

/-- Define bonza functions
-/
def bonza : Set (ℕ → ℕ) :=
  {f : ℕ → ℕ | (∀ a b : ℕ, 0 < a → 0 < b → (f a : ℤ) ∣ (b : ℤ) ^ a - (f b : ℤ) ^ (f a)) ∧
    ∀ n, 0 < n → f n > 0}

variable {f : ℕ → ℕ}

/- For each bonza function $f$, we have $f n | n ^ n$
-/
lemma bonza_apply_dvd_pow (hf : f ∈ bonza) {n : ℕ} (hn : n > 0) : f n ∣ n ^ n := by
  have : (f n : ℤ) ∣ (f n : ℤ) ^ f n :=
    Dvd.dvd.pow (Int.dvd_refl (f n)) (Nat.ne_zero_of_lt (hf.2 n hn))
  have : (f n : ℤ) ∣ (n : ℤ) ^ n := (Int.dvd_iff_dvd_of_dvd_sub (hf.1 n n hn hn)).mpr this
  rwa [← Int.natCast_pow n n, ofNat_dvd] at this

lemma bonza_apply_prime_eq_one_or_dvd_self_sub_apply (hf : f ∈ bonza) {p : ℕ} (hp : Nat.Prime p) :
    f p = 1 ∨ (∀ b : ℕ, b > 0 → (p : ℤ) ∣ (b : ℤ) - ((f b) : ℤ)) := by
  have : f p ∣ p ^ p := bonza_apply_dvd_pow hf (Prime.pos hp)
  obtain ⟨k, _, eq⟩ : ∃ k, k ≤ p ∧ f p = p ^ k := (Nat.dvd_prime_pow hp).mp this
  by_cases ch : k = 0
  · left
    rwa [ch, pow_zero] at eq
  · right
    intro b hb
    have : (p : ℤ) ∣ (b : ℤ) ^ p - (f b) ^ f p := by calc
      _ ∣ (f p : ℤ) := by
        rw [eq, natCast_dvd_natCast]
        exact dvd_pow_self p ch
      _ ∣ _ := hf.1 p b (Prime.pos hp) hb
    have : (b : ℤ) ≡ (f b : ℤ) [ZMOD p] := by calc
      _ ≡ (b : ℤ) ^ p [ZMOD p] := Int.ModEq.symm (ModEq.pow_card_eq_self hp)
      _ ≡ (f b) ^ f p [ZMOD p] := Int.ModEq.symm ((fun {n a b} ↦ Int.modEq_iff_dvd.mpr) this)
      _ ≡ _ [ZMOD p] := by
        rw [eq]
        nth_rw 2 [← pow_one (f b : ℤ)]
        exact Int.ModEq.pow_eq_pow hp (p.sub_one_dvd_pow_sub_one k) (one_le_pow k p (Prime.pos hp))
          (by norm_num)
    rwa [modEq_comm, Int.modEq_iff_dvd] at this

/- For each bonza function $f$, then $f p = 1$ for sufficient big prime $p$
-/
theorem bonza_not_x_apply_prime_of_gt_eq_one (hf : f ∈ bonza) (hnf : ¬ ∀ x, x > 0 → f x = x) :
    (∃ N, ∀ p > N, Nat.Prime p → f p = 1) := by
  obtain ⟨b, hb, neq⟩ : ∃ b, b > 0 ∧ f b ≠ b := Set.not_subset.mp hnf
  have {p : ℕ} (hp : Nat.Prime p): f p = 1 ∨ (p : ℤ) ∣ (b : ℤ) - (f b : ℤ) :=
    Or.casesOn (bonza_apply_prime_eq_one_or_dvd_self_sub_apply hf hp) (by grind) (by grind)
  use ((b : ℤ) - (f b : ℤ)).natAbs
  intro p _ pp
  rcases this pp with ch | ch
  · exact ch
  · have : p ≤ ((b : ℤ) - (f b : ℤ)).natAbs := natAbs_le_of_dvd_ne_zero ch (by grind)
    linarith

theorem Nat.exists_prime_gt_modEq_neg_one {k : ℕ} (n : ℕ) (hk0 : NeZero k) :
    ∃ (p : ℕ), Prime p ∧ n < p ∧ p ≡ -1 [ZMOD k] := by
  have : IsUnit (-1 : ZMod k) := by simp
  obtain ⟨p, hp⟩ := Nat.forall_exists_prime_gt_and_eq_mod this n
  refine ⟨p, ⟨hp.2.1, hp.1, ?_⟩⟩
  rw [modEq_comm, ← ZMod.intCast_eq_intCast_iff, ZMod.intCast_eq_intCast_iff_dvd_sub, Int.sub_neg]
  have := hp.2.2
  rw [eq_neg_iff_add_eq_zero, ← cast_add_one p, ZMod.natCast_eq_zero_iff] at this
  exact ofNat_dvd_left.mpr this

theorem bonza_apply_prime_gt_two_eq_one (hf : f ∈ bonza) (hnf : ¬ ∀ x, x > 0 → f x = x) :
    ∀ p > 2, Nat.Prime p → f p = 1 := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ p > N, Nat.Prime p → f p = 1 :=
    bonza_not_x_apply_prime_of_gt_eq_one hf hnf
  have apply_dvd_pow_sub {a p : ℕ} (ha : a > 0) (pp : Nat.Prime p) (hp : p > N) :
      (f a : ℤ) ∣ p ^ a - 1 := by
    simpa [hN p hp pp, Nat.cast_one, one_pow] using hf.1 a p ha (by omega)
  intro q hq qp
  obtain ⟨k, ha1, ha2⟩ : ∃ k, k ≤ q ∧ f q = q ^ k :=
    (Nat.dvd_prime_pow qp).mp (bonza_apply_dvd_pow hf (zero_lt_of_lt hq))
  by_cases ch : k = 0
  · simpa [ch] using ha2
  · have {p : ℕ} (pp : Nat.Prime p) (hp : p > N) : (q : ℤ) ∣ p ^ q - 1 := by calc
      _ ∣ (f q : ℤ) := by
        rw [ha2, Int.natCast_pow q k]
        exact dvd_pow_self (q : ℤ) ch
      _ ∣ _ := apply_dvd_pow_sub (zero_lt_of_lt hq) pp hp
    obtain ⟨p, hp⟩ := Nat.exists_prime_gt_modEq_neg_one N (NeZero.of_gt hq)
    have : 1 ≡ -1 [ZMOD q] := by calc
      _ ≡ p ^ q [ZMOD q] := by grind [Int.modEq_iff_dvd]
      _ ≡ p [ZMOD q] := ModEq.pow_card_eq_self qp
      _ ≡ _ [ZMOD q] := hp.2.2
    rw [modEq_comm, Int.modEq_iff_dvd] at this
    have : (q : ℤ).natAbs ≤ (1 - (-1) : ℤ).natAbs := natAbs_le_of_dvd_ne_zero this (by norm_num)
    omega

/- Therefore, if a bonza function is not identity, then every $f x$ is a pow of two
-/
lemma bonza_not_id_two_pow (hf : f ∈ bonza) (hnf : ¬ ∀ x, x > 0 → f x = x) :
    ∀ n, n > 0 → ∃ a, f n = 2 ^ a := fun n hn ↦ by
  have : ∀ {p}, Nat.Prime p → p ∣ f n → p = 2 := fun {p} pp hp ↦ by
    by_contra nh
    have dvd : (p : ℤ) ∣ p ^ n - 1 := by calc
      _ ∣ (f n : ℤ) := ofNat_dvd.mpr hp
      _ ∣ _ := by
        have := hf.1 n p hn (Prime.pos pp)
        have p_gt_two : p > 2 := Nat.lt_of_le_of_ne (Prime.two_le pp) (fun a ↦ nh (id (Eq.symm a)))
        rwa [bonza_apply_prime_gt_two_eq_one hf hnf p p_gt_two pp, Nat.cast_one, one_pow] at this
    have : (p : ℤ) ∣ p ^ n := dvd_pow (Int.dvd_refl p) (Nat.ne_zero_of_lt hn)
    exact (Nat.Prime.not_dvd_one pp) (ofNat_dvd.mp ((Int.dvd_iff_dvd_of_dvd_sub dvd).mp this))
  use (f n).primeFactorsList.length
  exact Nat.eq_prime_pow_of_unique_prime_dvd (Nat.ne_zero_of_lt (hf.2 n hn)) this

/-- An example of a bonza function achieving the maximum number of values of `c`.
-/
def fExample : ℕ → ℕ := fun x ↦
  if ¬ 2 ∣ x then 1
  else if x = 2 then 4
  else 2 ^ (padicValNat 2 x + 2)

lemma LTE_lemma_of_pow_sub {a b : ℕ} (h1b : 1 < b) (hb : ¬2 ∣ b) (ha : a ≠ 0) (Evena : Even a) :
    (padicValNat 2 a + 2) ≤ padicValNat 2 (b ^ a - 1) := by
  have : padicValNat 2 ((b + 1) * (b - 1)) ≥ 3 := by
    refine (padicValNat_dvd_iff_le (hp := fact_prime_two) (by grind [mul_ne_zero])).mp ?_
    simpa [← Nat.pow_two_sub_pow_two b 1] using by grind [Nat.eight_dvd_sq_sub_one_of_odd]
  have := padicValNat.pow_two_sub_pow h1b (by grind) hb ha Evena
  grind [← padicValNat.mul]

lemma padicValNat_lemma {a : ℕ} (ha : a ≥ 4) (dvd : 2 ∣ a) : padicValNat 2 a + 2 ≤ a := by
  rcases dvd with ⟨k, hk⟩
  have : padicValNat 2 k < k := by calc
    _ ≤ Nat.log 2 k := padicValNat_le_nat_log k
    _ < _ := log_lt_self 2 (by omega)
  grind [padicValNat.mul, padicValNat.self]

lemma verify_case_two_dvd {a b : ℕ} {x : ℤ} (hb : 2 ∣ b) (ha : a ≥ 4) (ha2 : 2 ∣ a) (hx : 2 ∣ x) :
    2 ^ (padicValNat 2 a + 2) ∣ (b : ℤ) ^ a - x ^ 2 ^ (padicValNat 2 a + 2) := by
  refine dvd_sub ?_ ?_
  · exact Int.dvd_trans (pow_dvd_pow 2 (padicValNat_lemma ha ha2))
      (pow_dvd_pow_of_dvd (ofNat_dvd_right.mpr hb) a)
  · calc
    _ ∣ (2 : ℤ) ^ 2 ^ (padicValNat 2 a + 2) := by
      refine pow_dvd_pow 2 ?_
      calc
      _ < 2 ^ (padicValNat 2 a + 1) := Nat.lt_two_pow_self
      _ ≤ _ := by simp [propext (Nat.pow_le_pow_iff_right le.refl)]
    _ ∣ _ := pow_dvd_pow_of_dvd hx (2 ^ (padicValNat 2 a + 2))

/- To verify the example is a bonza function
-/
lemma bonza_fExample : fExample ∈ bonza := by
  constructor
  · intro a b ha hb
    by_cases ch1 : ¬ 2 ∣ a
    · simp [fExample, ch1]
    by_cases ch2 : a = 2
    · simp [fExample, ch2]
      split_ifs with hb1 hb2
      · grind [sq_mod_four_eq_one_of_odd]
      · simp [hb2]
      · refine dvd_sub ?_ ?_
        · have : 2 ∣ (b : ℤ) := by grind
          simpa using pow_dvd_pow_of_dvd this 2
        · refine Dvd.dvd.pow ?_ (by norm_num)
          use 2 ^ padicValNat 2 b
          ring
    · simp [fExample, ch1, ch2]
      split_ifs with hb1 hb2
      · by_cases lt : b = 1
        · simp [lt]
        have : (padicValNat 2 a + 2) ≤ padicValInt 2 (b ^ a - 1) := by
          rw [← LucasLehmer.Int.natCast_pow_pred b a hb]
          exact LTE_lemma_of_pow_sub (by omega) (Nat.two_dvd_ne_zero.mpr hb1) (by omega)
            (Nat.even_iff.mpr (by simpa using ch1))
        exact Int.dvd_trans (pow_dvd_pow 2 this) (padicValInt_dvd ((b : ℤ) ^ a - 1))
      · grind [verify_case_two_dvd]
      · grind [verify_case_two_dvd]
  · grind [fExample, Nat.two_pow_pos]

theorem apply_le {f : ℕ → ℕ} (hf : f ∈ bonza) {n : ℕ} (hn : 0 < n) : f n ≤ 4 * n := by
  by_cases hnf : ∀ x, x > 0 → f x = x
  · simpa [hnf n hn] using by omega
  · obtain ⟨k, hk⟩ := bonza_not_id_two_pow hf hnf n hn
    rcases Nat.even_or_odd n with ch | ch
    · have apply_dvd_three_pow_sub_one : f n ∣ 3 ^ n - 1 := by
        have eq1 : f 3 = 1 := bonza_apply_prime_gt_two_eq_one hf hnf 3 (by norm_num) prime_three
        have eq2 : (3 : ℤ) ^ n - 1 = (3 ^ n - 1 : ℕ) := by
          have : (3 : ℤ) ^ n = (3 ^ n : ℕ) := by simp
          rw [this, natCast_pred_of_pos]
          exact pos_of_neZero (3 ^ n)
        have := hf.1 n 3 hn (by norm_num)
        rwa [Nat.cast_ofNat, eq1, Nat.cast_one, one_pow, eq2, ofNat_dvd] at this
      rw [hk] at apply_dvd_three_pow_sub_one
      calc
        _ ≤ 2 ^ padicValNat 2 (3 ^ n - 1) := by
          rwa [hk, propext (Nat.pow_le_pow_iff_right Nat.le.refl), ← padicValNat_dvd_iff_le
            (by grind [one_lt_pow])]
        _ = 4 * 2 ^ padicValNat 2 n := by
          have : padicValNat 2 (3 ^ n - 1) + 1 = 3 + padicValNat 2 n := by
            simpa [padicValNat_eq_primeFactorsList_count] using padicValNat.pow_two_sub_pow (x := 3)
              (y := 1) (by norm_num) (by norm_num) (by norm_num) (by omega) ch
          have : padicValNat 2 (3 ^ n - 1) = 2 + padicValNat 2 n := by omega
          rw [congrArg (HPow.hPow 2) this, Nat.pow_add]
        _ ≤ _ := Nat.mul_le_mul_left 4 (Nat.le_of_dvd hn pow_padicValNat_dvd)
    · have : k = 0 := by
        by_contra! nh
        have : Odd (f n) := Odd.of_dvd_nat (Odd.pow ch) (bonza_apply_dvd_pow hf hn)
        rw [hk, propext (odd_pow_iff nh)] at this
        contradiction
      simp [this] at hk
      omega

theorem result : IsLeast {c : ℝ | ∀ f : ℕ → ℕ, f ∈ bonza → ∀ n, 0 < n → f n ≤ c * n} 4 := by
  constructor
  · intro f hf n hn
    have : 4 * (n : ℝ) = (4 * n : ℕ) := by simp
    rw [this, Nat.cast_le]
    exact apply_le hf hn
  · intro c hc
    have : 16 ≤ c * 4 := by
      simpa [fExample, padicValNat_eq_primeFactorsList_count] using
        hc fExample bonza_fExample 4 (by norm_num)
    linarith

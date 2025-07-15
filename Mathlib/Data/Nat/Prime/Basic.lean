/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Defs

/-!
# Prime numbers

This file develops the theory of prime numbers: natural numbers `p ≥ 2` whose only divisors are
`p` and `1`.

-/

open Bool Subtype

open Nat

namespace Nat
variable {n : ℕ}

theorem prime_mul_iff {a b : ℕ} : Nat.Prime (a * b) ↔ a.Prime ∧ b = 1 ∨ b.Prime ∧ a = 1 := by
  simp only [irreducible_mul_iff, ← irreducible_iff_nat_prime, Nat.isUnit_iff]

theorem not_prime_mul {a b : ℕ} (a1 : a ≠ 1) (b1 : b ≠ 1) : ¬Prime (a * b) := by
  simp [prime_mul_iff, _root_.not_or, *]

theorem not_prime_of_mul_eq {a b n : ℕ} (h : a * b = n) (h₁ : a ≠ 1) (h₂ : b ≠ 1) : ¬Prime n :=
  h ▸ not_prime_mul h₁ h₂

@[deprecated (since := "2025-05-24")]
alias not_prime_mul' := not_prime_of_mul_eq

theorem Prime.dvd_iff_eq {p a : ℕ} (hp : p.Prime) (a1 : a ≠ 1) : a ∣ p ↔ p = a := by
  refine ⟨?_, by rintro rfl; rfl⟩
  rintro ⟨j, rfl⟩
  rcases prime_mul_iff.mp hp with (⟨_, rfl⟩ | ⟨_, rfl⟩)
  · exact mul_one _
  · exact (a1 rfl).elim

theorem Prime.eq_two_or_odd {p : ℕ} (hp : Prime p) : p = 2 ∨ p % 2 = 1 :=
  p.mod_two_eq_zero_or_one.imp_left fun h =>
    ((hp.eq_one_or_self_of_dvd 2 (dvd_of_mod_eq_zero h)).resolve_left (by decide)).symm

theorem Prime.eq_two_or_odd' {p : ℕ} (hp : Prime p) : p = 2 ∨ Odd p :=
  Or.imp_right (fun h => ⟨p / 2, (div_add_mod p 2).symm.trans (congr_arg _ h)⟩) hp.eq_two_or_odd

section

theorem Prime.five_le_of_ne_two_of_ne_three {p : ℕ} (hp : p.Prime) (h_two : p ≠ 2)
    (h_three : p ≠ 3) : 5 ≤ p := by
  by_contra! h
  revert h_two h_three hp
  decide +revert

end

theorem Prime.pred_pos {p : ℕ} (pp : Prime p) : 0 < pred p :=
  lt_pred_iff.2 pp.one_lt

theorem succ_pred_prime {p : ℕ} (pp : Prime p) : succ (pred p) = p :=
  succ_pred_eq_of_pos pp.pos

theorem exists_dvd_of_not_prime {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
  ⟨minFac n, minFac_dvd _, ne_of_gt (minFac_prime (ne_of_gt n2)).one_lt,
    ne_of_lt <| (not_prime_iff_minFac_lt n2).1 np⟩

theorem exists_dvd_of_not_prime2 {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) :
    ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
  ⟨minFac n, minFac_dvd _, (minFac_prime (ne_of_gt n2)).two_le,
    (not_prime_iff_minFac_lt n2).1 np⟩

theorem not_prime_of_dvd_of_ne {m n : ℕ} (h1 : m ∣ n) (h2 : m ≠ 1) (h3 : m ≠ n) : ¬Prime n :=
  fun h => Or.elim (h.eq_one_or_self_of_dvd m h1) h2 h3

theorem not_prime_of_dvd_of_lt {m n : ℕ} (h1 : m ∣ n) (h2 : 2 ≤ m) (h3 : m < n) : ¬Prime n :=
  not_prime_of_dvd_of_ne h1 (ne_of_gt h2) (ne_of_lt h3)

theorem not_prime_iff_exists_dvd_ne {n : ℕ} (h : 2 ≤ n) : (¬Prime n) ↔ ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
  ⟨exists_dvd_of_not_prime h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_ne h1 h2 h3⟩

theorem not_prime_iff_exists_dvd_lt {n : ℕ} (h : 2 ≤ n) : (¬Prime n) ↔ ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
  ⟨exists_dvd_of_not_prime2 h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_lt h1 h2 h3⟩

theorem dvd_of_forall_prime_mul_dvd {a b : ℕ}
    (hdvd : ∀ p : ℕ, p.Prime → p ∣ a → p * a ∣ b) : a ∣ b := by
  obtain rfl | ha := eq_or_ne a 1
  · apply one_dvd
  obtain ⟨p, hp⟩ := exists_prime_and_dvd ha
  exact _root_.trans (dvd_mul_left a p) (hdvd p hp.1 hp.2)

theorem Prime.even_iff {p : ℕ} (hp : Prime p) : Even p ↔ p = 2 := by
  rw [even_iff_two_dvd, prime_dvd_prime_iff_eq prime_two hp, eq_comm]

theorem Prime.odd_of_ne_two {p : ℕ} (hp : p.Prime) (h_two : p ≠ 2) : Odd p :=
  hp.eq_two_or_odd'.resolve_left h_two

theorem Prime.even_sub_one {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : Even (p - 1) :=
  let ⟨n, hn⟩ := hp.odd_of_ne_two h2; ⟨n, by rw [hn, Nat.add_sub_cancel, two_mul]⟩

/-- A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`. -/
theorem Prime.mod_two_eq_one_iff_ne_two {p : ℕ} [Fact p.Prime] : p % 2 = 1 ↔ p ≠ 2 := by
  refine ⟨fun h hf => ?_, (Nat.Prime.eq_two_or_odd <| @Fact.out p.Prime _).resolve_left⟩
  rw [hf] at h
  simp at h

theorem coprime_of_dvd' {m n : ℕ} (H : ∀ k, Prime k → k ∣ m → k ∣ n → k ∣ 1) : Coprime m n :=
  coprime_of_dvd fun k kp km kn => not_le_of_gt kp.one_lt <| le_of_dvd Nat.one_pos <| H k kp km kn

theorem Prime.dvd_iff_not_coprime {p n : ℕ} (pp : Prime p) : p ∣ n ↔ ¬Coprime p n :=
  iff_not_comm.2 pp.coprime_iff_not_dvd

theorem Prime.not_coprime_iff_dvd {m n : ℕ} : ¬Coprime m n ↔ ∃ p, Prime p ∧ p ∣ m ∧ p ∣ n := by
  apply Iff.intro
  · intro h
    exact
      ⟨minFac (gcd m n), minFac_prime h, (minFac_dvd (gcd m n)).trans (gcd_dvd_left m n),
        (minFac_dvd (gcd m n)).trans (gcd_dvd_right m n)⟩
  · intro h
    obtain ⟨p, hp⟩ := h
    apply Nat.not_coprime_of_dvd_of_dvd (Prime.one_lt hp.1) hp.2.1 hp.2.2

/-- If `0 < m < minFac n`, then `n` and `m` are coprime. -/
lemma coprime_of_lt_minFac {n m : ℕ} (h₀ : m ≠ 0) (h : m < minFac n) : Coprime n m  := by
  rw [← not_not (a := n.Coprime m), Prime.not_coprime_iff_dvd]
  push_neg
  exact fun p hp hn hm ↦
    ((le_of_dvd (by omega) hm).trans_lt <| h.trans_le <| minFac_le_of_dvd hp.two_le hn).false

/-- If `0 < m < minFac n`, then `n` and `m` have gcd equal to `1`. -/
lemma gcd_eq_one_of_lt_minFac {n m : ℕ} (h₀ : m ≠ 0) (h : m < minFac n) : n.gcd m = 1 :=
  coprime_iff_gcd_eq_one.mp <| coprime_of_lt_minFac h₀ h

theorem Prime.not_dvd_mul {p m n : ℕ} (pp : Prime p) (Hm : ¬p ∣ m) (Hn : ¬p ∣ n) : ¬p ∣ m * n :=
  mt pp.dvd_mul.1 <| by simp [Hm, Hn]

@[simp] lemma coprime_two_left : Coprime 2 n ↔ Odd n := by
  rw [prime_two.coprime_iff_not_dvd, ← not_even_iff_odd, even_iff_two_dvd]

@[simp] lemma coprime_two_right : n.Coprime 2 ↔ Odd n := coprime_comm.trans coprime_two_left

protected alias ⟨Coprime.odd_of_left, _root_.Odd.coprime_two_left⟩ := coprime_two_left
protected alias ⟨Coprime.odd_of_right, _root_.Odd.coprime_two_right⟩ := coprime_two_right

theorem Prime.dvd_of_dvd_pow {p m n : ℕ} (pp : Prime p) (h : p ∣ m ^ n) : p ∣ m :=
  pp.prime.dvd_of_dvd_pow h

theorem Prime.not_prime_pow' {x n : ℕ} (hn : n ≠ 1) : ¬(x ^ n).Prime :=
  not_irreducible_pow hn

theorem Prime.not_prime_pow {x n : ℕ} (hn : 2 ≤ n) : ¬(x ^ n).Prime :=
  not_prime_pow' ((two_le_iff _).mp hn).2

theorem Prime.eq_one_of_pow {x n : ℕ} (h : (x ^ n).Prime) : n = 1 :=
  not_imp_not.mp Prime.not_prime_pow' h

theorem Prime.pow_eq_iff {p a k : ℕ} (hp : p.Prime) : a ^ k = p ↔ a = p ∧ k = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, pow_one]⟩
  rw [← h] at hp
  rw [← h, hp.eq_one_of_pow, eq_self_iff_true, _root_.and_true, pow_one]

theorem Prime.mul_eq_prime_sq_iff {x y p : ℕ} (hp : p.Prime) (hx : x ≠ 1) (hy : y ≠ 1) :
    x * y = p ^ 2 ↔ x = p ∧ y = p := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => h₁.symm ▸ h₂.symm ▸ (sq _).symm⟩
  have pdvdxy : p ∣ x * y := by rw [h]; simp [sq]
  -- Could be `wlog := hp.dvd_mul.1 pdvdxy using x y`, but that imports more than we want.
  suffices ∀ x' y' : ℕ, x' ≠ 1 → y' ≠ 1 → x' * y' = p ^ 2 → p ∣ x' → x' = p ∧ y' = p by
    obtain hx | hy := hp.dvd_mul.1 pdvdxy <;>
      [skip; rw [And.comm]] <;>
      [skip; rw [mul_comm] at h pdvdxy] <;>
      apply this <;>
      assumption
  rintro x y hx hy h ⟨a, ha⟩
  have : a ∣ p := ⟨y, by rwa [ha, sq, mul_assoc, mul_right_inj' hp.ne_zero, eq_comm] at h⟩
  obtain ha1 | hap := (Nat.dvd_prime hp).mp ‹a ∣ p›
  · subst ha1
    rw [mul_one] at ha
    subst ha
    simp only [sq, mul_right_inj' hp.ne_zero] at h
    subst h
    exact ⟨rfl, rfl⟩
  · refine (hy ?_).elim
    subst hap
    subst ha
    rw [sq, Nat.mul_eq_left (Nat.mul_ne_zero hp.ne_zero hp.ne_zero)] at h
    exact h

theorem Prime.coprime_pow_of_not_dvd {p m a : ℕ} (pp : Prime p) (h : ¬p ∣ a) : Coprime a (p ^ m) :=
  (pp.coprime_iff_not_dvd.2 h).symm.pow_right _

theorem coprime_primes {p q : ℕ} (pp : Prime p) (pq : Prime q) : Coprime p q ↔ p ≠ q :=
  pp.coprime_iff_not_dvd.trans <| not_congr <| dvd_prime_two_le pq pp.two_le

theorem coprime_pow_primes {p q : ℕ} (n m : ℕ) (pp : Prime p) (pq : Prime q) (h : p ≠ q) :
    Coprime (p ^ n) (q ^ m) :=
  ((coprime_primes pp pq).2 h).pow _ _

theorem coprime_or_dvd_of_prime {p} (pp : Prime p) (i : ℕ) : Coprime p i ∨ p ∣ i := by
  rw [pp.dvd_iff_not_coprime]; apply em

theorem coprime_of_lt_prime {n p} (n_pos : 0 < n) (hlt : n < p) (pp : Prime p) : Coprime p n :=
  (coprime_or_dvd_of_prime pp n).resolve_right fun h => Nat.lt_le_asymm hlt (le_of_dvd n_pos h)

theorem eq_or_coprime_of_le_prime {n p} (n_pos : 0 < n) (hle : n ≤ p) (pp : Prime p) :
    p = n ∨ Coprime p n :=
  hle.eq_or_lt.imp Eq.symm fun h => coprime_of_lt_prime n_pos h pp

theorem prime_eq_prime_of_dvd_pow {m p q} (pp : Prime p) (pq : Prime q) (h : p ∣ q ^ m) : p = q :=
  (prime_dvd_prime_iff_eq pp pq).mp (pp.dvd_of_dvd_pow h)

theorem dvd_prime_pow {p : ℕ} (pp : Prime p) {m i : ℕ} : i ∣ p ^ m ↔ ∃ k ≤ m, i = p ^ k := by
  simp_rw [_root_.dvd_prime_pow (prime_iff.mp pp) m, associated_eq_eq]

theorem Prime.dvd_mul_of_dvd_ne {p1 p2 n : ℕ} (h_neq : p1 ≠ p2) (pp1 : Prime p1) (pp2 : Prime p2)
    (h1 : p1 ∣ n) (h2 : p2 ∣ n) : p1 * p2 ∣ n :=
  Coprime.mul_dvd_of_dvd_of_dvd ((coprime_primes pp1 pp2).mpr h_neq) h1 h2

/-- If `p` is prime,
and `a` doesn't divide `p^k`, but `a` does divide `p^(k+1)`
then `a = p^(k+1)`.
-/
theorem eq_prime_pow_of_dvd_least_prime_pow {a p k : ℕ} (pp : Prime p) (h₁ : ¬a ∣ p ^ k)
    (h₂ : a ∣ p ^ (k + 1)) : a = p ^ (k + 1) := by
  obtain ⟨l, ⟨h, rfl⟩⟩ := (dvd_prime_pow pp).1 h₂
  congr
  exact le_antisymm h (not_le.1 ((not_congr (pow_dvd_pow_iff_le_right (Prime.one_lt pp))).1 h₁))

theorem ne_one_iff_exists_prime_dvd : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n
  | 0 => by simpa using Exists.intro 2 Nat.prime_two
  | 1 => by simp [Nat.not_prime_one]
  | n + 2 => by
    let a := n + 2
    have ha : a ≠ 1 := Nat.succ_succ_ne_one n
    simp only [a, true_iff, Ne, not_false_iff, ha]
    exact ⟨a.minFac, Nat.minFac_prime ha, a.minFac_dvd⟩

theorem eq_one_iff_not_exists_prime_dvd {n : ℕ} : n = 1 ↔ ∀ p : ℕ, p.Prime → ¬p ∣ n := by
  simpa using not_iff_not.mpr ne_one_iff_exists_prime_dvd

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : Prime p) {m n k l : ℕ}
    (hpm : p ^ k ∣ m) (hpn : p ^ l ∣ n) (hpmn : p ^ (k + l + 1) ∣ m * n) :
    p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n := by
  have hpd : p ^ (k + l) * p ∣ m * n := by
      let hpmn' : p ^ (succ (k + l)) ∣ m * n := hpmn
      rwa [pow_succ'] at hpmn'
  have hpd2 : p ∣ m * n / p ^ (k + l) := dvd_div_of_mul_dvd hpd
  have hpd3 : p ∣ m * n / (p ^ k * p ^ l) := by simpa [pow_add] using hpd2
  have hpd4 : p ∣ m / p ^ k * (n / p ^ l) := by simpa [Nat.div_mul_div_comm hpm hpn] using hpd3
  have hpd5 : p ∣ m / p ^ k ∨ p ∣ n / p ^ l :=
    (Prime.dvd_mul p_prime).1 hpd4
  suffices p ^ k * p ∣ m ∨ p ^ l * p ∣ n by rwa [_root_.pow_succ, _root_.pow_succ]
  exact hpd5.elim (fun h : p ∣ m / p ^ k => Or.inl <| mul_dvd_of_dvd_div hpm h)
    fun h : p ∣ n / p ^ l => Or.inr <| mul_dvd_of_dvd_div hpn h

end Nat

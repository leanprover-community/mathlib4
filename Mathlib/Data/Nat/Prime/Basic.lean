/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Ring.Int
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Bounds.Basic

#align_import data.nat.prime from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
## Notable Theorems

- `Nat.exists_infinite_primes`: Euclid's theorem that there exist infinitely many prime numbers.
  This also appears as `Nat.not_bddAbove_setOf_prime` and `Nat.infinite_setOf_prime` (the latter
  in `Data.Nat.PrimeFin`).

-/


open Bool Subtype

open Nat

namespace Nat
variable {n : ℕ}

section

theorem Prime.five_le_of_ne_two_of_ne_three {p : ℕ} (hp : p.Prime) (h_two : p ≠ 2)
    (h_three : p ≠ 3) : 5 ≤ p := by
  by_contra! h
  revert h_two h_three hp
  -- Porting note (#11043): was `decide!`
  match p with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | n + 5 => exact (h.not_le le_add_self).elim
#align nat.prime.five_le_of_ne_two_of_ne_three Nat.Prime.five_le_of_ne_two_of_ne_three

end

theorem Prime.pred_pos {p : ℕ} (pp : Prime p) : 0 < pred p :=
  lt_pred_iff.2 pp.one_lt
#align nat.prime.pred_pos Nat.Prime.pred_pos

theorem succ_pred_prime {p : ℕ} (pp : Prime p) : succ (pred p) = p :=
  succ_pred_eq_of_pos pp.pos
#align nat.succ_pred_prime Nat.succ_pred_prime

theorem exists_dvd_of_not_prime {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
  ⟨minFac n, minFac_dvd _, ne_of_gt (minFac_prime (ne_of_gt n2)).one_lt,
    ne_of_lt <| (not_prime_iff_minFac_lt n2).1 np⟩
#align nat.exists_dvd_of_not_prime Nat.exists_dvd_of_not_prime

theorem exists_dvd_of_not_prime2 {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) :
    ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
  ⟨minFac n, minFac_dvd _, (minFac_prime (ne_of_gt n2)).two_le,
    (not_prime_iff_minFac_lt n2).1 np⟩
#align nat.exists_dvd_of_not_prime2 Nat.exists_dvd_of_not_prime2

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
#align nat.dvd_of_forall_prime_mul_dvd Nat.dvd_of_forall_prime_mul_dvd

/-- Euclid's theorem on the **infinitude of primes**.
Here given in the form: for every `n`, there exists a prime number `p ≥ n`. -/
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Prime p :=
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Prime p := minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, np, pp⟩
#align nat.exists_infinite_primes Nat.exists_infinite_primes

/-- A version of `Nat.exists_infinite_primes` using the `BddAbove` predicate. -/
theorem not_bddAbove_setOf_prime : ¬BddAbove { p | Prime p } := by
  rw [not_bddAbove_iff]
  intro n
  obtain ⟨p, hi, hp⟩ := exists_infinite_primes n.succ
  exact ⟨p, hp, hi⟩
#align nat.not_bdd_above_set_of_prime Nat.not_bddAbove_setOf_prime

theorem Prime.even_iff {p : ℕ} (hp : Prime p) : Even p ↔ p = 2 := by
  rw [even_iff_two_dvd, prime_dvd_prime_iff_eq prime_two hp, eq_comm]
#align nat.prime.even_iff Nat.Prime.even_iff

theorem Prime.odd_of_ne_two {p : ℕ} (hp : p.Prime) (h_two : p ≠ 2) : Odd p :=
  hp.eq_two_or_odd'.resolve_left h_two
#align nat.prime.odd_of_ne_two Nat.Prime.odd_of_ne_two

theorem Prime.even_sub_one {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : Even (p - 1) :=
  let ⟨n, hn⟩ := hp.odd_of_ne_two h2; ⟨n, by rw [hn, Nat.add_sub_cancel, two_mul]⟩
#align nat.prime.even_sub_one Nat.Prime.even_sub_one

/-- A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`. -/
theorem Prime.mod_two_eq_one_iff_ne_two {p : ℕ} [Fact p.Prime] : p % 2 = 1 ↔ p ≠ 2 := by
  refine ⟨fun h hf => ?_, (Nat.Prime.eq_two_or_odd <| @Fact.out p.Prime _).resolve_left⟩
  rw [hf] at h
  simp at h
#align nat.prime.mod_two_eq_one_iff_ne_two Nat.Prime.mod_two_eq_one_iff_ne_two

theorem coprime_of_dvd' {m n : ℕ} (H : ∀ k, Prime k → k ∣ m → k ∣ n → k ∣ 1) : Coprime m n :=
  coprime_of_dvd fun k kp km kn => not_le_of_gt kp.one_lt <| le_of_dvd zero_lt_one <| H k kp km kn
#align nat.coprime_of_dvd' Nat.coprime_of_dvd'

theorem Prime.dvd_iff_not_coprime {p n : ℕ} (pp : Prime p) : p ∣ n ↔ ¬Coprime p n :=
  iff_not_comm.2 pp.coprime_iff_not_dvd
#align nat.prime.dvd_iff_not_coprime Nat.Prime.dvd_iff_not_coprime

theorem Prime.not_coprime_iff_dvd {m n : ℕ} : ¬Coprime m n ↔ ∃ p, Prime p ∧ p ∣ m ∧ p ∣ n := by
  apply Iff.intro
  · intro h
    exact
      ⟨minFac (gcd m n), minFac_prime h, (minFac_dvd (gcd m n)).trans (gcd_dvd_left m n),
        (minFac_dvd (gcd m n)).trans (gcd_dvd_right m n)⟩
  · intro h
    cases' h with p hp
    apply Nat.not_coprime_of_dvd_of_dvd (Prime.one_lt hp.1) hp.2.1 hp.2.2
#align nat.prime.not_coprime_iff_dvd Nat.Prime.not_coprime_iff_dvd

theorem Prime.not_dvd_mul {p m n : ℕ} (pp : Prime p) (Hm : ¬p ∣ m) (Hn : ¬p ∣ n) : ¬p ∣ m * n :=
  mt pp.dvd_mul.1 <| by simp [Hm, Hn]
#align nat.prime.not_dvd_mul Nat.Prime.not_dvd_mul

@[simp] lemma coprime_two_left : Coprime 2 n ↔ Odd n := by
  rw [prime_two.coprime_iff_not_dvd, odd_iff_not_even, even_iff_two_dvd]

@[simp] lemma coprime_two_right : n.Coprime 2 ↔ Odd n := coprime_comm.trans coprime_two_left

alias ⟨Coprime.odd_of_left, _root_.Odd.coprime_two_left⟩ := coprime_two_left
alias ⟨Coprime.odd_of_right, _root_.Odd.coprime_two_right⟩ := coprime_two_right

-- Porting note: attributes `protected`, `nolint dup_namespace` removed

theorem Prime.dvd_of_dvd_pow {p m n : ℕ} (pp : Prime p) (h : p ∣ m ^ n) : p ∣ m :=
  pp.prime.dvd_of_dvd_pow h
#align nat.prime.dvd_of_dvd_pow Nat.Prime.dvd_of_dvd_pow

theorem Prime.not_prime_pow' {x n : ℕ} (hn : n ≠ 1) : ¬(x ^ n).Prime :=
  not_irreducible_pow hn
#align nat.prime.pow_not_prime' Nat.Prime.not_prime_pow'

theorem Prime.not_prime_pow {x n : ℕ} (hn : 2 ≤ n) : ¬(x ^ n).Prime :=
  not_prime_pow' ((two_le_iff _).mp hn).2
#align nat.prime.pow_not_prime Nat.Prime.not_prime_pow

theorem Prime.eq_one_of_pow {x n : ℕ} (h : (x ^ n).Prime) : n = 1 :=
  not_imp_not.mp Prime.not_prime_pow' h
#align nat.prime.eq_one_of_pow Nat.Prime.eq_one_of_pow

theorem Prime.pow_eq_iff {p a k : ℕ} (hp : p.Prime) : a ^ k = p ↔ a = p ∧ k = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, pow_one]⟩
  rw [← h] at hp
  rw [← h, hp.eq_one_of_pow, eq_self_iff_true, and_true_iff, pow_one]
#align nat.prime.pow_eq_iff Nat.Prime.pow_eq_iff

theorem pow_minFac {n k : ℕ} (hk : k ≠ 0) : (n ^ k).minFac = n.minFac := by
  rcases eq_or_ne n 1 with (rfl | hn)
  · simp
  have hnk : n ^ k ≠ 1 := fun hk' => hn ((pow_eq_one_iff hk).1 hk')
  apply (minFac_le_of_dvd (minFac_prime hn).two_le ((minFac_dvd n).pow hk)).antisymm
  apply
    minFac_le_of_dvd (minFac_prime hnk).two_le
      ((minFac_prime hnk).dvd_of_dvd_pow (minFac_dvd _))
#align nat.pow_min_fac Nat.pow_minFac

theorem Prime.pow_minFac {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : (p ^ k).minFac = p := by
  rw [Nat.pow_minFac hk, hp.minFac_eq]
#align nat.prime.pow_min_fac Nat.Prime.pow_minFac

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
    rw [sq, Nat.mul_right_eq_self_iff (Nat.mul_pos hp.pos hp.pos : 0 < a * a)] at h
    exact h
#align nat.prime.mul_eq_prime_sq_iff Nat.Prime.mul_eq_prime_sq_iff

theorem Prime.dvd_factorial : ∀ {n p : ℕ} (_ : Prime p), p ∣ n ! ↔ p ≤ n
  | 0, p, hp => iff_of_false hp.not_dvd_one (not_le_of_lt hp.pos)
  | n + 1, p, hp => by
    rw [factorial_succ, hp.dvd_mul, Prime.dvd_factorial hp]
    exact
      ⟨fun h => h.elim (le_of_dvd (succ_pos _)) le_succ_of_le, fun h =>
        (_root_.lt_or_eq_of_le h).elim (Or.inr ∘ le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩
#align nat.prime.dvd_factorial Nat.Prime.dvd_factorial

theorem Prime.coprime_pow_of_not_dvd {p m a : ℕ} (pp : Prime p) (h : ¬p ∣ a) : Coprime a (p ^ m) :=
  (pp.coprime_iff_not_dvd.2 h).symm.pow_right _
#align nat.prime.coprime_pow_of_not_dvd Nat.Prime.coprime_pow_of_not_dvd

theorem coprime_primes {p q : ℕ} (pp : Prime p) (pq : Prime q) : Coprime p q ↔ p ≠ q :=
  pp.coprime_iff_not_dvd.trans <| not_congr <| dvd_prime_two_le pq pp.two_le
#align nat.coprime_primes Nat.coprime_primes

theorem coprime_pow_primes {p q : ℕ} (n m : ℕ) (pp : Prime p) (pq : Prime q) (h : p ≠ q) :
    Coprime (p ^ n) (q ^ m) :=
  ((coprime_primes pp pq).2 h).pow _ _
#align nat.coprime_pow_primes Nat.coprime_pow_primes

theorem coprime_or_dvd_of_prime {p} (pp : Prime p) (i : ℕ) : Coprime p i ∨ p ∣ i := by
  rw [pp.dvd_iff_not_coprime]; apply em
#align nat.coprime_or_dvd_of_prime Nat.coprime_or_dvd_of_prime

theorem coprime_of_lt_prime {n p} (n_pos : 0 < n) (hlt : n < p) (pp : Prime p) : Coprime p n :=
  (coprime_or_dvd_of_prime pp n).resolve_right fun h => Nat.lt_le_asymm hlt (le_of_dvd n_pos h)
#align nat.coprime_of_lt_prime Nat.coprime_of_lt_prime

theorem eq_or_coprime_of_le_prime {n p} (n_pos : 0 < n) (hle : n ≤ p) (pp : Prime p) :
    p = n ∨ Coprime p n :=
  hle.eq_or_lt.imp Eq.symm fun h => coprime_of_lt_prime n_pos h pp
#align nat.eq_or_coprime_of_le_prime Nat.eq_or_coprime_of_le_prime

theorem dvd_prime_pow {p : ℕ} (pp : Prime p) {m i : ℕ} : i ∣ p ^ m ↔ ∃ k ≤ m, i = p ^ k := by
  simp_rw [_root_.dvd_prime_pow (prime_iff.mp pp) m, associated_eq_eq]
#align nat.dvd_prime_pow Nat.dvd_prime_pow

theorem Prime.dvd_mul_of_dvd_ne {p1 p2 n : ℕ} (h_neq : p1 ≠ p2) (pp1 : Prime p1) (pp2 : Prime p2)
    (h1 : p1 ∣ n) (h2 : p2 ∣ n) : p1 * p2 ∣ n :=
  Coprime.mul_dvd_of_dvd_of_dvd ((coprime_primes pp1 pp2).mpr h_neq) h1 h2
#align nat.prime.dvd_mul_of_dvd_ne Nat.Prime.dvd_mul_of_dvd_ne

/-- If `p` is prime,
and `a` doesn't divide `p^k`, but `a` does divide `p^(k+1)`
then `a = p^(k+1)`.
-/
theorem eq_prime_pow_of_dvd_least_prime_pow {a p k : ℕ} (pp : Prime p) (h₁ : ¬a ∣ p ^ k)
    (h₂ : a ∣ p ^ (k + 1)) : a = p ^ (k + 1) := by
  obtain ⟨l, ⟨h, rfl⟩⟩ := (dvd_prime_pow pp).1 h₂
  congr
  exact le_antisymm h (not_le.1 ((not_congr (pow_dvd_pow_iff_le_right (Prime.one_lt pp))).1 h₁))
#align nat.eq_prime_pow_of_dvd_least_prime_pow Nat.eq_prime_pow_of_dvd_least_prime_pow

theorem ne_one_iff_exists_prime_dvd : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n
  | 0 => by simpa using Exists.intro 2 Nat.prime_two
  | 1 => by simp [Nat.not_prime_one]
  | n + 2 => by
    let a := n + 2
    let ha : a ≠ 1 := Nat.succ_succ_ne_one n
    simp only [true_iff_iff, Ne, not_false_iff, ha]
    exact ⟨a.minFac, Nat.minFac_prime ha, a.minFac_dvd⟩
#align nat.ne_one_iff_exists_prime_dvd Nat.ne_one_iff_exists_prime_dvd

theorem eq_one_iff_not_exists_prime_dvd {n : ℕ} : n = 1 ↔ ∀ p : ℕ, p.Prime → ¬p ∣ n := by
  simpa using not_iff_not.mpr ne_one_iff_exists_prime_dvd
#align nat.eq_one_iff_not_exists_prime_dvd Nat.eq_one_iff_not_exists_prime_dvd

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
#align nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul

theorem prime_iff_prime_int {p : ℕ} : p.Prime ↔ _root_.Prime (p : ℤ) :=
  ⟨fun hp =>
    ⟨Int.natCast_ne_zero_iff_pos.2 hp.pos, mt Int.isUnit_iff_natAbs_eq.1 hp.ne_one, fun a b h => by
      rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast, Int.natAbs_mul, hp.dvd_mul] at h
      rwa [← Int.dvd_natAbs, Int.natCast_dvd_natCast, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]⟩,
    fun hp =>
    Nat.prime_iff.2
      ⟨Int.natCast_ne_zero.1 hp.1,
        (mt Nat.isUnit_iff.1) fun h => by simp [h, not_prime_one] at hp, fun a b => by
        simpa only [Int.natCast_dvd_natCast, (Int.ofNat_mul _ _).symm] using hp.2.2 a b⟩⟩
#align nat.prime_iff_prime_int Nat.prime_iff_prime_int

/-- Two prime powers with positive exponents are equal only when the primes and the
exponents are equal. -/
lemma Prime.pow_inj {p q m n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ^ (m + 1) = q ^ (n + 1)) : p = q ∧ m = n := by
  have H := dvd_antisymm (Prime.dvd_of_dvd_pow hp <| h ▸ dvd_pow_self p (succ_ne_zero m))
    (Prime.dvd_of_dvd_pow hq <| h.symm ▸ dvd_pow_self q (succ_ne_zero n))
  exact ⟨H, succ_inj'.mp <| Nat.pow_right_injective hq.two_le (H ▸ h)⟩

theorem exists_pow_lt_factorial (c : ℕ) : ∃ n0 > 1, ∀ n ≥ n0, c ^ n < (n - 1)! := by
  refine ⟨2 * (c ^ 2 + 1), ?_, ?_⟩
  · omega
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain (rfl | c0) := c.eq_zero_or_pos
  · simp [Nat.factorial_pos]
  refine (Nat.le_mul_of_pos_right _ (pow_pos c0 d)).trans_lt ?_
  convert_to (c ^ 2) ^ (c ^ 2 + d + 1) < (c ^ 2 + (c ^ 2 + d + 1))!
  · rw [← pow_mul, ← pow_add]
    congr 1
    omega
  · congr
    omega
  refine lt_of_lt_of_le ?_ Nat.factorial_mul_pow_le_factorial
  rw [← one_mul (_ ^ _ : ℕ)]
  exact Nat.mul_lt_mul_of_le_of_lt (Nat.one_le_of_lt (Nat.factorial_pos _))
    (Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.succ_ne_zero _)) (Nat.factorial_pos _)

theorem exists_mul_pow_lt_factorial (a : ℕ) (c : ℕ) : ∃ n0, ∀ n ≥ n0, a * c ^ n < (n - 1)! := by
  obtain ⟨n0, hn, h⟩ := Nat.exists_pow_lt_factorial (a * c)
  refine ⟨n0, fun n hn => lt_of_le_of_lt ?_ (h n hn)⟩
  rw [mul_pow]
  refine Nat.mul_le_mul_right _ (Nat.le_self_pow ?_ _)
  omega

theorem exists_prime_mul_pow_lt_factorial (n a c : ℕ) : ∃ p > n, p.Prime ∧ a * c ^ p < (p - 1)! :=
  have ⟨n0, h⟩ := Nat.exists_mul_pow_lt_factorial a c
  have ⟨p, hp, prime_p⟩ := (max (n + 1) n0).exists_infinite_primes
  ⟨p, (le_max_left _ _).trans hp, prime_p, h _ <| le_of_max_le_right hp⟩

end Nat

namespace Int

theorem prime_two : Prime (2 : ℤ) :=
  Nat.prime_iff_prime_int.mp Nat.prime_two
#align int.prime_two Int.prime_two

theorem prime_three : Prime (3 : ℤ) :=
  Nat.prime_iff_prime_int.mp Nat.prime_three
#align int.prime_three Int.prime_three

end Int

/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Associated.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.Basic

/-!
# Prime numbers

This file deals with prime numbers: natural numbers `p ≥ 2` whose only divisors are `p` and `1`.

## Important declarations

- `Nat.Prime`: the predicate that expresses that a natural number `p` is prime
- `Nat.Primes`: the subtype of natural numbers that are prime
- `Nat.minFac n`: the minimal prime factor of a natural number `n ≠ 1`
- `Nat.prime_iff`: `Nat.Prime` coincides with the general definition of `Prime`
- `Nat.irreducible_iff_nat_prime`: a non-unit natural number is
                                  only divisible by `1` iff it is prime

-/

open Bool Subtype

open Nat

namespace Nat
variable {n : ℕ}

/-- `Nat.Prime p` means that `p` is a prime number, that is, a natural number
  at least 2 whose only divisors are `p` and `1`. -/
@[pp_nodot]
def Prime (p : ℕ) :=
  Irreducible p

theorem irreducible_iff_nat_prime (a : ℕ) : Irreducible a ↔ Nat.Prime a :=
  Iff.rfl

@[aesop safe destruct] theorem not_prime_zero : ¬Prime 0
  | h => h.ne_zero rfl

@[aesop safe destruct] theorem not_prime_one : ¬Prime 1
  | h => h.ne_one rfl

theorem Prime.ne_zero {n : ℕ} (h : Prime n) : n ≠ 0 :=
  Irreducible.ne_zero h

theorem Prime.pos {p : ℕ} (pp : Prime p) : 0 < p :=
  Nat.pos_of_ne_zero pp.ne_zero

theorem Prime.two_le : ∀ {p : ℕ}, Prime p → 2 ≤ p
  | 0, h => (not_prime_zero h).elim
  | 1, h => (not_prime_one h).elim
  | _ + 2, _ => le_add_left 2 _

theorem Prime.one_lt {p : ℕ} : Prime p → 1 < p :=
  Prime.two_le

lemma Prime.one_le {p : ℕ} (hp : p.Prime) : 1 ≤ p := hp.one_lt.le

instance Prime.one_lt' (p : ℕ) [hp : Fact p.Prime] : Fact (1 < p) :=
  ⟨hp.1.one_lt⟩

theorem Prime.ne_one {p : ℕ} (hp : p.Prime) : p ≠ 1 :=
  hp.one_lt.ne'

theorem Prime.eq_one_or_self_of_dvd {p : ℕ} (pp : p.Prime) (m : ℕ) (hm : m ∣ p) :
    m = 1 ∨ m = p := by
  obtain ⟨n, hn⟩ := hm
  have := pp.isUnit_or_isUnit hn
  rw [Nat.isUnit_iff, Nat.isUnit_iff] at this
  apply Or.imp_right _ this
  rintro rfl
  rw [hn, mul_one]

theorem prime_def_lt'' {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p := by
  refine ⟨fun h => ⟨h.two_le, h.eq_one_or_self_of_dvd⟩, fun h => ?_⟩
  have h1 := Nat.one_lt_two.trans_le h.1
  refine ⟨mt Nat.isUnit_iff.mp h1.ne', fun a b hab => ?_⟩
  simp only [Nat.isUnit_iff]
  apply Or.imp_right _ (h.2 a _)
  · rintro rfl
    rw [← mul_right_inj' (not_eq_zero_of_lt h1), ← hab, mul_one]
  · rw [hab]
    exact dvd_mul_right _ _

theorem prime_def_lt {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1 :=
  prime_def_lt''.trans <|
    and_congr_right fun p2 =>
      forall_congr' fun _ =>
        ⟨fun h l d => (h d).resolve_right (ne_of_lt l), fun h d =>
          (le_of_dvd (le_of_succ_le p2) d).lt_or_eq_dec.imp_left fun l => h l d⟩

theorem prime_def_lt' {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m < p → ¬m ∣ p :=
  prime_def_lt.trans <|
    and_congr_right fun p2 =>
      forall_congr' fun m =>
        ⟨fun h m2 l d => not_lt_of_ge m2 ((h l d).symm ▸ by decide), fun h l d => by
          rcases m with (_ | _ | m)
          · rw [eq_zero_of_zero_dvd d] at p2
            revert p2
            decide
          · rfl
          · exact (h (le_add_left 2 m) l).elim d⟩

theorem prime_def_le_sqrt {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m ≤ sqrt p → ¬m ∣ p :=
  prime_def_lt'.trans <|
    and_congr_right fun p2 =>
      ⟨fun a m m2 l => a m m2 <| lt_of_le_of_lt l <| sqrt_lt_self p2, fun a =>
        have : ∀ {m k : ℕ}, m ≤ k → 1 < m → p ≠ m * k := fun {m k} mk m1 e =>
          a m m1 (le_sqrt.2 (e.symm ▸ Nat.mul_le_mul_left m mk)) ⟨k, e⟩
        fun m m2 l ⟨k, e⟩ => by
        rcases le_total m k with mk | km
        · exact this mk m2 e
        · rw [mul_comm] at e
          refine this km (Nat.lt_of_mul_lt_mul_right (a := m) ?_) e
          rwa [one_mul, ← e]⟩

theorem prime_of_coprime (n : ℕ) (h1 : 1 < n) (h : ∀ m < n, m ≠ 0 → n.Coprime m) : Prime n := by
  refine prime_def_lt.mpr ⟨h1, fun m mlt mdvd => ?_⟩
  have hm : m ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at mdvd
    exact mlt.ne' mdvd
  exact (h m mlt hm).symm.eq_one_of_dvd mdvd

section

/-- This instance is slower than the instance `decidablePrime` defined below,
  but has the advantage that it works in the kernel for small values.

  If you need to prove that a particular number is prime, in any case
  you should not use `by decide`, but rather `by norm_num`, which is
  much faster.
  -/
@[local instance]
def decidablePrime1 (p : ℕ) : Decidable (Prime p) :=
  decidable_of_iff' _ prime_def_lt'

theorem prime_two : Prime 2 := by decide

theorem prime_three : Prime 3 := by decide

theorem prime_five : Prime 5 := by decide

end

theorem dvd_prime {p m : ℕ} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m = p :=
  ⟨fun d => pp.eq_one_or_self_of_dvd m d, fun h =>
    h.elim (fun e => e.symm ▸ one_dvd _) fun e => e.symm ▸ dvd_rfl⟩

theorem dvd_prime_two_le {p m : ℕ} (pp : Prime p) (H : 2 ≤ m) : m ∣ p ↔ m = p :=
  (dvd_prime pp).trans <| or_iff_right_of_imp <| Not.elim <| ne_of_gt H

theorem prime_dvd_prime_iff_eq {p q : ℕ} (pp : p.Prime) (qp : q.Prime) : p ∣ q ↔ p = q :=
  dvd_prime_two_le qp (Prime.two_le pp)

theorem Prime.not_dvd_one {p : ℕ} (pp : Prime p) : ¬p ∣ 1 :=
  Irreducible.not_dvd_one pp

theorem prime_mul_iff {a b : ℕ} : Nat.Prime (a * b) ↔ a.Prime ∧ b = 1 ∨ b.Prime ∧ a = 1 := by
  simp only [iff_self_iff, irreducible_mul_iff, ← irreducible_iff_nat_prime, Nat.isUnit_iff]

theorem not_prime_mul {a b : ℕ} (a1 : a ≠ 1) (b1 : b ≠ 1) : ¬Prime (a * b) := by
  simp [prime_mul_iff, _root_.not_or, *]

theorem not_prime_mul' {a b n : ℕ} (h : a * b = n) (h₁ : a ≠ 1) (h₂ : b ≠ 1) : ¬Prime n :=
  h ▸ not_prime_mul h₁ h₂

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

section MinFac

theorem minFac_lemma (n k : ℕ) (h : ¬n < k * k) : sqrt n - k < sqrt n + 2 - k :=
  (Nat.sub_lt_sub_right <| le_sqrt.2 <| le_of_not_gt h) <| Nat.lt_add_of_pos_right (by decide)

/--
If `n < k * k`, then `minFacAux n k = n`, if `k | n`, then `minFacAux n k = k`.
Otherwise, `minFacAux n k = minFacAux n (k+2)` using well-founded recursion.
If `n` is odd and `1 < n`, then `minFacAux n 3` is the smallest prime factor of `n`.

By default this well-founded recursion would be irreducible.
This prevents use `decide` to resolve `Nat.prime n` for small values of `n`,
so we mark this as `@[semireducible]`.

In future, we may want to remove this annotation and instead use `norm_num` instead of `decide`
in these situations.
-/
@[semireducible] def minFacAux (n : ℕ) : ℕ → ℕ
  | k =>
    if n < k * k then n
    else
      if k ∣ n then k
      else
        minFacAux n (k + 2)
termination_by k => sqrt n + 2 - k
decreasing_by simp_wf; apply minFac_lemma n k; assumption

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def minFac (n : ℕ) : ℕ :=
  if 2 ∣ n then 2 else minFacAux n 3

@[simp]
theorem minFac_zero : minFac 0 = 2 :=
  rfl

@[simp]
theorem minFac_one : minFac 1 = 1 := by
  simp [minFac, minFacAux]

@[simp]
theorem minFac_two : minFac 2 = 2 := by
  simp [minFac, minFacAux]

theorem minFac_eq (n : ℕ) : minFac n = if 2 ∣ n then 2 else minFacAux n 3 := rfl

private def minFacProp (n k : ℕ) :=
  2 ≤ k ∧ k ∣ n ∧ ∀ m, 2 ≤ m → m ∣ n → k ≤ m

theorem minFacAux_has_prop {n : ℕ} (n2 : 2 ≤ n) :
    ∀ k i, k = 2 * i + 3 → (∀ m, 2 ≤ m → m ∣ n → k ≤ m) → minFacProp n (minFacAux n k)
  | k => fun i e a => by
    rw [minFacAux]
    by_cases h : n < k * k
    · have pp : Prime n :=
        prime_def_le_sqrt.2
          ⟨n2, fun m m2 l d => not_lt_of_ge l <| lt_of_lt_of_le (sqrt_lt.2 h) (a m m2 d)⟩
      simpa [h] using ⟨n2, dvd_rfl, fun m m2 d => le_of_eq ((dvd_prime_two_le pp m2).1 d).symm⟩
    have k2 : 2 ≤ k := by
      subst e
      apply Nat.le_add_left
    simp only [h, ↓reduceIte]
    by_cases dk : k ∣ n <;> simp only [dk, ↓reduceIte]
    · exact ⟨k2, dk, a⟩
    · refine
        have := minFac_lemma n k h
        minFacAux_has_prop n2 (k + 2) (i + 1) (by simp [k, e, left_distrib, add_right_comm])
          fun m m2 d => ?_
      rcases Nat.eq_or_lt_of_le (a m m2 d) with me | ml
      · subst me
        contradiction
      apply (Nat.eq_or_lt_of_le ml).resolve_left
      intro me
      rw [← me, e] at d
      have d' : 2 * (i + 2) ∣ n := d
      have := a _ le_rfl (dvd_of_mul_right_dvd d')
      rw [e] at this
      exact absurd this (by contradiction)
  termination_by k => sqrt n + 2 - k

theorem minFac_has_prop {n : ℕ} (n1 : n ≠ 1) : minFacProp n (minFac n) := by
  by_cases n0 : n = 0
  · simp [n0, minFacProp, GE.ge]
  have n2 : 2 ≤ n := by
    revert n0 n1
    rcases n with (_ | _ | _) <;> simp [succ_le_succ]
  simp only [minFac_eq, Nat.isUnit_iff]
  by_cases d2 : 2 ∣ n <;> simp only [d2, ↓reduceIte]
  · exact ⟨le_rfl, d2, fun k k2 _ => k2⟩
  · refine
      minFacAux_has_prop n2 3 0 rfl fun m m2 d => (Nat.eq_or_lt_of_le m2).resolve_left (mt ?_ d2)
    exact fun e => e.symm ▸ d

theorem minFac_dvd (n : ℕ) : minFac n ∣ n :=
  if n1 : n = 1 then by simp [n1] else (minFac_has_prop n1).2.1

theorem minFac_prime {n : ℕ} (n1 : n ≠ 1) : Prime (minFac n) :=
  let ⟨f2, fd, a⟩ := minFac_has_prop n1
  prime_def_lt'.2 ⟨f2, fun m m2 l d => not_le_of_gt l (a m m2 (d.trans fd))⟩

theorem minFac_le_of_dvd {n : ℕ} : ∀ {m : ℕ}, 2 ≤ m → m ∣ n → minFac n ≤ m := by
  by_cases n1 : n = 1
  · exact fun m2 _ => n1.symm ▸ le_trans (by simp) m2
  · apply (minFac_has_prop n1).2.2

theorem minFac_pos (n : ℕ) : 0 < minFac n := by
  by_cases n1 : n = 1
  · simp [n1]
  · exact (minFac_prime n1).pos

theorem minFac_le {n : ℕ} (H : 0 < n) : minFac n ≤ n :=
  le_of_dvd H (minFac_dvd n)

theorem le_minFac {m n : ℕ} : n = 1 ∨ m ≤ minFac n ↔ ∀ p, Prime p → p ∣ n → m ≤ p :=
  ⟨fun h p pp d =>
    h.elim (by rintro rfl; cases pp.not_dvd_one d) fun h =>
      le_trans h <| minFac_le_of_dvd pp.two_le d,
    fun H => or_iff_not_imp_left.2 fun n1 => H _ (minFac_prime n1) (minFac_dvd _)⟩

theorem le_minFac' {m n : ℕ} : n = 1 ∨ m ≤ minFac n ↔ ∀ p, 2 ≤ p → p ∣ n → m ≤ p :=
  ⟨fun h p (pp : 1 < p) d =>
    h.elim (by rintro rfl; cases not_le_of_lt pp (le_of_dvd (by decide) d)) fun h =>
      le_trans h <| minFac_le_of_dvd pp d,
    fun H => le_minFac.2 fun p pp d => H p pp.two_le d⟩

theorem prime_def_minFac {p : ℕ} : Prime p ↔ 2 ≤ p ∧ minFac p = p :=
  ⟨fun pp =>
    ⟨pp.two_le,
      let ⟨f2, fd, _⟩ := minFac_has_prop <| ne_of_gt pp.one_lt
      ((dvd_prime pp).1 fd).resolve_left (ne_of_gt f2)⟩,
    fun ⟨p2, e⟩ => e ▸ minFac_prime (ne_of_gt p2)⟩

@[simp]
theorem Prime.minFac_eq {p : ℕ} (hp : Prime p) : minFac p = p :=
  (prime_def_minFac.1 hp).2

/-- This instance is faster in the virtual machine than `decidablePrime1`,
but slower in the kernel.

If you need to prove that a particular number is prime, in any case
you should not use `by decide`, but rather `by norm_num`, which is
much faster.
-/
instance decidablePrime (p : ℕ) : Decidable (Prime p) :=
  decidable_of_iff' _ prime_def_minFac

theorem not_prime_iff_minFac_lt {n : ℕ} (n2 : 2 ≤ n) : ¬Prime n ↔ minFac n < n :=
  (not_congr <| prime_def_minFac.trans <| and_iff_right n2).trans <|
    (lt_iff_le_and_ne.trans <| and_iff_right <| minFac_le <| le_of_succ_le n2).symm

theorem minFac_le_div {n : ℕ} (pos : 0 < n) (np : ¬Prime n) : minFac n ≤ n / minFac n :=
  match minFac_dvd n with
  | ⟨0, h0⟩ => absurd pos <| by rw [h0, mul_zero]; decide
  | ⟨1, h1⟩ => by
    rw [mul_one] at h1
    rw [prime_def_minFac, not_and_or, ← h1, eq_self_iff_true, _root_.not_true, or_false_iff,
      not_le] at np
    rw [le_antisymm (le_of_lt_succ np) (succ_le_of_lt pos), minFac_one, Nat.div_one]
  | ⟨x + 2, hx⟩ => by
    conv_rhs =>
      congr
      rw [hx]
    rw [Nat.mul_div_cancel_left _ (minFac_pos _)]
    exact minFac_le_of_dvd (le_add_left 2 x) ⟨minFac n, by rwa [mul_comm]⟩

/-- The square of the smallest prime factor of a composite number `n` is at most `n`.
-/
theorem minFac_sq_le_self {n : ℕ} (w : 0 < n) (h : ¬Prime n) : minFac n ^ 2 ≤ n :=
  have t : minFac n ≤ n / minFac n := minFac_le_div w h
  calc
    minFac n ^ 2 = minFac n * minFac n := sq (minFac n)
    _ ≤ n / minFac n * minFac n := Nat.mul_le_mul_right (minFac n) t
    _ ≤ n := div_mul_le_self n (minFac n)

@[simp]
theorem minFac_eq_one_iff {n : ℕ} : minFac n = 1 ↔ n = 1 := by
  constructor
  · intro h
    by_contra hn
    have := minFac_prime hn
    rw [h] at this
    exact not_prime_one this
  · rintro rfl
    rfl

@[simp]
theorem minFac_eq_two_iff (n : ℕ) : minFac n = 2 ↔ 2 ∣ n := by
  constructor
  · intro h
    rw [← h]
    exact minFac_dvd n
  · intro h
    have ub := minFac_le_of_dvd (le_refl 2) h
    have lb := minFac_pos n
    refine ub.eq_or_lt.resolve_right fun h' => ?_
    have := le_antisymm (Nat.succ_le_of_lt lb) (Nat.lt_succ_iff.mp h')
    rw [eq_comm, Nat.minFac_eq_one_iff] at this
    subst this
    exact not_lt_of_le (le_of_dvd lb h) h'

theorem factors_lemma {k} : (k + 2) / minFac (k + 2) < k + 2 :=
  div_lt_self (Nat.zero_lt_succ _) (minFac_prime (by
      apply Nat.ne_of_gt
      apply Nat.succ_lt_succ
      apply Nat.zero_lt_succ
      )).one_lt

end MinFac

theorem exists_prime_and_dvd {n : ℕ} (hn : n ≠ 1) : ∃ p, Prime p ∧ p ∣ n :=
  ⟨minFac n, minFac_prime hn, minFac_dvd _⟩

theorem coprime_of_dvd {m n : ℕ} (H : ∀ k, Prime k → k ∣ m → ¬k ∣ n) : Coprime m n := by
  rw [coprime_iff_gcd_eq_one]
  by_contra g2
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2
  apply H p hp <;> apply dvd_trans hpdvd
  · exact gcd_dvd_left _ _
  · exact gcd_dvd_right _ _

theorem Prime.coprime_iff_not_dvd {p n : ℕ} (pp : Prime p) : Coprime p n ↔ ¬p ∣ n :=
  ⟨fun co d => pp.not_dvd_one <| co.dvd_of_dvd_mul_left (by simp [d]), fun nd =>
    coprime_of_dvd fun m m2 mp => ((prime_dvd_prime_iff_eq m2 pp).1 mp).symm ▸ nd⟩

theorem Prime.dvd_mul {p m n : ℕ} (pp : Prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=
  ⟨fun H => or_iff_not_imp_left.2 fun h => (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
    Or.rec (fun h : p ∣ m => h.mul_right _) fun h : p ∣ n => h.mul_left _⟩

theorem prime_iff {p : ℕ} : p.Prime ↔ _root_.Prime p :=
  ⟨fun h => ⟨h.ne_zero, h.not_unit, fun _ _ => h.dvd_mul.mp⟩, Prime.irreducible⟩

alias ⟨Prime.prime, _root_.Prime.nat_prime⟩ := prime_iff

theorem irreducible_iff_prime {p : ℕ} : Irreducible p ↔ _root_.Prime p :=
  prime_iff

/-- The type of prime numbers -/
def Primes :=
  { p : ℕ // p.Prime }
  deriving DecidableEq

namespace Primes

instance : Repr Nat.Primes :=
  ⟨fun p _ => repr p.val⟩

instance inhabitedPrimes : Inhabited Primes :=
  ⟨⟨2, prime_two⟩⟩

instance coeNat : Coe Nat.Primes ℕ :=
  ⟨Subtype.val⟩

-- Porting note: change in signature to match change in coercion
theorem coe_nat_injective : Function.Injective (fun (a : Nat.Primes) ↦ (a : ℕ)) :=
  Subtype.coe_injective

theorem coe_nat_inj (p q : Nat.Primes) : (p : ℕ) = (q : ℕ) ↔ p = q :=
  Subtype.ext_iff.symm

end Primes

instance monoid.primePow {α : Type*} [Monoid α] : Pow α Primes :=
  ⟨fun x p => x ^ (p : ℕ)⟩

end Nat

namespace Nat

instance fact_prime_two : Fact (Prime 2) :=
  ⟨prime_two⟩

instance fact_prime_three : Fact (Prime 3) :=
  ⟨prime_three⟩

end Nat

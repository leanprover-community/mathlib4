/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Associated
import Mathlib.Algebra.Parity
import Mathlib.Data.Int.Dvd.Basic
import Mathlib.Data.Int.Units
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Bounds.Basic

#align_import data.nat.prime from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# Prime numbers

This file deals with prime numbers: natural numbers `p ≥ 2` whose only divisors are `p` and `1`.

## Important declarations

- `Nat.Prime`: the predicate that expresses that a natural number `p` is prime
- `Nat.Primes`: the subtype of natural numbers that are prime
- `Nat.minFac n`: the minimal prime factor of a natural number `n ≠ 1`
- `Nat.exists_infinite_primes`: Euclid's theorem that there exist infinitely many prime numbers.
  This also appears as `Nat.not_bddAbove_setOf_prime` and `Nat.infinite_setOf_prime` (the latter
  in `Data.Nat.PrimeFin`).
- `Nat.prime_iff`: `Nat.Prime` coincides with the general definition of `Prime`
- `Nat.irreducible_iff_nat_prime`: a non-unit natural number is
                                  only divisible by `1` iff it is prime

-/


open Bool Subtype

open Nat

namespace Nat

/-- `Nat.Prime p` means that `p` is a prime number, that is, a natural number
  at least 2 whose only divisors are `p` and `1`. -/
-- Porting note: removed @[pp_nodot]
def Prime (p : ℕ) :=
  Irreducible p
#align nat.prime Nat.Prime

theorem irreducible_iff_nat_prime (a : ℕ) : Irreducible a ↔ Nat.Prime a :=
  Iff.rfl
#align irreducible_iff_nat_prime Nat.irreducible_iff_nat_prime

theorem not_prime_zero : ¬Prime 0
  | h => h.ne_zero rfl
#align nat.not_prime_zero Nat.not_prime_zero

theorem not_prime_one : ¬Prime 1
  | h => h.ne_one rfl
#align nat.not_prime_one Nat.not_prime_one

theorem Prime.ne_zero {n : ℕ} (h : Prime n) : n ≠ 0 :=
  Irreducible.ne_zero h
#align nat.prime.ne_zero Nat.Prime.ne_zero

theorem Prime.pos {p : ℕ} (pp : Prime p) : 0 < p :=
  Nat.pos_of_ne_zero pp.ne_zero
#align nat.prime.pos Nat.Prime.pos

theorem Prime.two_le : ∀ {p : ℕ}, Prime p → 2 ≤ p
  | 0, h => (not_prime_zero h).elim
  | 1, h => (not_prime_one h).elim
  | _ + 2, _ => le_add_self
#align nat.prime.two_le Nat.Prime.two_le

theorem Prime.one_lt {p : ℕ} : Prime p → 1 < p :=
  Prime.two_le
#align nat.prime.one_lt Nat.Prime.one_lt

instance Prime.one_lt' (p : ℕ) [hp : Fact p.Prime] : Fact (1 < p) :=
  ⟨hp.1.one_lt⟩
#align nat.prime.one_lt' Nat.Prime.one_lt'

theorem Prime.ne_one {p : ℕ} (hp : p.Prime) : p ≠ 1 :=
  hp.one_lt.ne'
#align nat.prime.ne_one Nat.Prime.ne_one

theorem Prime.eq_one_or_self_of_dvd {p : ℕ} (pp : p.Prime) (m : ℕ) (hm : m ∣ p) :
    m = 1 ∨ m = p := by
  obtain ⟨n, hn⟩ := hm
  -- ⊢ m = 1 ∨ m = p
  have := pp.isUnit_or_isUnit hn
  -- ⊢ m = 1 ∨ m = p
  rw [Nat.isUnit_iff, Nat.isUnit_iff] at this
  -- ⊢ m = 1 ∨ m = p
  apply Or.imp_right _ this
  -- ⊢ n = 1 → m = p
  rintro rfl
  -- ⊢ m = p
  rw [hn, mul_one]
  -- 🎉 no goals
#align nat.prime.eq_one_or_self_of_dvd Nat.Prime.eq_one_or_self_of_dvd

theorem prime_def_lt'' {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ (m) (_ : m ∣ p), m = 1 ∨ m = p := by
  refine' ⟨fun h => ⟨h.two_le, h.eq_one_or_self_of_dvd⟩, fun h => _⟩
  -- ⊢ Prime p
  -- Porting note: needed to make ℕ explicit
  have h1 := (@one_lt_two ℕ ..).trans_le h.1
  -- ⊢ Prime p
  refine' ⟨mt Nat.isUnit_iff.mp h1.ne', fun a b hab => _⟩
  -- ⊢ IsUnit a ∨ IsUnit b
  simp only [Nat.isUnit_iff]
  -- ⊢ a = 1 ∨ b = 1
  apply Or.imp_right _ (h.2 a _)
  -- ⊢ a = p → b = 1
  · rintro rfl
    -- ⊢ b = 1
    rw [← mul_right_inj' (pos_of_gt h1).ne', ← hab, mul_one]
    -- 🎉 no goals
  · rw [hab]
    -- ⊢ a ∣ a * b
    exact dvd_mul_right _ _
    -- 🎉 no goals
#align nat.prime_def_lt'' Nat.prime_def_lt''

theorem prime_def_lt {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1 :=
  prime_def_lt''.trans <|
    and_congr_right fun p2 =>
      forall_congr' fun _ =>
        ⟨fun h l d => (h d).resolve_right (ne_of_lt l), fun h d =>
          (le_of_dvd (le_of_succ_le p2) d).lt_or_eq_dec.imp_left fun l => h l d⟩
#align nat.prime_def_lt Nat.prime_def_lt

theorem prime_def_lt' {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m < p → ¬m ∣ p :=
  prime_def_lt.trans <|
    and_congr_right fun p2 =>
      forall_congr' fun m =>
        ⟨fun h m2 l d => not_lt_of_ge m2 ((h l d).symm ▸ by decide), fun h l d => by
                                                            -- 🎉 no goals
          rcases m with (_ | _ | m)
          · rw [eq_zero_of_zero_dvd d] at p2
            -- ⊢ zero = 1
            revert p2
            -- ⊢ 2 ≤ 0 → zero = 1
            decide
            -- 🎉 no goals
          · rfl
            -- 🎉 no goals
          · exact (h le_add_self l).elim d⟩
            -- 🎉 no goals
#align nat.prime_def_lt' Nat.prime_def_lt'

theorem prime_def_le_sqrt {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m ≤ sqrt p → ¬m ∣ p :=
  prime_def_lt'.trans <|
    and_congr_right fun p2 =>
      ⟨fun a m m2 l => a m m2 <| lt_of_le_of_lt l <| sqrt_lt_self p2, fun a =>
        have : ∀ {m k : ℕ}, m ≤ k → 1 < m → p ≠ m * k := fun {m k} mk m1 e =>
          a m m1 (le_sqrt.2 (e.symm ▸ Nat.mul_le_mul_left m mk)) ⟨k, e⟩
        fun m m2 l ⟨k, e⟩ => by
        cases' le_total m k with mk km
        -- ⊢ False
        · exact this mk m2 e
          -- 🎉 no goals
        · rw [mul_comm] at e
          -- ⊢ False
          refine' this km (lt_of_mul_lt_mul_right _ (zero_le m)) e
          -- ⊢ 1 * m < k * m
          rwa [one_mul, ← e]⟩
          -- 🎉 no goals
#align nat.prime_def_le_sqrt Nat.prime_def_le_sqrt

theorem prime_of_coprime (n : ℕ) (h1 : 1 < n) (h : ∀ m < n, m ≠ 0 → n.coprime m) : Prime n := by
  refine' prime_def_lt.mpr ⟨h1, fun m mlt mdvd => _⟩
  -- ⊢ m = 1
  have hm : m ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at mdvd
    exact mlt.ne' mdvd
  exact (h m mlt hm).symm.eq_one_of_dvd mdvd
  -- 🎉 no goals
#align nat.prime_of_coprime Nat.prime_of_coprime

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
#align nat.decidable_prime_1 Nat.decidablePrime1

theorem prime_two : Prime 2 := by decide
                                  -- 🎉 no goals
#align nat.prime_two Nat.prime_two

theorem prime_three : Prime 3 := by decide
                                    -- 🎉 no goals
#align nat.prime_three Nat.prime_three

theorem Prime.five_le_of_ne_two_of_ne_three {p : ℕ} (hp : p.Prime) (h_two : p ≠ 2)
    (h_three : p ≠ 3) : 5 ≤ p := by
  by_contra' h
  -- ⊢ False
  revert h_two h_three hp
  -- ⊢ Prime p → p ≠ 2 → p ≠ 3 → False
  -- Porting note: was `decide!`
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

theorem dvd_prime {p m : ℕ} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m = p :=
  ⟨fun d => pp.eq_one_or_self_of_dvd m d, fun h =>
    h.elim (fun e => e.symm ▸ one_dvd _) fun e => e.symm ▸ dvd_rfl⟩
#align nat.dvd_prime Nat.dvd_prime

theorem dvd_prime_two_le {p m : ℕ} (pp : Prime p) (H : 2 ≤ m) : m ∣ p ↔ m = p :=
  (dvd_prime pp).trans <| or_iff_right_of_imp <| Not.elim <| ne_of_gt H
#align nat.dvd_prime_two_le Nat.dvd_prime_two_le

theorem prime_dvd_prime_iff_eq {p q : ℕ} (pp : p.Prime) (qp : q.Prime) : p ∣ q ↔ p = q :=
  dvd_prime_two_le qp (Prime.two_le pp)
#align nat.prime_dvd_prime_iff_eq Nat.prime_dvd_prime_iff_eq

theorem Prime.not_dvd_one {p : ℕ} (pp : Prime p) : ¬p ∣ 1 :=
  Irreducible.not_dvd_one pp
#align nat.prime.not_dvd_one Nat.Prime.not_dvd_one

theorem not_prime_mul {a b : ℕ} (a1 : 1 < a) (b1 : 1 < b) : ¬Prime (a * b) := fun h =>
  ne_of_lt (Nat.mul_lt_mul_of_pos_left b1 (lt_of_succ_lt a1)) <| by
    simpa using (dvd_prime_two_le h a1).1 (dvd_mul_right _ _)
    -- 🎉 no goals
#align nat.not_prime_mul Nat.not_prime_mul

theorem not_prime_mul' {a b n : ℕ} (h : a * b = n) (h₁ : 1 < a) (h₂ : 1 < b) : ¬Prime n := by
  rw [← h]
  -- ⊢ ¬Prime (a * b)
  exact not_prime_mul h₁ h₂
  -- 🎉 no goals
#align nat.not_prime_mul' Nat.not_prime_mul'

theorem prime_mul_iff {a b : ℕ} : Nat.Prime (a * b) ↔ a.Prime ∧ b = 1 ∨ b.Prime ∧ a = 1 := by
  simp only [iff_self_iff, irreducible_mul_iff, ← irreducible_iff_nat_prime, Nat.isUnit_iff]
  -- 🎉 no goals
#align nat.prime_mul_iff Nat.prime_mul_iff

theorem Prime.dvd_iff_eq {p a : ℕ} (hp : p.Prime) (a1 : a ≠ 1) : a ∣ p ↔ p = a := by
  refine'
    ⟨_, by
      rintro rfl
      rfl⟩
  rintro ⟨j, rfl⟩
  -- ⊢ a * j = a
  rcases prime_mul_iff.mp hp with (⟨_, rfl⟩ | ⟨_, rfl⟩)
  -- ⊢ a * 1 = a
  · exact mul_one _
    -- 🎉 no goals
  · exact (a1 rfl).elim
    -- 🎉 no goals
#align nat.prime.dvd_iff_eq Nat.Prime.dvd_iff_eq

section MinFac

theorem minFac_lemma (n k : ℕ) (h : ¬n < k * k) : sqrt n - k < sqrt n + 2 - k :=
  (tsub_lt_tsub_iff_right <| le_sqrt.2 <| le_of_not_gt h).2 <| Nat.lt_add_of_pos_right (by decide)
                                                                                           -- 🎉 no goals
#align nat.min_fac_lemma Nat.minFac_lemma

/-- If `n < k * k`, then `minFacAux n k = n`, if `k | n`, then `minFacAux n k = k`.
  Otherwise, `minFacAux n k = minFacAux n (k+2)` using well-founded recursion.
  If `n` is odd and `1 < n`, then `minFacAux n 3` is the smallest prime factor of `n`. -/
def minFacAux (n : ℕ) : ℕ → ℕ
  | k =>
    if h : n < k * k then n
    else
      if k ∣ n then k
      else
        have := minFac_lemma n k h
        minFacAux n (k + 2)
termination_by _ n k => sqrt n + 2 - k
#align nat.min_fac_aux Nat.minFacAux

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def minFac (n : ℕ) : ℕ :=
  if 2 ∣ n then 2 else minFacAux n 3
#align nat.min_fac Nat.minFac

@[simp]
theorem minFac_zero : minFac 0 = 2 :=
  rfl
#align nat.min_fac_zero Nat.minFac_zero

@[simp]
theorem minFac_one : minFac 1 = 1 :=
  rfl
#align nat.min_fac_one Nat.minFac_one

theorem minFac_eq (n : ℕ) : minFac n = if 2 ∣ n then 2 else minFacAux n 3 := rfl
#align nat.min_fac_eq Nat.minFac_eq

private def minFacProp (n k : ℕ) :=
  2 ≤ k ∧ k ∣ n ∧ ∀ m, 2 ≤ m → m ∣ n → k ≤ m

theorem minFacAux_has_prop {n : ℕ} (n2 : 2 ≤ n) :
    ∀ k i, k = 2 * i + 3 → (∀ m, 2 ≤ m → m ∣ n → k ≤ m) → minFacProp n (minFacAux n k)
  | k => fun i e a => by
    rw [minFacAux]
    -- ⊢ Nat.minFacProp n
    by_cases h : n < k * k <;> simp [h]
                               -- ⊢ Nat.minFacProp n n
                               -- ⊢ Nat.minFacProp n (if x✝ ∣ n then x✝ else minFacAux n (x✝ + 2))
    · have pp : Prime n :=
        prime_def_le_sqrt.2
          ⟨n2, fun m m2 l d => not_lt_of_ge l <| lt_of_lt_of_le (sqrt_lt.2 h) (a m m2 d)⟩
      exact ⟨n2, dvd_rfl, fun m m2 d => le_of_eq ((dvd_prime_two_le pp m2).1 d).symm⟩
      -- 🎉 no goals
    have k2 : 2 ≤ k := by
      subst e
      apply Nat.le_add_left
    by_cases dk : k ∣ n <;> simp [dk]
    -- ⊢ Nat.minFacProp n (if x✝ ∣ n then x✝ else minFacAux n (x✝ + 2))
                            -- ⊢ Nat.minFacProp n x✝
                            -- ⊢ Nat.minFacProp n (minFacAux n (x✝ + 2))
    · exact ⟨k2, dk, a⟩
      -- 🎉 no goals
    · refine'
        have := minFac_lemma n k h
        minFacAux_has_prop n2 (k + 2) (i + 1) (by simp [e, left_distrib]) fun m m2 d => _
      cases' Nat.eq_or_lt_of_le (a m m2 d) with me ml
      -- ⊢ k + 2 ≤ m
      · subst me
        -- ⊢ k + 2 ≤ x✝
        contradiction
        -- 🎉 no goals
      apply (Nat.eq_or_lt_of_le ml).resolve_left
      -- ⊢ ¬succ x✝ = m
      intro me
      -- ⊢ False
      rw [← me, e] at d
      -- ⊢ False
      have d' : 2 * (i + 2) ∣ n := d
      -- ⊢ False
      have := a _ le_rfl (dvd_of_mul_right_dvd d')
      -- ⊢ False
      rw [e] at this
      -- ⊢ False
      exact absurd this (by contradiction)
      -- 🎉 no goals
  termination_by _ n _ k => sqrt n + 2 - k
#align nat.min_fac_aux_has_prop Nat.minFacAux_has_prop

theorem minFac_has_prop {n : ℕ} (n1 : n ≠ 1) : minFacProp n (minFac n) := by
  by_cases n0 : n = 0
  -- ⊢ Nat.minFacProp n (minFac n)
  · simp [n0, minFacProp, GE.ge]
    -- 🎉 no goals
  have n2 : 2 ≤ n := by
    revert n0 n1
    rcases n with (_ | _ | _) <;> simp [succ_le_succ]
  simp [minFac_eq]
  -- ⊢ Nat.minFacProp n (if 2 ∣ n then 2 else minFacAux n 3)
  by_cases d2 : 2 ∣ n <;> simp [d2]
  -- ⊢ Nat.minFacProp n (if 2 ∣ n then 2 else minFacAux n 3)
                          -- ⊢ Nat.minFacProp n 2
                          -- ⊢ Nat.minFacProp n (minFacAux n 3)
  · exact ⟨le_rfl, d2, fun k k2 _ => k2⟩
    -- 🎉 no goals
  · refine'
      minFacAux_has_prop n2 3 0 rfl fun m m2 d => (Nat.eq_or_lt_of_le m2).resolve_left (mt _ d2)
    exact fun e => e.symm ▸ d
    -- 🎉 no goals
#align nat.min_fac_has_prop Nat.minFac_has_prop

theorem minFac_dvd (n : ℕ) : minFac n ∣ n :=
  if n1 : n = 1 then by simp [n1] else (minFac_has_prop n1).2.1
                        -- 🎉 no goals
#align nat.min_fac_dvd Nat.minFac_dvd

theorem minFac_prime {n : ℕ} (n1 : n ≠ 1) : Prime (minFac n) :=
  let ⟨f2, fd, a⟩ := minFac_has_prop n1
  prime_def_lt'.2 ⟨f2, fun m m2 l d => not_le_of_gt l (a m m2 (d.trans fd))⟩
#align nat.min_fac_prime Nat.minFac_prime

theorem minFac_le_of_dvd {n : ℕ} : ∀ {m : ℕ}, 2 ≤ m → m ∣ n → minFac n ≤ m := by
  by_cases n1 : n = 1 <;> [exact fun m2 _ => n1.symm ▸ le_trans (by decide) m2;
    apply (minFac_has_prop n1).2.2]
#align nat.min_fac_le_of_dvd Nat.minFac_le_of_dvd

theorem minFac_pos (n : ℕ) : 0 < minFac n := by
  by_cases n1 : n = 1 <;> [exact n1.symm ▸ (by decide); exact (minFac_prime n1).pos]
  -- 🎉 no goals
#align nat.min_fac_pos Nat.minFac_pos

theorem minFac_le {n : ℕ} (H : 0 < n) : minFac n ≤ n :=
  le_of_dvd H (minFac_dvd n)
#align nat.min_fac_le Nat.minFac_le

theorem le_minFac {m n : ℕ} : n = 1 ∨ m ≤ minFac n ↔ ∀ p, Prime p → p ∣ n → m ≤ p :=
  ⟨fun h p pp d =>
    h.elim (by rintro rfl; cases pp.not_dvd_one d) fun h =>
               -- ⊢ m ≤ p
                           -- 🎉 no goals
      le_trans h <| minFac_le_of_dvd pp.two_le d,
    fun H => or_iff_not_imp_left.2 fun n1 => H _ (minFac_prime n1) (minFac_dvd _)⟩
#align nat.le_min_fac Nat.le_minFac

theorem le_minFac' {m n : ℕ} : n = 1 ∨ m ≤ minFac n ↔ ∀ p, 2 ≤ p → p ∣ n → m ≤ p :=
  ⟨fun h p (pp : 1 < p) d =>
    h.elim (by rintro rfl; cases not_le_of_lt pp (le_of_dvd (by decide) d)) fun h =>
               -- ⊢ m ≤ p
                           -- 🎉 no goals
      le_trans h <| minFac_le_of_dvd pp d,
    fun H => le_minFac.2 fun p pp d => H p pp.two_le d⟩
#align nat.le_min_fac' Nat.le_minFac'

theorem prime_def_minFac {p : ℕ} : Prime p ↔ 2 ≤ p ∧ minFac p = p :=
  ⟨fun pp =>
    ⟨pp.two_le,
      let ⟨f2, fd, _⟩ := minFac_has_prop <| ne_of_gt pp.one_lt
      ((dvd_prime pp).1 fd).resolve_left (ne_of_gt f2)⟩,
    fun ⟨p2, e⟩ => e ▸ minFac_prime (ne_of_gt p2)⟩
#align nat.prime_def_min_fac Nat.prime_def_minFac

@[simp]
theorem Prime.minFac_eq {p : ℕ} (hp : Prime p) : minFac p = p :=
  (prime_def_minFac.1 hp).2
#align nat.prime.min_fac_eq Nat.Prime.minFac_eq

/-- This instance is faster in the virtual machine than `decidablePrime1`,
but slower in the kernel.

If you need to prove that a particular number is prime, in any case
you should not use `by decide`, but rather `by norm_num`, which is
much faster.
-/
instance decidablePrime (p : ℕ) : Decidable (Prime p) :=
  decidable_of_iff' _ prime_def_minFac
#align nat.decidable_prime Nat.decidablePrime

theorem not_prime_iff_minFac_lt {n : ℕ} (n2 : 2 ≤ n) : ¬Prime n ↔ minFac n < n :=
  (not_congr <| prime_def_minFac.trans <| and_iff_right n2).trans <|
    (lt_iff_le_and_ne.trans <| and_iff_right <| minFac_le <| le_of_succ_le n2).symm
#align nat.not_prime_iff_min_fac_lt Nat.not_prime_iff_minFac_lt

theorem minFac_le_div {n : ℕ} (pos : 0 < n) (np : ¬Prime n) : minFac n ≤ n / minFac n :=
  match minFac_dvd n with
  | ⟨0, h0⟩ => absurd pos <| by rw [h0, mul_zero]; exact by decide
                                -- ⊢ ¬0 < 0
                                                   -- 🎉 no goals
  | ⟨1, h1⟩ => by
    rw [mul_one] at h1
    -- ⊢ minFac n ≤ n / minFac n
    rw [prime_def_minFac, not_and_or, ← h1, eq_self_iff_true, _root_.not_true, or_false_iff,
      not_le] at np
    rw [le_antisymm (le_of_lt_succ np) (succ_le_of_lt pos), minFac_one, Nat.div_one]
    -- 🎉 no goals
  | ⟨x + 2, hx⟩ => by
    conv_rhs =>
      congr
      rw [hx]
    rw [Nat.mul_div_cancel_left _ (minFac_pos _)]
    -- ⊢ minFac n ≤ x + 2
    exact minFac_le_of_dvd (le_add_left 2 x) ⟨minFac n, by rwa [mul_comm]⟩
    -- 🎉 no goals
#align nat.min_fac_le_div Nat.minFac_le_div

/-- The square of the smallest prime factor of a composite number `n` is at most `n`.
-/
theorem minFac_sq_le_self {n : ℕ} (w : 0 < n) (h : ¬Prime n) : minFac n ^ 2 ≤ n :=
  have t : minFac n ≤ n / minFac n := minFac_le_div w h
  calc
    minFac n ^ 2 = minFac n * minFac n := sq (minFac n)
    _ ≤ n / minFac n * minFac n := Nat.mul_le_mul_right (minFac n) t
    _ ≤ n := div_mul_le_self n (minFac n)
#align nat.min_fac_sq_le_self Nat.minFac_sq_le_self

@[simp]
theorem minFac_eq_one_iff {n : ℕ} : minFac n = 1 ↔ n = 1 := by
  constructor
  -- ⊢ minFac n = 1 → n = 1
  · intro h
    -- ⊢ n = 1
    by_contra hn
    -- ⊢ False
    have := minFac_prime hn
    -- ⊢ False
    rw [h] at this
    -- ⊢ False
    exact not_prime_one this
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ minFac 1 = 1
    rfl
    -- 🎉 no goals
#align nat.min_fac_eq_one_iff Nat.minFac_eq_one_iff

@[simp]
theorem minFac_eq_two_iff (n : ℕ) : minFac n = 2 ↔ 2 ∣ n := by
  constructor
  -- ⊢ minFac n = 2 → 2 ∣ n
  · intro h
    -- ⊢ 2 ∣ n
    rw [←h]
    -- ⊢ minFac n ∣ n
    exact minFac_dvd n
    -- 🎉 no goals
  · intro h
    -- ⊢ minFac n = 2
    have ub := minFac_le_of_dvd (le_refl 2) h
    -- ⊢ minFac n = 2
    have lb := minFac_pos n
    -- ⊢ minFac n = 2
    refine ub.eq_or_lt.resolve_right fun h' => ?_
    -- ⊢ False
    have := le_antisymm (Nat.succ_le_of_lt lb) (lt_succ_iff.mp h')
    -- ⊢ False
    rw [eq_comm, Nat.minFac_eq_one_iff] at this
    -- ⊢ False
    subst this
    -- ⊢ False
    exact not_lt_of_le (le_of_dvd zero_lt_one h) one_lt_two
    -- 🎉 no goals
#align nat.min_fac_eq_two_iff Nat.minFac_eq_two_iff

end MinFac

theorem exists_dvd_of_not_prime {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
  ⟨minFac n, minFac_dvd _, ne_of_gt (minFac_prime (ne_of_gt n2)).one_lt,
    ne_of_lt <| (not_prime_iff_minFac_lt n2).1 np⟩
#align nat.exists_dvd_of_not_prime Nat.exists_dvd_of_not_prime

theorem exists_dvd_of_not_prime2 {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) :
    ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
  ⟨minFac n, minFac_dvd _, (minFac_prime (ne_of_gt n2)).two_le,
    (not_prime_iff_minFac_lt n2).1 np⟩
#align nat.exists_dvd_of_not_prime2 Nat.exists_dvd_of_not_prime2

theorem exists_prime_and_dvd {n : ℕ} (hn : n ≠ 1) : ∃ p, Prime p ∧ p ∣ n :=
  ⟨minFac n, minFac_prime hn, minFac_dvd _⟩
#align nat.exists_prime_and_dvd Nat.exists_prime_and_dvd

theorem dvd_of_forall_prime_mul_dvd {a b : ℕ}
    (hdvd : ∀ p : ℕ, p.Prime → p ∣ a → p * a ∣ b) : a ∣ b := by
  obtain rfl | ha := eq_or_ne a 1
  -- ⊢ 1 ∣ b
  · apply one_dvd
    -- 🎉 no goals
  obtain ⟨p, hp⟩ := exists_prime_and_dvd ha
  -- ⊢ a ∣ b
  exact _root_.trans (dvd_mul_left a p) (hdvd p hp.1 hp.2)
  -- 🎉 no goals
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
  -- ⊢ ∀ (x : ℕ), ∃ y, y ∈ {p | Prime p} ∧ x < y
  intro n
  -- ⊢ ∃ y, y ∈ {p | Prime p} ∧ n < y
  obtain ⟨p, hi, hp⟩ := exists_infinite_primes n.succ
  -- ⊢ ∃ y, y ∈ {p | Prime p} ∧ n < y
  exact ⟨p, hp, hi⟩
  -- 🎉 no goals
#align nat.not_bdd_above_set_of_prime Nat.not_bddAbove_setOf_prime

theorem Prime.eq_two_or_odd {p : ℕ} (hp : Prime p) : p = 2 ∨ p % 2 = 1 :=
  p.mod_two_eq_zero_or_one.imp_left fun h =>
    ((hp.eq_one_or_self_of_dvd 2 (dvd_of_mod_eq_zero h)).resolve_left (by decide)).symm
                                                                          -- 🎉 no goals
#align nat.prime.eq_two_or_odd Nat.Prime.eq_two_or_odd

theorem Prime.eq_two_or_odd' {p : ℕ} (hp : Prime p) : p = 2 ∨ Odd p :=
  Or.imp_right (fun h => ⟨p / 2, (div_add_mod p 2).symm.trans (congr_arg _ h)⟩) hp.eq_two_or_odd
#align nat.prime.eq_two_or_odd' Nat.Prime.eq_two_or_odd'

theorem Prime.even_iff {p : ℕ} (hp : Prime p) : Even p ↔ p = 2 := by
  rw [even_iff_two_dvd, prime_dvd_prime_iff_eq prime_two hp, eq_comm]
  -- 🎉 no goals
#align nat.prime.even_iff Nat.Prime.even_iff

theorem Prime.odd_of_ne_two {p : ℕ} (hp : p.Prime) (h_two : p ≠ 2) : Odd p :=
  hp.eq_two_or_odd'.resolve_left h_two
#align nat.prime.odd_of_ne_two Nat.Prime.odd_of_ne_two

theorem Prime.even_sub_one {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : Even (p - 1) :=
  let ⟨n, hn⟩ := hp.odd_of_ne_two h2; ⟨n, by rw [hn, Nat.add_sub_cancel, two_mul]⟩
                                             -- 🎉 no goals
#align nat.prime.even_sub_one Nat.Prime.even_sub_one

/-- A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`. -/
theorem Prime.mod_two_eq_one_iff_ne_two {p : ℕ} [Fact p.Prime] : p % 2 = 1 ↔ p ≠ 2 := by
  refine' ⟨fun h hf => _, (Nat.Prime.eq_two_or_odd <| @Fact.out p.Prime _).resolve_left⟩
  -- ⊢ False
  rw [hf] at h
  -- ⊢ False
  simp at h
  -- 🎉 no goals
#align nat.prime.mod_two_eq_one_iff_ne_two Nat.Prime.mod_two_eq_one_iff_ne_two

theorem coprime_of_dvd {m n : ℕ} (H : ∀ k, Prime k → k ∣ m → ¬k ∣ n) : coprime m n := by
  rw [coprime_iff_gcd_eq_one]
  -- ⊢ gcd m n = 1
  by_contra g2
  -- ⊢ False
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2
  -- ⊢ False
  apply H p hp <;> apply dvd_trans hpdvd
  -- ⊢ p ∣ m
                   -- ⊢ gcd m n ∣ m
                   -- ⊢ gcd m n ∣ n
  · exact gcd_dvd_left _ _
    -- 🎉 no goals
  · exact gcd_dvd_right _ _
    -- 🎉 no goals
#align nat.coprime_of_dvd Nat.coprime_of_dvd

theorem coprime_of_dvd' {m n : ℕ} (H : ∀ k, Prime k → k ∣ m → k ∣ n → k ∣ 1) : coprime m n :=
  coprime_of_dvd fun k kp km kn => not_le_of_gt kp.one_lt <| le_of_dvd zero_lt_one <| H k kp km kn
#align nat.coprime_of_dvd' Nat.coprime_of_dvd'

theorem factors_lemma {k} : (k + 2) / minFac (k + 2) < k + 2 :=
  div_lt_self (Nat.zero_lt_succ _) (minFac_prime (by
      apply Nat.ne_of_gt
      -- ⊢ 1 < k + 2
      apply Nat.succ_lt_succ
      -- ⊢ 0 < k + 1
      apply Nat.zero_lt_succ
      -- 🎉 no goals
      )).one_lt
#align nat.factors_lemma Nat.factors_lemma

theorem Prime.coprime_iff_not_dvd {p n : ℕ} (pp : Prime p) : coprime p n ↔ ¬p ∣ n :=
  ⟨fun co d => pp.not_dvd_one <| co.dvd_of_dvd_mul_left (by simp [d]), fun nd =>
                                                            -- 🎉 no goals
    coprime_of_dvd fun m m2 mp => ((prime_dvd_prime_iff_eq m2 pp).1 mp).symm ▸ nd⟩
#align nat.prime.coprime_iff_not_dvd Nat.Prime.coprime_iff_not_dvd

theorem Prime.dvd_iff_not_coprime {p n : ℕ} (pp : Prime p) : p ∣ n ↔ ¬coprime p n :=
  iff_not_comm.2 pp.coprime_iff_not_dvd
#align nat.prime.dvd_iff_not_coprime Nat.Prime.dvd_iff_not_coprime

theorem Prime.not_coprime_iff_dvd {m n : ℕ} : ¬coprime m n ↔ ∃ p, Prime p ∧ p ∣ m ∧ p ∣ n := by
  apply Iff.intro
  -- ⊢ ¬coprime m n → ∃ p, Prime p ∧ p ∣ m ∧ p ∣ n
  · intro h
    -- ⊢ ∃ p, Prime p ∧ p ∣ m ∧ p ∣ n
    exact
      ⟨minFac (gcd m n), minFac_prime h, (minFac_dvd (gcd m n)).trans (gcd_dvd_left m n),
        (minFac_dvd (gcd m n)).trans (gcd_dvd_right m n)⟩
  · intro h
    -- ⊢ ¬coprime m n
    cases' h with p hp
    -- ⊢ ¬coprime m n
    apply Nat.not_coprime_of_dvd_of_dvd (Prime.one_lt hp.1) hp.2.1 hp.2.2
    -- 🎉 no goals
#align nat.prime.not_coprime_iff_dvd Nat.Prime.not_coprime_iff_dvd

theorem Prime.dvd_mul {p m n : ℕ} (pp : Prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=
  ⟨fun H => or_iff_not_imp_left.2 fun h => (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
    Or.rec (fun h : p ∣ m => h.mul_right _) fun h : p ∣ n => h.mul_left _⟩
#align nat.prime.dvd_mul Nat.Prime.dvd_mul

theorem Prime.not_dvd_mul {p m n : ℕ} (pp : Prime p) (Hm : ¬p ∣ m) (Hn : ¬p ∣ n) : ¬p ∣ m * n :=
  mt pp.dvd_mul.1 <| by simp [Hm, Hn]
                        -- 🎉 no goals
#align nat.prime.not_dvd_mul Nat.Prime.not_dvd_mul

theorem prime_iff {p : ℕ} : p.Prime ↔ _root_.Prime p :=
  ⟨fun h => ⟨h.ne_zero, h.not_unit, fun _ _ => h.dvd_mul.mp⟩, Prime.irreducible⟩
#align nat.prime_iff Nat.prime_iff

alias ⟨Prime.prime, _root_.Prime.nat_prime⟩ := prime_iff
#align nat.prime.prime Nat.Prime.prime
#align prime.nat_prime Prime.nat_prime

-- Porting note: attributes `protected`, `nolint dup_namespace` removed

theorem irreducible_iff_prime {p : ℕ} : Irreducible p ↔ _root_.Prime p :=
  prime_iff
#align nat.irreducible_iff_prime Nat.irreducible_iff_prime

theorem Prime.dvd_of_dvd_pow {p m n : ℕ} (pp : Prime p) (h : p ∣ m ^ n) : p ∣ m := by
  induction' n with n IH
  -- ⊢ p ∣ m
  · exact pp.not_dvd_one.elim h
    -- 🎉 no goals
  · rw [pow_succ] at h
    -- ⊢ p ∣ m
    exact (pp.dvd_mul.1 h).elim IH id
    -- 🎉 no goals
#align nat.prime.dvd_of_dvd_pow Nat.Prime.dvd_of_dvd_pow

theorem Prime.pow_not_prime {x n : ℕ} (hn : 2 ≤ n) : ¬(x ^ n).Prime := fun hp =>
  (hp.eq_one_or_self_of_dvd x <| dvd_trans ⟨x, sq _⟩ (pow_dvd_pow _ hn)).elim
    (fun hx1 => hp.ne_one <| hx1.symm ▸ one_pow _) fun hxn =>
    lt_irrefl x <|
      calc
        x = x ^ 1 := (pow_one _).symm
        _ < x ^ n := Nat.pow_right_strictMono (hxn.symm ▸ hp.two_le) hn
        _ = x := hxn.symm
#align nat.prime.pow_not_prime Nat.Prime.pow_not_prime

theorem Prime.pow_not_prime' {x : ℕ} : ∀ {n : ℕ}, n ≠ 1 → ¬(x ^ n).Prime
  | 0 => fun _ => not_prime_one
  | 1 => fun h => (h rfl).elim
  | _ + 2 => fun _ => Prime.pow_not_prime le_add_self
#align nat.prime.pow_not_prime' Nat.Prime.pow_not_prime'

theorem Prime.eq_one_of_pow {x n : ℕ} (h : (x ^ n).Prime) : n = 1 :=
  not_imp_not.mp Prime.pow_not_prime' h
#align nat.prime.eq_one_of_pow Nat.Prime.eq_one_of_pow

theorem Prime.pow_eq_iff {p a k : ℕ} (hp : p.Prime) : a ^ k = p ↔ a = p ∧ k = 1 := by
  refine' ⟨fun h => _, fun h => by rw [h.1, h.2, pow_one]⟩
  -- ⊢ a = p ∧ k = 1
  rw [← h] at hp
  -- ⊢ a = p ∧ k = 1
  rw [← h, hp.eq_one_of_pow, eq_self_iff_true, and_true_iff, pow_one]
  -- 🎉 no goals
#align nat.prime.pow_eq_iff Nat.Prime.pow_eq_iff

theorem pow_minFac {n k : ℕ} (hk : k ≠ 0) : (n ^ k).minFac = n.minFac := by
  rcases eq_or_ne n 1 with (rfl | hn)
  -- ⊢ minFac (1 ^ k) = minFac 1
  · simp
    -- 🎉 no goals
  have hnk : n ^ k ≠ 1 := fun hk' => hn ((pow_eq_one_iff hk).1 hk')
  -- ⊢ minFac (n ^ k) = minFac n
  apply (minFac_le_of_dvd (minFac_prime hn).two_le ((minFac_dvd n).pow hk)).antisymm
  -- ⊢ minFac n ≤ minFac (n ^ k)
  apply
    minFac_le_of_dvd (minFac_prime hnk).two_le
      ((minFac_prime hnk).dvd_of_dvd_pow (minFac_dvd _))
#align nat.pow_min_fac Nat.pow_minFac

theorem Prime.pow_minFac {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : (p ^ k).minFac = p := by
  rw [Nat.pow_minFac hk, hp.minFac_eq]
  -- 🎉 no goals
#align nat.prime.pow_min_fac Nat.Prime.pow_minFac

theorem Prime.mul_eq_prime_sq_iff {x y p : ℕ} (hp : p.Prime) (hx : x ≠ 1) (hy : y ≠ 1) :
    x * y = p ^ 2 ↔ x = p ∧ y = p := by
    refine' ⟨fun h => _, fun ⟨h₁, h₂⟩ => h₁.symm ▸ h₂.symm ▸ (sq _).symm⟩
    -- ⊢ x = p ∧ y = p
    have pdvdxy : p ∣ x * y := by rw [h]; simp [sq]
    -- ⊢ x = p ∧ y = p
    -- Could be `wlog := hp.dvd_mul.1 pdvdxy using x y`, but that imports more than we want.
    suffices ∀ x' y' : ℕ, x' ≠ 1 → y' ≠ 1 → x' * y' = p ^ 2 → p ∣ x' → x' = p ∧ y' = p by
      obtain hx | hy := hp.dvd_mul.1 pdvdxy <;>
        [skip; rw [And.comm]] <;>
        [skip; rw [mul_comm] at h pdvdxy] <;>
        apply this <;>
        assumption
    rintro x y hx hy h ⟨a, ha⟩
    -- ⊢ x = p ∧ y = p
    have : a ∣ p := ⟨y, by rwa [ha, sq, mul_assoc, mul_right_inj' hp.ne_zero, eq_comm] at h⟩
    -- ⊢ x = p ∧ y = p
    obtain ha1 | hap := (Nat.dvd_prime hp).mp ‹a ∣ p›
    -- ⊢ x = p ∧ y = p
    · subst ha1
      -- ⊢ x = p ∧ y = p
      rw [mul_one] at ha
      -- ⊢ x = p ∧ y = p
      subst ha
      -- ⊢ x = x ∧ y = x
      simp only [sq, mul_right_inj' hp.ne_zero] at h
      -- ⊢ x = x ∧ y = x
      subst h
      -- ⊢ y = y ∧ y = y
      exact ⟨rfl, rfl⟩
      -- 🎉 no goals
    · refine' (hy ?_).elim
      -- ⊢ y = 1
      subst hap
      -- ⊢ y = 1
      subst ha
      -- ⊢ y = 1
      rw [sq, Nat.mul_right_eq_self_iff (Nat.mul_pos hp.pos hp.pos : 0 < a * a)] at h
      -- ⊢ y = 1
      exact h
      -- 🎉 no goals
#align nat.prime.mul_eq_prime_sq_iff Nat.Prime.mul_eq_prime_sq_iff

theorem Prime.dvd_factorial : ∀ {n p : ℕ} (_ : Prime p), p ∣ n ! ↔ p ≤ n
  | 0, p, hp => iff_of_false hp.not_dvd_one (not_le_of_lt hp.pos)
  | n + 1, p, hp => by
    rw [factorial_succ, hp.dvd_mul, Prime.dvd_factorial hp]
    -- ⊢ p ∣ n + 1 ∨ p ≤ n ↔ p ≤ n + 1
    exact
      ⟨fun h => h.elim (le_of_dvd (succ_pos _)) le_succ_of_le, fun h =>
        (_root_.lt_or_eq_of_le h).elim (Or.inr ∘ le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩
#align nat.prime.dvd_factorial Nat.Prime.dvd_factorial

theorem Prime.coprime_pow_of_not_dvd {p m a : ℕ} (pp : Prime p) (h : ¬p ∣ a) : coprime a (p ^ m) :=
  (pp.coprime_iff_not_dvd.2 h).symm.pow_right _
#align nat.prime.coprime_pow_of_not_dvd Nat.Prime.coprime_pow_of_not_dvd

theorem coprime_primes {p q : ℕ} (pp : Prime p) (pq : Prime q) : coprime p q ↔ p ≠ q :=
  pp.coprime_iff_not_dvd.trans <| not_congr <| dvd_prime_two_le pq pp.two_le
#align nat.coprime_primes Nat.coprime_primes

theorem coprime_pow_primes {p q : ℕ} (n m : ℕ) (pp : Prime p) (pq : Prime q) (h : p ≠ q) :
    coprime (p ^ n) (q ^ m) :=
  ((coprime_primes pp pq).2 h).pow _ _
#align nat.coprime_pow_primes Nat.coprime_pow_primes

theorem coprime_or_dvd_of_prime {p} (pp : Prime p) (i : ℕ) : coprime p i ∨ p ∣ i := by
  rw [pp.dvd_iff_not_coprime]; apply em
  -- ⊢ coprime p i ∨ ¬coprime p i
                               -- 🎉 no goals
#align nat.coprime_or_dvd_of_prime Nat.coprime_or_dvd_of_prime

theorem coprime_of_lt_prime {n p} (n_pos : 0 < n) (hlt : n < p) (pp : Prime p) : coprime p n :=
  (coprime_or_dvd_of_prime pp n).resolve_right fun h => lt_le_antisymm hlt (le_of_dvd n_pos h)
#align nat.coprime_of_lt_prime Nat.coprime_of_lt_prime

theorem eq_or_coprime_of_le_prime {n p} (n_pos : 0 < n) (hle : n ≤ p) (pp : Prime p) :
    p = n ∨ coprime p n :=
  hle.eq_or_lt.imp Eq.symm fun h => coprime_of_lt_prime n_pos h pp
#align nat.eq_or_coprime_of_le_prime Nat.eq_or_coprime_of_le_prime

theorem dvd_prime_pow {p : ℕ} (pp : Prime p) {m i : ℕ} : i ∣ p ^ m ↔ ∃ k ≤ m, i = p ^ k := by
  simp_rw [_root_.dvd_prime_pow (prime_iff.mp pp) m, associated_eq_eq]
  -- 🎉 no goals
#align nat.dvd_prime_pow Nat.dvd_prime_pow

theorem Prime.dvd_mul_of_dvd_ne {p1 p2 n : ℕ} (h_neq : p1 ≠ p2) (pp1 : Prime p1) (pp2 : Prime p2)
    (h1 : p1 ∣ n) (h2 : p2 ∣ n) : p1 * p2 ∣ n :=
  coprime.mul_dvd_of_dvd_of_dvd ((coprime_primes pp1 pp2).mpr h_neq) h1 h2
#align nat.prime.dvd_mul_of_dvd_ne Nat.Prime.dvd_mul_of_dvd_ne

/-- If `p` is prime,
and `a` doesn't divide `p^k`, but `a` does divide `p^(k+1)`
then `a = p^(k+1)`.
-/
theorem eq_prime_pow_of_dvd_least_prime_pow {a p k : ℕ} (pp : Prime p) (h₁ : ¬a ∣ p ^ k)
    (h₂ : a ∣ p ^ (k + 1)) : a = p ^ (k + 1) := by
  obtain ⟨l, ⟨h, rfl⟩⟩ := (dvd_prime_pow pp).1 h₂
  -- ⊢ p ^ l = p ^ (k + 1)
  congr
  -- ⊢ l = k + 1
  exact le_antisymm h (not_le.1 ((not_congr (pow_dvd_pow_iff_le_right (Prime.one_lt pp))).1 h₁))
  -- 🎉 no goals
#align nat.eq_prime_pow_of_dvd_least_prime_pow Nat.eq_prime_pow_of_dvd_least_prime_pow

theorem ne_one_iff_exists_prime_dvd : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n
  | 0 => by simpa using Exists.intro 2 Nat.prime_two
            -- 🎉 no goals
  | 1 => by simp [Nat.not_prime_one]
            -- 🎉 no goals
  | n + 2 => by
    let a := n + 2
    -- ⊢ n + 2 ≠ 1 ↔ ∃ p, Prime p ∧ p ∣ n + 2
    let ha : a ≠ 1 := Nat.succ_succ_ne_one n
    -- ⊢ n + 2 ≠ 1 ↔ ∃ p, Prime p ∧ p ∣ n + 2
    simp only [true_iff_iff, Ne.def, not_false_iff, ha]
    -- ⊢ ∃ p, Prime p ∧ p ∣ n + 2
    exact ⟨a.minFac, Nat.minFac_prime ha, a.minFac_dvd⟩
    -- 🎉 no goals
#align nat.ne_one_iff_exists_prime_dvd Nat.ne_one_iff_exists_prime_dvd

theorem eq_one_iff_not_exists_prime_dvd {n : ℕ} : n = 1 ↔ ∀ p : ℕ, p.Prime → ¬p ∣ n := by
  simpa using not_iff_not.mpr ne_one_iff_exists_prime_dvd
  -- 🎉 no goals
#align nat.eq_one_iff_not_exists_prime_dvd Nat.eq_one_iff_not_exists_prime_dvd

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : Prime p) {m n k l : ℕ}
    (hpm : p ^ k ∣ m) (hpn : p ^ l ∣ n) (hpmn : p ^ (k + l + 1) ∣ m * n) :
    p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n := by
  have hpd : p ^ (k + l) * p ∣ m * n := by
      let hpmn' : p ^ (succ (k + l)) ∣ m * n := hpmn
      rwa [pow_succ'] at hpmn'
  have hpd2 : p ∣ m * n / p ^ (k + l) := dvd_div_of_mul_dvd hpd
  -- ⊢ p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n
  have hpd3 : p ∣ m * n / (p ^ k * p ^ l) := by simpa [pow_add] using hpd2
  -- ⊢ p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n
  have hpd4 : p ∣ m / p ^ k * (n / p ^ l) := by simpa [Nat.div_mul_div_comm hpm hpn] using hpd3
  -- ⊢ p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n
  have hpd5 : p ∣ m / p ^ k ∨ p ∣ n / p ^ l :=
    (Prime.dvd_mul p_prime).1 hpd4
  suffices p ^ k * p ∣ m ∨ p ^ l * p ∣ n by rwa [_root_.pow_succ', _root_.pow_succ']
  -- ⊢ p ^ k * p ∣ m ∨ p ^ l * p ∣ n
  exact hpd5.elim (fun h : p ∣ m / p ^ k => Or.inl <| mul_dvd_of_dvd_div hpm h)
    fun h : p ∣ n / p ^ l => Or.inr <| mul_dvd_of_dvd_div hpn h
#align nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul

theorem prime_iff_prime_int {p : ℕ} : p.Prime ↔ _root_.Prime (p : ℤ) :=
  ⟨fun hp =>
    ⟨Int.coe_nat_ne_zero_iff_pos.2 hp.pos, mt Int.isUnit_iff_natAbs_eq.1 hp.ne_one, fun a b h => by
      rw [← Int.dvd_natAbs, Int.coe_nat_dvd, Int.natAbs_mul, hp.dvd_mul] at h
      -- ⊢ ↑p ∣ a ∨ ↑p ∣ b
      rwa [← Int.dvd_natAbs, Int.coe_nat_dvd, ← Int.dvd_natAbs, Int.coe_nat_dvd]⟩,
      -- 🎉 no goals
    fun hp =>
    Nat.prime_iff.2
      ⟨Int.coe_nat_ne_zero.1 hp.1,
        (mt Nat.isUnit_iff.1) fun h => by simp [h, not_prime_one] at hp, fun a b => by
                                          -- 🎉 no goals
        simpa only [Int.coe_nat_dvd, (Int.ofNat_mul _ _).symm] using hp.2.2 a b⟩⟩
        -- 🎉 no goals
#align nat.prime_iff_prime_int Nat.prime_iff_prime_int

/-- The type of prime numbers -/
def Primes :=
  { p : ℕ // p.Prime }
  deriving DecidableEq
#align nat.primes Nat.Primes

namespace Primes

instance : Repr Nat.Primes :=
  ⟨fun p _ => repr p.val⟩

instance inhabitedPrimes : Inhabited Primes :=
  ⟨⟨2, prime_two⟩⟩
#align nat.primes.inhabited_primes Nat.Primes.inhabitedPrimes

instance coeNat : Coe Nat.Primes ℕ :=
  ⟨Subtype.val⟩
#align nat.primes.coe_nat Nat.Primes.coeNat

-- Porting note: change in signature to match change in coercion
theorem coe_nat_injective : Function.Injective (fun (a : Nat.Primes) ↦ (a : ℕ)) :=
  Subtype.coe_injective
#align nat.primes.coe_nat_injective Nat.Primes.coe_nat_injective

theorem coe_nat_inj (p q : Nat.Primes) : (p : ℕ) = (q : ℕ) ↔ p = q :=
  Subtype.ext_iff.symm
#align nat.primes.coe_nat_inj Nat.Primes.coe_nat_inj

end Primes

instance monoid.primePow {α : Type*} [Monoid α] : Pow α Primes :=
  ⟨fun x p => x ^ (p : ℕ)⟩
#align nat.monoid.prime_pow Nat.monoid.primePow

end Nat

namespace Nat

instance fact_prime_two : Fact (Prime 2) :=
  ⟨prime_two⟩
#align nat.fact_prime_two Nat.fact_prime_two

instance fact_prime_three : Fact (Prime 3) :=
  ⟨prime_three⟩
#align nat.fact_prime_three Nat.fact_prime_three

end Nat

namespace Int

theorem prime_two : Prime (2 : ℤ) :=
  Nat.prime_iff_prime_int.mp Nat.prime_two
#align int.prime_two Int.prime_two

theorem prime_three : Prime (3 : ℤ) :=
  Nat.prime_iff_prime_int.mp Nat.prime_three
#align int.prime_three Int.prime_three

end Int

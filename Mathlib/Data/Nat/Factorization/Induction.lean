/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import Mathlib.Data.Nat.Factorization.Defs

/-!
# Induction principles involving factorizations
-/

open Nat Finset List Finsupp

namespace Nat
variable {a b m n p : ℕ}

/-! ## Definitions -/


/-- Given `P 0, P 1` and a way to extend `P a` to `P (p ^ n * a)` for prime `p` not dividing `a`,
we can define `P` for all natural numbers. -/
@[elab_as_elim]
def recOnPrimePow {P : ℕ → Sort*} (h0 : P 0) (h1 : P 1)
    (h : ∀ a p n : ℕ, p.Prime → ¬p ∣ a → 0 < n → P a → P (p ^ n * a)) : ∀ a : ℕ, P a := fun a =>
  Nat.strongRecOn' a fun n =>
    match n with
    | 0 => fun _ => h0
    | 1 => fun _ => h1
    | k + 2 => fun hk => by
      letI p := (k + 2).minFac
      haveI hp : Prime p := minFac_prime (succ_succ_ne_one k)
      letI t := (k + 2).factorization p
      haveI hpt : p ^ t ∣ k + 2 := ordProj_dvd _ _
      haveI htp : 0 < t := hp.factorization_pos_of_dvd (k + 1).succ_ne_zero (k + 2).minFac_dvd
      convert h ((k + 2) / p ^ t) p t hp _ htp (hk _ (Nat.div_lt_of_lt_mul _)) using 1
      · rw [Nat.mul_div_cancel' hpt]
      · rw [Nat.dvd_div_iff_mul_dvd hpt, ← Nat.pow_succ]
        exact pow_succ_factorization_not_dvd (k + 1).succ_ne_zero hp
      · simp [htp.ne', hp.one_lt]

/-- Given `P 0`, `P 1`, and `P (p ^ n)` for positive prime powers, and a way to extend `P a` and
`P b` to `P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_elim]
def recOnPosPrimePosCoprime {P : ℕ → Sort*} (hp : ∀ p n : ℕ, Prime p → 0 < n → P (p ^ n))
    (h0 : P 0) (h1 : P 1) (h : ∀ a b, 1 < a → 1 < b → Coprime a b → P a → P b → P (a * b)) :
    ∀ a, P a :=
  recOnPrimePow h0 h1 <| by
    intro a p n hp' hpa hn hPa
    by_cases ha1 : a = 1
    · rw [ha1, mul_one]
      exact hp p n hp' hn
    refine h (p ^ n) a (hp'.one_lt.trans_le (le_self_pow hn.ne' _)) ?_ ?_ (hp _ _ hp' hn) hPa
    · contrapose! hpa
      simp [lt_one_iff.1 (lt_of_le_of_ne hpa ha1)]
    · simpa [hn, Prime.coprime_iff_not_dvd hp']

/-- Given `P 0`, `P (p ^ n)` for all prime powers, and a way to extend `P a` and `P b` to
`P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_elim]
def recOnPrimeCoprime {P : ℕ → Sort*} (h0 : P 0) (hp : ∀ p n : ℕ, Prime p → P (p ^ n))
    (h : ∀ a b, 1 < a → 1 < b → Coprime a b → P a → P b → P (a * b)) : ∀ a, P a :=
  recOnPosPrimePosCoprime (fun p n h _ => hp p n h) h0 (hp 2 0 prime_two) h

/-- Given `P 0`, `P 1`, `P p` for all primes, and a way to extend `P a` and `P b` to
`P (a * b)`, we can define `P` for all natural numbers. -/
@[elab_as_elim]
def recOnMul {P : ℕ → Sort*} (h0 : P 0) (h1 : P 1) (hp : ∀ p, Prime p → P p)
    (h : ∀ a b, P a → P b → P (a * b)) : ∀ a, P a :=
  let rec
    /-- The predicate holds on prime powers -/
    hp'' (p n : ℕ) (hp' : Prime p) : P (p ^ n) :=
    match n with
    | 0 => h1
    | n + 1 => h _ _ (hp'' p n hp') (hp p hp')
  recOnPrimeCoprime h0 hp'' fun a b _ _ _ => h a b

lemma _root_.induction_on_primes {P : ℕ → Prop} (h₀ : P 0) (h₁ : P 1)
    (h : ∀ p a : ℕ, p.Prime → P a → P (p * a)) : ∀ n, P n := by
  refine recOnPrimePow h₀ h₁ ?_
  rintro a p n hp - - ha
  induction' n with n ih
  · simpa using ha
  · rw [pow_succ', mul_assoc]
    exact h _ _ hp ih

lemma prime_composite_induction {P : ℕ → Prop} (zero : P 0) (one : P 1)
    (prime : ∀ p : ℕ, p.Prime → P p) (composite : ∀ a, 2 ≤ a → P a → ∀ b, 2 ≤ b → P b → P (a * b))
    (n : ℕ) : P n := by
  refine induction_on_primes zero one ?_ _
  rintro p (_ | _ | a) hp ha
  · simpa
  · simpa using prime _ hp
  · exact composite _ hp.two_le (prime _ hp) _ a.one_lt_succ_succ ha

/-! ## Lemmas on multiplicative functions -/

/-- For any multiplicative function `f` with `f 1 = 1` and any `n ≠ 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
theorem multiplicative_factorization {β : Type*} [CommMonoid β] (f : ℕ → β)
    (h_mult : ∀ x y : ℕ, Coprime x y → f (x * y) = f x * f y) (hf : f 1 = 1) :
    ∀ {n : ℕ}, n ≠ 0 → f n = n.factorization.prod fun p k => f (p ^ k) := by
  apply Nat.recOnPosPrimePosCoprime
  · rintro p k hp - -
    simp [Prime.factorization_pow hp, Finsupp.prod_single_index _, hf]
  · simp
  · rintro -
    rw [factorization_one, hf]
    simp
  · intro a b _ _ hab ha hb hab_pos
    rw [h_mult a b hab, ha (left_ne_zero_of_mul hab_pos), hb (right_ne_zero_of_mul hab_pos),
      factorization_mul_of_coprime hab, ← prod_add_index_of_disjoint]
    exact hab.disjoint_primeFactors

/-- For any multiplicative function `f` with `f 1 = 1` and `f 0 = 1`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
theorem multiplicative_factorization' {β : Type*} [CommMonoid β] (f : ℕ → β)
    (h_mult : ∀ x y : ℕ, Coprime x y → f (x * y) = f x * f y) (hf0 : f 0 = 1) (hf1 : f 1 = 1) :
    f n = n.factorization.prod fun p k => f (p ^ k) := by
  obtain rfl | hn := eq_or_ne n 0
  · simpa
  · exact multiplicative_factorization _ h_mult hf1 hn

end Nat

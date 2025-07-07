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
def recOnPrimePow {motive : ℕ → Sort*} (zero : motive 0) (one : motive 1)
    (prime_pow_mul : ∀ a p n : ℕ, p.Prime → ¬p ∣ a → 0 < n → motive a → motive (p ^ n * a)) :
    ∀ a : ℕ, motive a := fun a =>
  Nat.strongRecOn' a fun n =>
    match n with
    | 0 => fun _ => zero
    | 1 => fun _ => one
    | k + 2 => fun hk => by
      letI p := (k + 2).minFac
      haveI hp : Prime p := minFac_prime (succ_succ_ne_one k)
      letI t := (k + 2).factorization p
      haveI hpt : p ^ t ∣ k + 2 := ordProj_dvd _ _
      haveI htp : 0 < t := hp.factorization_pos_of_dvd (k + 1).succ_ne_zero (k + 2).minFac_dvd
      convert prime_pow_mul ((k + 2) / p ^ t) p t hp _ htp (hk _ (Nat.div_lt_of_lt_mul _)) using 1
      · rw [Nat.mul_div_cancel' hpt]
      · rw [Nat.dvd_div_iff_mul_dvd hpt, ← Nat.pow_succ]
        exact pow_succ_factorization_not_dvd (k + 1).succ_ne_zero hp
      · simp [htp.ne', hp.one_lt]

/-- Given `P 0`, `P 1`, and `P (p ^ n)` for positive prime powers, and a way to extend `P a` and
`P b` to `P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_elim]
def recOnPosPrimePosCoprime {motive : ℕ → Sort*} (zero : motive 0) (one : motive 1)
    (prime_pow : ∀ p n : ℕ, Prime p → 0 < n → motive (p ^ n))
    (mul : ∀ a b, 1 < a → 1 < b → Coprime a b → motive a → motive b → motive (a * b)) :
    ∀ a, motive a :=
  recOnPrimePow zero one <| by
    intro a p n hp' hpa hn hPa
    by_cases ha1 : a = 1
    · rw [ha1, mul_one]
      exact prime_pow p n hp' hn
    refine mul (p ^ n) a (hp'.one_lt.trans_le (le_self_pow hn.ne' _)) ?_ ?_
      (prime_pow _ _ hp' hn) hPa
    · contrapose! hpa
      simp [lt_one_iff.1 (lt_of_le_of_ne hpa ha1)]
    · simpa [hn, Prime.coprime_iff_not_dvd hp']

/-- Given `P 0`, `P (p ^ n)` for all prime powers, and a way to extend `P a` and `P b` to
`P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_elim]
def recOnPrimeCoprime {motive : ℕ → Sort*} (zero : motive 0)
    (prime_pow : ∀ p n : ℕ, Prime p → motive (p ^ n))
    (mul : ∀ a b, 1 < a → 1 < b → Coprime a b → motive a → motive b → motive (a * b)) :
    ∀ a, motive a :=
  recOnPosPrimePosCoprime zero (prime_pow 2 0 prime_two) (fun p n h _ => prime_pow p n h) mul

/-- Given `P 0`, `P 1`, `P p` for all primes, and a way to extend `P a` and `P b` to
`P (a * b)`, we can define `P` for all natural numbers. -/
@[elab_as_elim]
def recOnMul {motive : ℕ → Sort*} (zero : motive 0) (one : motive 1)
    (prime : ∀ p, Prime p → motive p) (mul : ∀ a b, motive a → motive b → motive (a * b)) :
    ∀ a, motive a :=
  let rec
    /-- The predicate holds on prime powers -/
    prime_pow (p n : ℕ) (prime' : Prime p) : motive (p ^ n) :=
    match n with
    | 0 => one
    | n + 1 => mul _ _ (prime_pow p n prime') (prime p prime')
  recOnPrimeCoprime zero prime_pow fun a b _ _ _ => mul a b

@[elab_as_elim]
lemma _root_.induction_on_primes {motive : ℕ → Prop} (zero : motive 0) (one : motive 1)
    (prime_mul : ∀ p a : ℕ, p.Prime → motive a → motive (p * a)) : ∀ n, motive n := by
  refine recOnPrimePow zero one ?_
  rintro a p n hp - - ha
  induction' n with n ih
  · simpa using ha
  · rw [pow_succ', mul_assoc]
    exact prime_mul _ _ hp ih

@[elab_as_elim]
lemma prime_composite_induction
    {motive : ℕ → Prop} (zero : motive 0) (one : motive 1) (prime : ∀ p : ℕ, p.Prime → motive p)
    (composite : ∀ a, 2 ≤ a → motive a → ∀ b, 2 ≤ b → motive b → motive (a * b)) (n : ℕ) :
    motive n := by
  induction n using induction_on_primes with
  | zero => exact zero
  | one => exact one
  | prime_mul p a hp ha =>
    match a with
    | 0 => simpa
    | 1 => simpa using prime _ hp
    | b + 2 => exact composite _ hp.two_le (prime _ hp) _ (le_add_left 2 b) ha

/-! ## Lemmas on multiplicative functions -/

/-- For any multiplicative function `f` with `f 1 = 1` and any `n ≠ 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
theorem multiplicative_factorization {β : Type*} [CommMonoid β] (f : ℕ → β)
    (h_mult : ∀ x y : ℕ, Coprime x y → f (x * y) = f x * f y) (hf : f 1 = 1) :
    ∀ {n : ℕ}, n ≠ 0 → f n = n.factorization.prod fun p k => f (p ^ k) := by
  apply Nat.recOnPosPrimePosCoprime
  · simp
  · rintro -
    rw [factorization_one, hf]
    simp
  · rintro p k hp - -
    simp [Prime.factorization_pow hp, Finsupp.prod_single_index _, hf]
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

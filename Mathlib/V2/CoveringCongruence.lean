import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Fin.Tuple.Reflection

open Nat

def primes : Fin 18 → ℕ :=
  ![3, 2, 5, 7, 17, 11, 47, 19, 61, 2207, 53, 31, 1087, 109, 41, 4481, 5779, 2521]

def apparitions : Fin 18 → ℕ :=
  ![4, 3, 5, 8, 9, 10, 16, 18, 15, 32, 27, 30, 64, 27, 20, 64, 54, 60]

lemma apparitions_pos : ∀ i : Fin 18, 0 < apparitions i := by
  decide

lemma primes_are_prime : ∀ i : Fin 18, (primes i).Prime := by
  norm_num [Fin.forall_fin_succ, primes]

lemma dvd_apparitions : ∀ i : Fin 18, primes i ∣ fib (apparitions i) := by
  decide

lemma minimal_dvd_apparitions : ∀ i : Fin 18, ∀ j < apparitions i, j ≠ 0 → ¬ primes i ∣ fib j := by
  decide

lemma gcd_eq_left_iff {a b : ℕ} : a.gcd b = a ↔ a ∣ b := by
  exact gcd_eq_left_iff_dvd

lemma dvd_fib_iff {i : Fin 18} (n : ℕ) :
    primes i ∣ fib n ↔ apparitions i ∣ n := by
  constructor
  · intro h
    have hp : primes i ∣ fib (gcd n (apparitions i)) := by
      simp [fib_gcd, dvd_gcd_iff, dvd_apparitions i, h]
    by_contra! hndvd
    have hn₀ : n ≠ 0 := by rintro rfl; simp at hndvd
    have h₁ : gcd n (apparitions i) ≠ 0 := Nat.gcd_ne_zero_left hn₀
    have h₂ : gcd n (apparitions i) < apparitions i := by
      refine lt_of_le_of_ne (le_of_dvd (apparitions_pos _) (gcd_dvd_right _ _)) ?o_
      rwa [ne_eq, gcd_eq_right_iff_dvd]
    exact minimal_dvd_apparitions i _ h₂ h₁ hp
  · intro h
    exact (dvd_apparitions i).trans (fib_dvd _ _ h)

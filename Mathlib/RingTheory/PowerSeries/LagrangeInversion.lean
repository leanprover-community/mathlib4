/-
Copyright (c) 2026 Seiichi Manyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seiichi Manyama
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Lagrange inversion for formal power series

This file proves the polynomial-kernel form of the one-variable Lagrange inversion theorem over a
commutative ring without additive torsion. Let `P` be a polynomial and let `Y` be a formal power
series satisfying

`Y = X * P(Y)`.

Then, for natural numbers `n` and `k`,

`(n + k) * [X^(n+k)] Y^k = k * [X^n] P^(n+k)`.

We also give the Lagrange–Bürmann form

`(n + 1) * [X^(n+1)] H(Y) = [X^n] (H' * P^(n+1))`

for a polynomial `H`, and the usual divided coefficient formula over a field of characteristic
zero. No analytic convergence is involved.

The proof is purely algebraic and follows the induction in the reference below.

## References

* [Erlang Surya and Lutz Warnke, *Lagrange Inversion Formula by
  Induction*][surya_warnke_2023]
-/

@[expose] public section

namespace PowerSeries

open Finset Polynomial
open scoped PowerSeries

section CommRing

variable {R : Type*} [CommRing R]
variable {P : R[X]} {Y : R⟦X⟧}

private lemma coeff_pow_of_lt
    (hY : Y = PowerSeries.X * Polynomial.aeval Y P) {m k : ℕ} (h : m < k) :
    PowerSeries.coeff m (Y ^ k) = 0 := by
  have hpow : Y ^ k = PowerSeries.X ^ k * (Polynomial.aeval Y P) ^ k := by
    rw [← mul_pow, ← hY]
  simp [hpow, PowerSeries.coeff_X_pow_mul', Nat.not_le.2 h]

private lemma coeff_aeval
    (hY : Y = PowerSeries.X * Polynomial.aeval Y P) (Q : R[X]) (j : ℕ) :
    PowerSeries.coeff j (Polynomial.aeval Y Q) =
      ∑ l ∈ range (j + 1), Q.coeff l * PowerSeries.coeff j (Y ^ l) := by
  let N := max Q.natDegree j
  have hbig : PowerSeries.coeff j (Polynomial.aeval Y Q) =
      ∑ l ∈ range (N + 1), Q.coeff l * PowerSeries.coeff j (Y ^ l) := by
    rw [Polynomial.aeval_eq_sum_range, map_sum]
    rw [Finset.sum_subset
      (Finset.range_subset_range.mpr (by omega : Q.natDegree + 1 ≤ N + 1))]
    · exact Finset.sum_congr rfl fun l _ ↦ by simp
    · intro l _ hl
      have hlt : Q.natDegree < l := by
        have := mem_range.not.1 hl
        omega
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
  rw [hbig]
  refine (Finset.sum_subset
    (Finset.range_subset_range.mpr (by omega : j + 1 ≤ N + 1)) ?_).symm
  intro l _ hl
  have hjl : j < l := by
    have := mem_range.not.1 hl
    omega
  rw [coeff_pow_of_lt hY hjl, mul_zero]

end CommRing

section TorsionFree

variable {R : Type*} [CommRing R] [IsAddTorsionFree R]
variable {P : R[X]} {Y : R⟦X⟧}

private theorem lagrange_inversion_coeff_pow_of_le
    (hY : Y = PowerSeries.X * Polynomial.aeval Y P) :
    ∀ m : ℕ, ∀ k ≤ m + 1,
      ((m + 1 : ℕ) : R) * PowerSeries.coeff (m + 1) (Y ^ k) =
        (k : R) * (P ^ (m + 1)).coeff (m + 1 - k) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    obtain ⟨t, hmt⟩ : ∃ t, m + 1 = k + t := ⟨m + 1 - k, by omega⟩
    have hcoe : (Y ^ k).coeff (m + 1) = (Polynomial.aeval Y (P ^ k)).coeff t := by
      rw [hmt]
      nth_rw 1 [hY, mul_pow, map_pow, add_comm k t, PowerSeries.coeff_X_pow_mul]
    rcases t with _ | t
    · rw [hcoe, coeff_aeval hY]
      simp only [Nat.add_zero] at hmt
      rw [hmt]
      simp
    have hih : ∀ l ∈ range (t + 2),
        ((t : R) + 1) * ((P ^ k).coeff l * PowerSeries.coeff (t + 1) (Y ^ l)) =
          (P ^ k).coeff l * ((l : R) * (P ^ (t + 1)).coeff (t + 1 - l)) := by
      intro l hl
      have hl' : l ≤ t + 1 := by simpa [Nat.lt_succ_iff] using mem_range.1 hl
      have h := ih t (by omega) l hl'
      push_cast at h ⊢
      rw [show ((t : R) + 1) *
          ((P ^ k).coeff l * PowerSeries.coeff (t + 1) (Y ^ l)) =
            (P ^ k).coeff l *
              (((t : R) + 1) * PowerSeries.coeff (t + 1) (Y ^ l)) by ring, h]
    have hconv :
        ∑ l ∈ range (t + 2),
            (P ^ k).coeff l * ((l : R) * (P ^ (t + 1)).coeff (t + 1 - l)) =
          (Polynomial.derivative (P ^ k) * P ^ (t + 1)).coeff t := by
      rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [Finset.sum_range_succ'
        (fun l ↦ (P ^ k).coeff l * ((l : R) * (P ^ (t + 1)).coeff (t + 1 - l)))]
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Polynomial.coeff_derivative, show t + 1 - (p + 1) = t - p by omega]
      ring
    have hpoly : Polynomial.C ((k : R) + (t + 1)) *
          (Polynomial.derivative (P ^ k) * P ^ (t + 1)) =
        Polynomial.C (k : R) * Polynomial.derivative (P ^ (k + (t + 1))) := by
      rw [Polynomial.derivative_pow, Polynomial.derivative_pow,
        show k + (t + 1) - 1 = (k - 1) + (t + 1) by omega, pow_add,
        show ((k + (t + 1) : ℕ) : R) = (k : R) + (t + 1) by push_cast; ring]
      ring
    have hcoeff : ((k : R) + (t + 1)) *
          (Polynomial.derivative (P ^ k) * P ^ (t + 1)).coeff t =
        (k : R) * ((t : R) + 1) * (P ^ (k + (t + 1))).coeff (t + 1) := by
      have h := congrArg (fun q : R[X] ↦ q.coeff t) hpoly
      simp only [Polynomial.coeff_C_mul] at h
      rw [h, Polynomial.coeff_derivative]
      ring
    have hsum : ((t : R) + 1) * PowerSeries.coeff (m + 1) (Y ^ k) =
        (Polynomial.derivative (P ^ k) * P ^ (t + 1)).coeff t := by
      rw [hcoe, coeff_aeval hY, Finset.mul_sum, ← hconv]
      exact Finset.sum_congr rfl hih
    rw [hmt] at hsum
    rw [hmt, show k + (t + 1) - k = t + 1 by omega]
    apply nsmul_right_injective (by omega : t + 1 ≠ 0)
    simp only [nsmul_eq_mul]
    push_cast
    linear_combination ((k : R) + (t + 1)) * hsum + hcoeff

/-- **Lagrange inversion for powers.** If `Y = X * P(Y)`, then
`(n + k) * [X^(n+k)] Y^k = k * [X^n] P^(n+k)` for all natural numbers `n` and `k`.

The coefficient ring is assumed to have no additive torsion because the inductive proof cancels
multiplication by a positive natural number. -/
theorem lagrange_inversion_coeff_pow
    (hY : Y = PowerSeries.X * Polynomial.aeval Y P) (n k : ℕ) :
    ((n + k : ℕ) : R) * PowerSeries.coeff (n + k) (Y ^ k) =
      (k : R) * (P ^ (n + k)).coeff n := by
  rcases eq_or_ne (n + k) 0 with hnk | hnk
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hnk
    simp
  · simpa [show n + k - 1 + 1 = n + k by omega, show n + k - k = n by omega] using
      lagrange_inversion_coeff_pow_of_le hY (n + k - 1) k (by omega)

/-- **Lagrange–Bürmann formula.** If `Y = X * P(Y)`, then for a natural number `n` and
a polynomial `H`,

`(n + 1) * [X^(n+1)] H(Y) = [X^n] (H' * P^(n+1))`. -/
theorem lagrange_burmann_coeff
    (hY : Y = PowerSeries.X * Polynomial.aeval Y P) (n : ℕ) (H : R[X]) :
    ((n + 1 : ℕ) : R) * PowerSeries.coeff (n + 1) (Polynomial.aeval Y H) =
      (Polynomial.derivative H * P ^ (n + 1)).coeff n := by
  set f : ℕ → R := fun i ↦
    H.coeff i * ((i : R) * (P ^ (n + 1)).coeff (n + 1 - i)) with hf
  have hlhs : ((n + 1 : ℕ) : R) *
      PowerSeries.coeff (n + 1) (Polynomial.aeval Y H) =
        ∑ i ∈ range (n + 2), f i := by
    rw [coeff_aeval hY H, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ n + 1 := by simpa [Nat.lt_succ_iff] using mem_range.1 hi
    have h := lagrange_inversion_coeff_pow_of_le hY n i hi'
    simp only [hf]
    rw [← h]
    ring
  rw [hlhs, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ' f (n + 1)]
  grind [Polynomial.coeff_derivative]

end TorsionFree

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The usual coefficient form of formal Lagrange inversion for a polynomial kernel. This is the
case `H = X`, equivalently `k = 1`, of `lagrange_burmann_coeff`. -/
theorem lagrange_inversion_coeff (P : K[X]) (Y : K⟦X⟧)
    (hY : Y = PowerSeries.X * Polynomial.aeval Y P) (n : ℕ) :
    PowerSeries.coeff (n + 1) Y = (P ^ (n + 1)).coeff n / (n + 1) := by
  have h := lagrange_inversion_coeff_pow (P := P) hY n 1
  simp only [pow_one, Nat.cast_one, one_mul] at h
  apply (eq_div_iff (Nat.cast_add_one_ne_zero n)).2
  simpa [mul_comm] using h

end Field

end PowerSeries

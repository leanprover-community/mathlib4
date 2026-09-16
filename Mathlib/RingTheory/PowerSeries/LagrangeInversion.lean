/-
Copyright (c) 2026 manman4. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: manman4
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Lagrange inversion for formal power series

This file proves the polynomial-kernel form of the one-variable Lagrange inversion theorem.
Let `P` be a polynomial and let `Y` be a formal power series satisfying

`Y = X * P(Y)`.

Then, for `1 ≤ m` and `k ≤ m`,

`m * [X^m] Y^k = k * [X^(m-k)] P^m`.

We also give the Lagrange--Bürmann form

`m * [X^m] H(Y) = [X^(m-1)] (H' * P^m)`

for a polynomial `H`, and the usual divided coefficient formula over a field of characteristic
zero.

The proof is purely algebraic and follows the induction in E. Surya and L. Warnke,
*Lagrange Inversion Formula by Induction*.
-/

@[expose] public section

noncomputable section

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
  rw [hpow, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.2 h]

private lemma coeff_aeval
    (hY : Y = PowerSeries.X * Polynomial.aeval Y P) (Q : R[X]) (j : ℕ) :
    PowerSeries.coeff j (Polynomial.aeval Y Q) =
      ∑ l ∈ range (j + 1), Q.coeff l * PowerSeries.coeff j (Y ^ l) := by
  classical
  set N := max Q.natDegree j with hN
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

variable {R : Type*} [CommRing R] [NoZeroSMulDivisors ℕ R]
variable {P : R[X]} {Y : R⟦X⟧}

private lemma natCast_mul_cancel {n : ℕ} (hn : n ≠ 0) {a b : R}
    (h : (n : R) * a = (n : R) * b) : a = b := by
  have hsmul : n • a = n • b := by simpa [nsmul_eq_mul] using h
  exact smul_right_injective R hn hsmul

/-- **Lagrange inversion for powers.** If `Y = X * P(Y)`, then
`m * [X^m] Y^k = k * [X^(m-k)] P^m` for `1 ≤ m` and `k ≤ m`.

The coefficient ring is assumed to have no additive torsion because the inductive proof cancels
multiplication by a positive natural number. -/
theorem lagrange_inversion_coeff_pow
    (hY : Y = PowerSeries.X * Polynomial.aeval Y P) :
    ∀ m : ℕ, 1 ≤ m → ∀ k ≤ m,
      (m : R) * PowerSeries.coeff m (Y ^ k) = (k : R) * (P ^ m).coeff (m - k) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have hm0 : m ≠ 0 := by omega
      simp [hm0]
    obtain ⟨t, rfl⟩ : ∃ t, m = k + t := ⟨m - k, by omega⟩
    have hcoe : PowerSeries.coeff (k + t) (Y ^ k) =
        PowerSeries.coeff t (Polynomial.aeval Y (P ^ k)) := by
      have hpow : Y ^ k = PowerSeries.X ^ k * Polynomial.aeval Y (P ^ k) := by
        rw [map_pow, ← mul_pow, ← hY]
      rw [hpow, show k + t = t + k by omega, PowerSeries.coeff_X_pow_mul]
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp only [add_zero] at hcoe ⊢
      rw [hcoe, coeff_aeval hY]
      simp
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hexp : PowerSeries.coeff (k + (s + 1)) (Y ^ k) =
        ∑ l ∈ range (s + 2),
          (P ^ k).coeff l * PowerSeries.coeff (s + 1) (Y ^ l) := by
      rw [hcoe, coeff_aeval hY]
    have hih : ∀ l ∈ range (s + 2),
        ((s : R) + 1) * ((P ^ k).coeff l * PowerSeries.coeff (s + 1) (Y ^ l)) =
          (P ^ k).coeff l * ((l : R) * (P ^ (s + 1)).coeff (s + 1 - l)) := by
      intro l hl
      have hl' : l ≤ s + 1 := by simpa [Nat.lt_succ_iff] using mem_range.1 hl
      have h := ih (s + 1) (by omega) (by omega) l hl'
      push_cast at h ⊢
      rw [show ((s : R) + 1) *
          ((P ^ k).coeff l * PowerSeries.coeff (s + 1) (Y ^ l)) =
            (P ^ k).coeff l *
              (((s : R) + 1) * PowerSeries.coeff (s + 1) (Y ^ l)) by ring, h]
    have hconv :
        ∑ l ∈ range (s + 2),
            (P ^ k).coeff l * ((l : R) * (P ^ (s + 1)).coeff (s + 1 - l)) =
          (Polynomial.derivative (P ^ k) * P ^ (s + 1)).coeff s := by
      rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [Finset.sum_range_succ'
        (fun l ↦ (P ^ k).coeff l * ((l : R) * (P ^ (s + 1)).coeff (s + 1 - l)))]
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [Polynomial.coeff_derivative, show s + 1 - (p + 1) = s - p by omega]
      ring
    have hpoly : Polynomial.C ((k : R) + (s + 1)) *
          (Polynomial.derivative (P ^ k) * P ^ (s + 1)) =
        Polynomial.C (k : R) * Polynomial.derivative (P ^ (k + (s + 1))) := by
      rw [Polynomial.derivative_pow, Polynomial.derivative_pow,
        show k + (s + 1) - 1 = (k - 1) + (s + 1) by omega, pow_add,
        show ((k + (s + 1) : ℕ) : R) = (k : R) + (s + 1) by push_cast; ring]
      ring
    have hcoeff : ((k : R) + (s + 1)) *
          (Polynomial.derivative (P ^ k) * P ^ (s + 1)).coeff s =
        (k : R) * ((s : R) + 1) * (P ^ (k + (s + 1))).coeff (s + 1) := by
      have h := congrArg (fun q : R[X] ↦ q.coeff s) hpoly
      simp only [Polynomial.coeff_C_mul] at h
      rw [h, Polynomial.coeff_derivative]
      ring
    have hsum : ((s : R) + 1) * PowerSeries.coeff (k + (s + 1)) (Y ^ k) =
        (Polynomial.derivative (P ^ k) * P ^ (s + 1)).coeff s := by
      rw [hexp, Finset.mul_sum, ← hconv]
      exact Finset.sum_congr rfl hih
    rw [show k + (s + 1) - k = s + 1 by omega]
    refine natCast_mul_cancel (n := s + 1) (by omega) ?_
    push_cast
    linear_combination ((k : R) + (s + 1)) * hsum + hcoeff

/-- **Lagrange--Bürmann formula.** If `Y = X * P(Y)`, then for `m ≥ 1` and a
polynomial `H`,

`m * [X^m] H(Y) = [X^(m-1)] (H' * P^m)`. -/
theorem lagrange_burmann_coeff
    (hY : Y = PowerSeries.X * Polynomial.aeval Y P) {m : ℕ} (hm : 1 ≤ m) (H : R[X]) :
    (m : R) * PowerSeries.coeff m (Polynomial.aeval Y H) =
      (Polynomial.derivative H * P ^ m).coeff (m - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, by omega⟩
  set f : ℕ → R := fun i ↦
    H.coeff i * ((i : R) * (P ^ (s + 1)).coeff (s + 1 - i)) with hf
  have hlhs : ((s + 1 : ℕ) : R) *
      PowerSeries.coeff (s + 1) (Polynomial.aeval Y H) =
        ∑ i ∈ range (s + 2), f i := by
    rw [coeff_aeval hY H, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ s + 1 := by simpa [Nat.lt_succ_iff] using mem_range.1 hi
    have h := lagrange_inversion_coeff_pow hY (s + 1) (by omega) i hi'
    rw [hf]
    simp only
    rw [← h]
    ring
  rw [hlhs, Nat.add_sub_cancel, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ' f (s + 1)]
  have hzero : f 0 = 0 := by simp [hf]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [hf, Polynomial.coeff_derivative,
    show s + 1 - (i + 1) = s - i by omega]
  push_cast
  ring

end TorsionFree

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The usual coefficient form of formal Lagrange inversion for a polynomial kernel. This is the
case `H = X`, equivalently `k = 1`, of `lagrange_burmann_coeff`. -/
theorem lagrange_inversion_coeff (P : K[X]) (Y : K⟦X⟧)
    (hY : Y = PowerSeries.X * Polynomial.aeval Y P) (n : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff n Y = (P ^ n).coeff (n - 1) / n := by
  have h := lagrange_inversion_coeff_pow (P := P) hY n hn 1 hn
  simp only [pow_one, Nat.cast_one, one_mul] at h
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (by omega))).2
  simpa [mul_comm] using h

end Field

end PowerSeries

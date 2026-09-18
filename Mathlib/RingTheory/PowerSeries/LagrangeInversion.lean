/-
Copyright (c) 2026 Seiichi Manyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seiichi Manyama
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Lagrange inversion formula for formal power series

This file proves the one-variable Lagrange inversion formula over a commutative ring without
additive torsion. Let `P` and `Y` be formal power series satisfying

`Y = X * P(Y)`.

Then, for natural numbers `n` and `k`,

`(n + k) * [X ^ (n + k)] Y ^ k = k * [X ^ n] P ^ (n + k)`.

We also give the Lagrange–Bürmann form

`(n + 1) * [X ^ (n + 1)] H(Y) = [X ^ n] (H' * P ^ (n + 1))`

for a formal power series `H`, together with the corresponding divided formulas over a field of
characteristic zero.

## Main results

* `PowerSeries.lagrange_burmann_coeff`: the Lagrange–Bürmann coefficient formula over a
  commutative ring without additive torsion.
* `PowerSeries.lagrange_inversion_coeff_pow`: the coefficient formula for powers of `Y`.
* `PowerSeries.lagrange_burmann_coeff_div`: the divided Lagrange–Bürmann formula over a field of
  characteristic zero.
* `PowerSeries.lagrange_inversion_coeff`: the usual divided coefficient formula over a field of
  characteristic zero.

## References

* [Erlang Surya and Lutz Warnke, *Lagrange Inversion Formula by
  Induction*][surya_warnke_2023]
-/

@[expose] public section

namespace PowerSeries

open Finset
open scoped PowerSeries

section CommRing

variable {R : Type*} [CommRing R]
variable {P Y : R⟦X⟧}
variable (hY : Y = X * P.subst Y)
include hY

private lemma constantCoeff_eq_zero : Y.constantCoeff = 0 := by
  simpa using congrArg constantCoeff hY

private lemma hasSubst_of_fixedPoint : HasSubst Y :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_eq_zero hY)

/-- If `Y = X * P(Y)` and the constant coefficient of `P` is zero, then `Y = 0`. -/
theorem eq_zero_of_fixedPoint_of_constantCoeff_eq_zero (hP : P.constantCoeff = 0) : Y = 0 := by
  have hsubst := hasSubst_of_fixedPoint hY
  obtain ⟨Q, rfl⟩ := X_dvd_iff.mpr hP
  rw [subst_mul hsubst, subst_X hsubst] at hY
  have hunit : IsUnit (1 - X * Q.subst Y) := by
    simp [isUnit_iff_constantCoeff]
  rw [← hunit.mul_left_eq_zero]
  linear_combination hY

end CommRing

section TorsionFree

variable {R : Type*} [CommRing R] [IsAddTorsionFree R]
variable {P Y : R⟦X⟧}
variable (hY : Y = X * P.subst Y)
include hY

private theorem lagrange_inversion_coeff_pow_of_le : ∀ m : ℕ, ∀ k ≤ m + 1,
      (m + 1) • (Y ^ k).coeff (m + 1) = k • (P ^ (m + 1)).coeff (m + 1 - k) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro k hk
    simp only [nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    obtain ⟨t, hmt⟩ : ∃ t, m + 1 = k + t := ⟨m + 1 - k, by omega⟩
    have hcoe : (Y ^ k).coeff (m + 1) = coeff t ((P ^ k).subst Y) := by
      nth_rw 1 [hmt, hY, mul_pow, ← subst_pow (hasSubst_of_fixedPoint hY), add_comm k t,
        coeff_X_pow_mul]
    rcases t with _ | t
    · rw [hcoe, coeff_subst_of_constantCoeff_zero (constantCoeff_eq_zero hY), hmt]
      simp
    have hih : ∀ l ∈ range (t + 2),
        ((t : R) + 1) * ((P ^ k).coeff l * (Y ^ l).coeff (t + 1)) =
          (P ^ k).coeff l * ((l : R) * (P ^ (t + 1)).coeff (t + 1 - l)) := by
      intro l hl
      rw [mem_range_succ_iff] at hl
      have h := ih t (by omega) l hl
      simp only [nsmul_eq_mul] at h
      push_cast at h
      rw [show ((t : R) + 1) * ((P ^ k).coeff l * (Y ^ l).coeff (t + 1)) =
          (P ^ k).coeff l * (((t : R) + 1) * (Y ^ l).coeff (t + 1)) by ring, h]
    have hconv :
        ∑ l ∈ range (t + 2),
          (P ^ k).coeff l * ((l : R) * (P ^ (t + 1)).coeff (t + 1 - l)) =
          (d⁄dX (P ^ k) * P ^ (t + 1)).coeff t := by
      rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ'
        (fun l ↦ (P ^ k).coeff l * ((l : R) * (P ^ (t + 1)).coeff (t + 1 - l)))]
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
      refine sum_congr rfl fun p _ ↦ ?_
      rw [coeff_derivative, show t + 1 - (p + 1) = t - p by omega]
      ring
    have hpoly : C ((k : R) + (t + 1)) *
          (d⁄dX (P ^ k) * P ^ (t + 1)) =
        C (k : R) * d⁄dX (P ^ (k + (t + 1))) := by
      rw [derivative_pow, derivative_pow,
        show k + (t + 1) - 1 = (k - 1) + (t + 1) by omega, pow_add]
      simp only [map_add, map_natCast, map_one]
      push_cast
      ring
    have hcoeff : ((k : R) + (t + 1)) *
          (d⁄dX (P ^ k) * P ^ (t + 1)).coeff t =
        (k : R) * ((t : R) + 1) * (P ^ (k + (t + 1))).coeff (t + 1) := by
      rw [← coeff_C_mul, hpoly, coeff_C_mul, coeff_derivative]
      ring
    have hsum : ((t : R) + 1) * (Y ^ k).coeff (m + 1) = (d⁄dX (P ^ k) * P ^ (t + 1)).coeff t := by
      rw [hcoe, coeff_subst_of_constantCoeff_zero (constantCoeff_eq_zero hY), mul_sum, ← hconv]
      exact sum_congr rfl hih
    rw [hmt] at hsum
    rw [hmt, show k + (t + 1) - k = t + 1 by omega]
    apply nsmul_right_injective (by omega : t + 1 ≠ 0)
    push_cast
    linear_combination ((k : R) + (t + 1)) * hsum + hcoeff

/-- **Lagrange–Bürmann formula.** If `Y = X * P(Y)`, then for a natural number `n` and
a formal power series `H`,

`(n + 1) * [X ^ (n + 1)] H(Y) = [X ^ n] (H' * P ^ (n + 1))`. -/
theorem lagrange_burmann_coeff (n : ℕ) (H : R⟦X⟧) :
    (n + 1) • coeff (n + 1) (H.subst Y) = (d⁄dX H * P ^ (n + 1)).coeff n := by
  simp only [nsmul_eq_mul]
  have hlhs : ((n + 1 : ℕ) : R) * coeff (n + 1) (H.subst Y) =
        ∑ i ∈ range (n + 2), H.coeff i * ((i : R) * (P ^ (n + 1)).coeff (n + 1 - i)) := by
    rw [coeff_subst_of_constantCoeff_zero (constantCoeff_eq_zero hY) H, mul_sum]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [mem_range_succ_iff] at hi
    have h := lagrange_inversion_coeff_pow_of_le hY n i hi
    simp only [nsmul_eq_mul] at h
    rw [← h]
    ring
  rw [hlhs, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ']
  grind [coeff_derivative]

/-- **Lagrange inversion for powers.** If `Y = X * P(Y)`, then
`(n + k) * [X ^ (n + k)] Y ^ k = k * [X ^ n] P ^ (n + k)` for all natural numbers
`n` and `k`. -/
theorem lagrange_inversion_coeff_pow (n k : ℕ) :
    (n + k) • (Y ^ k).coeff (n + k) = k • (P ^ (n + k)).coeff n := by
  rcases k with _ | k
  · simp +contextual
  have hYsubst := hasSubst_of_fixedPoint hY
  have h := lagrange_burmann_coeff hY (n + k) (X ^ (k + 1))
  simp only [subst_pow hYsubst, subst_X hYsubst, derivative_pow, derivative_X, mul_assoc,
    coeff_natCast_mul, add_assoc] at h
  simpa using h

end TorsionFree

section Field

variable {K : Type*} [Field K] [CharZero K]
variable (P Y : K⟦X⟧) (hY : Y = X * P.subst Y)
include hY

/-- The divided coefficient form of the Lagrange–Bürmann formula over a field of
characteristic zero. -/
theorem lagrange_burmann_coeff_div (n : ℕ) (H : K⟦X⟧) :
    coeff (n + 1) (H.subst Y) = (d⁄dX H * P ^ (n + 1)).coeff n / (n + 1) := by
  field_simp [Nat.cast_add_one_ne_zero n]
  simpa [nsmul_eq_mul, mul_comm] using lagrange_burmann_coeff hY n H

/-- The usual coefficient form of the formal Lagrange inversion formula. This is the
case `H = X`, equivalently `k = 1`, of `lagrange_burmann_coeff_div`. -/
theorem lagrange_inversion_coeff (n : ℕ) :
    Y.coeff (n + 1) = (P ^ (n + 1)).coeff n / (n + 1) := by
  simpa [subst_X (hasSubst_of_fixedPoint hY)] using lagrange_burmann_coeff_div P Y hY n X

end Field

end PowerSeries

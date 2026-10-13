/-
Copyright (c) 2026 Seiichi Manyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seiichi Manyama
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative

import Mathlib.Tactic.LinearCombination

/-!
# Lagrange inversion formula for formal power series

This file proves the one-variable Lagrange inversion formula over a commutative ring without
additive torsion.
Let `P` and `Y` be formal power series satisfying

`Y = X * P(Y)`.

This condition implies that `Y` has zero constant coefficient.

Then, for natural numbers `n` and `k`,

`(n + k) * [X ^ (n + k)] Y ^ k = k * [X ^ n] P ^ (n + k)`.

We also give the Lagrange–Bürmann form

`(n + 1) * [X ^ (n + 1)] H(Y) = [X ^ n] (H' * P ^ (n + 1))`

for a formal power series `H`. When `n + 1` is a unit, this gives a coefficient formula using
its inverse; over a field of characteristic zero, it gives the usual divided formulas.

## Main results

* `PowerSeries.lagrange_burmann_coeff`: the Lagrange–Bürmann coefficient formula over a
  commutative ring without additive torsion.
* `PowerSeries.lagrange_inversion_coeff_pow`: the coefficient formula for powers of `Y`.
* `PowerSeries.lagrange_burmann_coeff_of_isUnit`: the coefficient formula when `n + 1` is a unit.
* `PowerSeries.lagrange_burmann_coeff_div`: the divided Lagrange–Bürmann formula over a field of
  characteristic zero.
* `PowerSeries.lagrange_inversion_coeff`: the usual divided coefficient formula over a field of
  characteristic zero.

## Implementation details

The proof follows the induction in the reference below, using the absence of additive torsion to
cancel multiplication by positive natural numbers.

## References

* [Erlang Surya and Lutz Warnke, *Lagrange Inversion Formula by Induction*][surya_warnke_2023]
-/

@[expose] public section

namespace PowerSeries

open Finset

section CommRing

variable {R : Type*} [CommRing R]
variable {P Y : R⟦X⟧}

private lemma constantCoeff_eq_zero (hY : Y = X * P.subst Y) : Y.constantCoeff = 0 := by
  simpa using congrArg constantCoeff hY

private lemma hasSubst_of_fixedPoint (hY : Y = X * P.subst Y) : HasSubst Y :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_eq_zero hY)

end CommRing

section TorsionFree

variable {R : Type*} [CommRing R] [HasUniqueDiv R]
variable {P Y : R⟦X⟧}
variable (hY : Y = X * P.subst Y)
include hY

private theorem lagrange_inversion_coeff_pow_of_le {m k : ℕ} (hk : k ≤ m + 1) :
    (m + 1) • (Y ^ k).coeff (m + 1) = k • (P ^ (m + 1)).coeff (m + 1 - k) := by
  induction m using Nat.strong_induction_on generalizing k with
  | h m ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    obtain ⟨t, hmt⟩ := Nat.exists_eq_add_of_le hk
    have hcoe : (Y ^ k).coeff (m + 1) = coeff t ((P ^ k).subst Y) := by
      nth_rw 1 [hmt, hY, mul_pow, ← subst_pow (hasSubst_of_fixedPoint hY), add_comm k t,
        coeff_X_pow_mul]
    rcases t with _ | t
    · rw [hcoe, coeff_subst_of_constantCoeff_zero (constantCoeff_eq_zero hY), hmt]
      simp
    have hih : ∀ l ∈ range (t + 2), (t + 1) • ((P ^ k).coeff l * (Y ^ l).coeff (t + 1)) =
        (P ^ k).coeff l * (l • (P ^ (t + 1)).coeff (t + 1 - l)) := by
      intro l hl
      rw [← mul_smul_comm, ih t (by omega) (mem_range_succ_iff.mp hl)]
    have hpoly : (k + t + 1) • (d⁄dX (P ^ k) * P ^ (t + 1)) = k • d⁄dX (P ^ (k + (t + 1))) := by
      rw [derivative_pow, derivative_pow, Nat.sub_add_comm hk0, pow_add]
      push_cast
      ring
    have hcoeff : (k + t + 1) • (d⁄dX (P ^ k) * P ^ (t + 1)).coeff t =
        k • (t + 1) • (P ^ (k + (t + 1))).coeff (t + 1) := by
      simpa only [map_nsmul, coeff_derivative, ← Nat.cast_add_one, ← nsmul_eq_mul'] using
        congrArg (coeff t) hpoly
    have hsum : (t + 1) • (Y ^ k).coeff (m + 1) = (d⁄dX (P ^ k) * P ^ (t + 1)).coeff t := by
      rw [hcoe, coeff_subst_of_constantCoeff_zero (constantCoeff_eq_zero hY), smul_sum,
        coeff_derivative_mul]
      exact sum_congr rfl hih
    apply nsmul_right_injective (Nat.succ_ne_zero t)
    simp [hmt] at *
    linear_combination (k + t + 1) • hsum + hcoeff

/-- **Lagrange–Bürmann formula.** If `Y = X * P(Y)`, then for a natural number `n` and
a formal power series `H`,

`(n + 1) * [X ^ (n + 1)] H(Y) = [X ^ n] (H' * P ^ (n + 1))`. -/
theorem lagrange_burmann_coeff (n : ℕ) (H : R⟦X⟧) :
    (n + 1) • coeff (n + 1) (H.subst Y) = (d⁄dX H * P ^ (n + 1)).coeff n := by
  rw [coeff_subst_of_constantCoeff_zero (constantCoeff_eq_zero hY) H, smul_sum,
    coeff_derivative_mul]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [← mul_smul_comm, lagrange_inversion_coeff_pow_of_le hY (mem_range_succ_iff.mp hi)]

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

open scoped Ring in
/-- The coefficient form of the Lagrange–Bürmann formula when `n + 1` is a unit. -/
theorem lagrange_burmann_coeff_of_isUnit (n : ℕ) (H : R⟦X⟧) (hn : IsUnit (n + 1 : R)) :
    coeff (n + 1) (H.subst Y) = (d⁄dX H * P ^ (n + 1)).coeff n * (n + 1 : R)⁻¹ʳ := by
  apply (Ring.eq_mul_inverse_iff_mul_eq _ _ _ hn).2
  simpa [mul_comm] using lagrange_burmann_coeff hY n H

end TorsionFree

section Field

variable {K : Type*} [Field K] [CharZero K]
variable {P Y : K⟦X⟧} (hY : Y = X * P.subst Y)
include hY

/-- The divided coefficient form of the Lagrange–Bürmann formula over a field of
characteristic zero. -/
theorem lagrange_burmann_coeff_div (n : ℕ) (H : K⟦X⟧) :
    coeff (n + 1) (H.subst Y) = (d⁄dX H * P ^ (n + 1)).coeff n / (n + 1) := by
  simpa [Ring.inverse_eq_inv, div_eq_mul_inv] using
    lagrange_burmann_coeff_of_isUnit hY n H (Nat.cast_add_one_ne_zero n).isUnit

/-- The usual coefficient form of the formal Lagrange inversion formula. This is the
case `H = X`, equivalently `k = 1`, of `lagrange_burmann_coeff_div`. -/
theorem lagrange_inversion_coeff (n : ℕ) :
    Y.coeff (n + 1) = (P ^ (n + 1)).coeff n / (n + 1) := by
  simpa [subst_X (hasSubst_of_fixedPoint hY)] using lagrange_burmann_coeff_div hY n X

end Field

end PowerSeries

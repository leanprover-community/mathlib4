/-
Copyright (c) 2026 Seiichi Manyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seiichi Manyama
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Lagrange inversion formula for formal power series

This file proves the one-variable Lagrange inversion formula over a commutative ring without
additive torsion. Let `P` and `Y` be formal power series satisfying

`Y = X * P(Y)`.

Then, for natural numbers `n` and `k`,

`(n + k) * [X^(n+k)] Y^k = k * [X^n] P^(n+k)`.

We also give the Lagrange–Bürmann form

`(n + 1) * [X^(n+1)] H(Y) = [X^n] (H' * P^(n+1))`

for a formal power series `H`, and the usual divided coefficient formula over a field of
characteristic zero.

The proof follows the induction in the reference below.

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

private lemma constantCoeff_eq_zero
    (hY : Y = X * P.subst Y) : Y.constantCoeff = 0 := by
  rw [hY]
  simp

private lemma hasSubst_of_fixedPoint
    (hY : Y = X * P.subst Y) : HasSubst Y :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_eq_zero hY)

private lemma coeff_pow_of_lt
    (hY : Y = X * P.subst Y) {m k : ℕ} (h : m < k) :
    coeff m (Y ^ k) = 0 := by
  have hpow : Y ^ k = X ^ k * (P.subst Y) ^ k := by rw [← mul_pow, ← hY]
  simp [hpow, coeff_X_pow_mul', Nat.not_le.2 h]

private lemma coeff_subst_of_fixedPoint
    (hY : Y = X * P.subst Y) (Q : R⟦X⟧) (j : ℕ) :
    coeff j (Q.subst Y) =
      ∑ l ∈ range (j + 1), Q.coeff l * coeff j (Y ^ l) := by
  rw [coeff_subst' (hasSubst_of_fixedPoint hY),
    finsum_eq_sum_of_support_subset (s := range (j + 1))]
  · simp [smul_eq_mul]
  · intro l hl
    simp only [mem_coe, mem_range]
    by_contra hlj
    simp [coeff_pow_of_lt hY (by omega : j < l)] at hl

end CommRing

section TorsionFree

variable {R : Type*} [CommRing R] [IsAddTorsionFree R]
variable {P Y : R⟦X⟧}

private theorem lagrange_inversion_coeff_pow_of_le
    (hY : Y = X * P.subst Y) :
    ∀ m : ℕ, ∀ k ≤ m + 1,
      ((m + 1 : ℕ) : R) * coeff (m + 1) (Y ^ k) =
        (k : R) * (P ^ (m + 1)).coeff (m + 1 - k) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    obtain ⟨t, hmt⟩ : ∃ t, m + 1 = k + t := ⟨m + 1 - k, by omega⟩
    have hcoe : (Y ^ k).coeff (m + 1) = coeff t ((P ^ k).subst Y) := by
      nth_rw 1 [hmt, hY, mul_pow, ← subst_pow (hasSubst_of_fixedPoint hY), add_comm k t,
        coeff_X_pow_mul]
    rcases t with _ | t
    · rw [hcoe, coeff_subst_of_fixedPoint hY, hmt]
      simp
    have hih : ∀ l ∈ range (t + 2),
        ((t : R) + 1) * ((P ^ k).coeff l * coeff (t + 1) (Y ^ l)) =
          (P ^ k).coeff l * ((l : R) * (P ^ (t + 1)).coeff (t + 1 - l)) := by
      intro l hl
      rw [mem_range_succ_iff] at hl
      rw_mod_cast [← ih t (by omega) l hl]
      ring
    have hconv :
        ∑ l ∈ range (t + 2),
          (P ^ k).coeff l * ((l : R) * (P ^ (t + 1)).coeff (t + 1 - l)) =
          (d⁄dX (P ^ k) * P ^ (t + 1)).coeff t := by
      rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [sum_range_succ'
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
      have h := congrArg (fun q : R⟦X⟧ ↦ q.coeff t) hpoly
      simp only [coeff_C_mul] at h
      rw [h, coeff_derivative]
      ring
    have hsum : ((t : R) + 1) * coeff (m + 1) (Y ^ k) =
        (d⁄dX (P ^ k) * P ^ (t + 1)).coeff t := by
      rw [hcoe, coeff_subst_of_fixedPoint hY, mul_sum, ← hconv]
      exact sum_congr rfl hih
    rw [hmt] at hsum
    rw [hmt, show k + (t + 1) - k = t + 1 by omega]
    apply nsmul_right_injective (by omega : t + 1 ≠ 0)
    push_cast
    linear_combination ((k : R) + (t + 1)) * hsum + hcoeff

/-- **Lagrange inversion for powers.** If `Y = X * P(Y)`, then
`(n + k) * [X^(n+k)] Y^k = k * [X^n] P^(n+k)` for all natural numbers `n` and `k`.

The coefficient ring is assumed to have no additive torsion because the inductive proof cancels
multiplication by a positive natural number. -/
theorem lagrange_inversion_coeff_pow
    (hY : Y = X * P.subst Y) (n k : ℕ) :
    ((n + k : ℕ) : R) * coeff (n + k) (Y ^ k) =
      (k : R) * (P ^ (n + k)).coeff n := by
  rcases eq_or_ne (n + k) 0 with hnk | hnk
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hnk
    simp
  · simpa [show n + k - 1 + 1 = n + k by omega] using
      lagrange_inversion_coeff_pow_of_le hY (n + k - 1) k (by omega)

/-- **Lagrange–Bürmann formula.** If `Y = X * P(Y)`, then for a natural number `n` and
a formal power series `H`,

`(n + 1) * [X^(n+1)] H(Y) = [X^n] (H' * P^(n+1))`. -/
theorem lagrange_burmann_coeff
    (hY : Y = X * P.subst Y) (n : ℕ) (H : R⟦X⟧) :
    ((n + 1 : ℕ) : R) * coeff (n + 1) (H.subst Y) =
      (d⁄dX H * P ^ (n + 1)).coeff n := by
  have hlhs : ((n + 1 : ℕ) : R) * coeff (n + 1) (H.subst Y) =
        ∑ i ∈ range (n + 2), H.coeff i * ((i : R) * (P ^ (n + 1)).coeff (n + 1 - i)) := by
    rw [coeff_subst_of_fixedPoint hY H, mul_sum]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [mem_range_succ_iff] at hi
    simp only [← lagrange_inversion_coeff_pow_of_le hY n i hi]
    ring
  rw [hlhs, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ']
  grind [coeff_derivative]

end TorsionFree

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The usual coefficient form of the formal Lagrange inversion formula. This is the
case `H = X`, equivalently `k = 1`, of `lagrange_burmann_coeff`. -/
theorem lagrange_inversion_coeff (P Y : K⟦X⟧)
    (hY : Y = X * P.subst Y) (n : ℕ) :
    coeff (n + 1) Y = (P ^ (n + 1)).coeff n / (n + 1) := by
  field_simp [Nat.cast_add_one_ne_zero n]
  simpa [mul_comm] using lagrange_inversion_coeff_pow (P := P) hY n 1

end Field

end PowerSeries

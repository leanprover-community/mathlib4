/-
Copyright (c) 2026 Seiichi Manyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seiichi Manyama
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Lagrange inversion formula for formal power series

This file proves the one-variable Lagrange inversion formula over a commutative ring.
Let `P` and `Y` be formal power series satisfying

`Y = X * P(Y)`.

Then, for natural numbers `n` and `k`,

`(n + k) * [X ^ (n + k)] Y ^ k = k * [X ^ n] P ^ (n + k)`.

We also give the Lagrange–Bürmann form

`(n + 1) * [X ^ (n + 1)] H(Y) = [X ^ n] (H' * P ^ (n + 1))`

for a formal power series `H`. When `n + 1` is a unit, this gives a coefficient formula using
its inverse; over a field of characteristic zero, it gives the usual divided formulas.

## Main results

* `PowerSeries.existsUnique_fixedPoint`: existence and uniqueness of a solution of
  `Y = X * P(Y)`.
* `PowerSeries.fixedPoint_unique`: any two solutions of the fixed-point equation are equal.
* `PowerSeries.eq_zero_of_fixedPoint_of_constantCoeff_eq_zero`: the degenerate case where the
  constant coefficient of `P` is zero.
* `PowerSeries.lagrange_burmann_coeff`: the Lagrange–Bürmann coefficient formula over a
  commutative ring.
* `PowerSeries.lagrange_inversion_coeff_pow`: the coefficient formula for powers of `Y`.
* `PowerSeries.lagrange_burmann_coeff_of_isUnit`: the coefficient formula when `n + 1` is a unit.
* `PowerSeries.lagrange_burmann_coeff_div`: the divided Lagrange–Bürmann formula over a field of
  characteristic zero.
* `PowerSeries.lagrange_inversion_coeff`: the usual divided coefficient formula over a field of
  characteristic zero.

## Implementation details

We first prove the formulas over rings without additive torsion, following the induction in the
reference below. Specializing the coefficients of power series over `MvPolynomial (ℕ ⊕ ℕ) ℤ`
then gives the division-free formulas over arbitrary commutative rings. Fixed-point uniqueness
identifies the specialized solution.

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

/-- Solutions of `Y = X * P(Y)` over a commutative ring are unique. -/
theorem fixedPoint_unique {Z : R⟦X⟧} (hY : Y = X * P.subst Y)
    (hZ : Z = X * P.subst Z) : Y = Z := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp [constantCoeff_eq_zero hY, constantCoeff_eq_zero hZ]
    | succ n =>
      rw [hY, hZ, coeff_succ_X_mul, coeff_succ_X_mul]
      apply coeff_subst_congr (constantCoeff_eq_zero hY) (constantCoeff_eq_zero hZ)
      intro j hj
      exact ih j (by omega)

private noncomputable def fixedPointApprox (P : R⟦X⟧) : ℕ → R⟦X⟧
  | 0 => 0
  | n + 1 => X * P.subst (fixedPointApprox P n)

private lemma constantCoeff_fixedPointApprox (P : R⟦X⟧) (n : ℕ) :
    (fixedPointApprox P n).constantCoeff = 0 := by
  cases n <;> simp [fixedPointApprox]

private lemma coeff_fixedPointApprox_stable (P : R⟦X⟧) (n s j : ℕ) (hj : j < n) :
    (fixedPointApprox P n).coeff j = (fixedPointApprox P (n + s)).coeff j := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [constantCoeff_fixedPointApprox]
    | succ j =>
      simp only [Nat.succ_add, fixedPointApprox, coeff_succ_X_mul]
      apply coeff_subst_congr (constantCoeff_fixedPointApprox P n)
        (constantCoeff_fixedPointApprox P (n + s))
      intro i hi
      exact ih i (by omega)

private noncomputable def fixedPointSolution (P : R⟦X⟧) : R⟦X⟧ :=
  mk fun n ↦ (fixedPointApprox P (n + 1)).coeff n

private lemma coeff_fixedPointSolution_eq_approx (P : R⟦X⟧) {n j : ℕ} (hj : j < n) :
    (fixedPointSolution P).coeff j = (fixedPointApprox P n).coeff j := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
  rw [fixedPointSolution, coeff_mk]
  exact coeff_fixedPointApprox_stable P (j + 1) s j (by omega)

@[simp] private lemma constantCoeff_fixedPointSolution (P : R⟦X⟧) :
    (fixedPointSolution P).constantCoeff = 0 := by
  rw [fixedPointSolution, constantCoeff_mk]
  simpa only [coeff_zero_eq_constantCoeff_apply] using constantCoeff_fixedPointApprox P 1

private theorem fixedPointSolution_fixedPoint (P : R⟦X⟧) :
    fixedPointSolution P = X * P.subst (fixedPointSolution P) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [fixedPointSolution, fixedPointApprox, coeff_mk, coeff_succ_X_mul]
    apply coeff_subst_congr (constantCoeff_fixedPointApprox P (n + 1))
      (constantCoeff_fixedPointSolution P)
    intro j hj
    exact (coeff_fixedPointSolution_eq_approx P (by omega : j < n + 1)).symm

/-- Existence and uniqueness of a solution of `Y = X * P(Y)`. -/
theorem existsUnique_fixedPoint (P : R⟦X⟧) : ∃! Y : R⟦X⟧, Y = X * P.subst Y :=
  ⟨fixedPointSolution P, fixedPointSolution_fixedPoint P, fun _ hY ↦
    fixedPoint_unique hY (fixedPointSolution_fixedPoint P)⟩

variable (hY : Y = X * P.subst Y)
include hY

/-- If `Y = X * P(Y)` and the constant coefficient of `P` is zero, then `Y = 0`. -/
theorem eq_zero_of_fixedPoint_of_constantCoeff_eq_zero (hP : P.constantCoeff = 0) : Y = 0 := by
  apply fixedPoint_unique hY
  simp [hP]

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

end TorsionFree

section CommRing

variable {R : Type*} [CommRing R]
variable {P Y : R⟦X⟧}
variable (hY : Y = X * P.subst Y)
include hY

/-- **Lagrange–Bürmann formula.** If `Y = X * P(Y)`, then for a natural number `n` and
a formal power series `H`,

`(n + 1) * [X ^ (n + 1)] H(Y) = [X ^ n] (H' * P ^ (n + 1))`. -/
theorem lagrange_burmann_coeff (n : ℕ) (H : R⟦X⟧) :
    (n + 1) • coeff (n + 1) (H.subst Y) = (d⁄dX H * P ^ (n + 1)).coeff n := by
  let U := MvPolynomial (ℕ ⊕ ℕ) ℤ
  let : HasUniqueDiv U := AddMonoidAlgebra.coeff_injective.hasUniqueDiv
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom
  let P₀ : U⟦X⟧ := mk fun i ↦ MvPolynomial.X (Sum.inl i)
  let H₀ : U⟦X⟧ := mk fun i ↦ MvPolynomial.X (Sum.inr i)
  obtain ⟨Y₀, hY₀, _⟩ := existsUnique_fixedPoint P₀
  have hcoeff : (n + 1) • coeff (n + 1) (H₀.subst Y₀) =
      (d⁄dX H₀ * P₀ ^ (n + 1)).coeff n := by
    rw [coeff_subst_of_constantCoeff_zero (constantCoeff_eq_zero hY₀) H₀, smul_sum,
      coeff_derivative_mul]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [← mul_smul_comm, lagrange_inversion_coeff_pow_of_le hY₀ (mem_range_succ_iff.mp hi)]
  let e : U →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    (Sum.elim (fun i ↦ P.coeff i) (fun i ↦ H.coeff i))
  have hP : map e P₀ = P := by
    ext i
    simp [P₀, e, U, coeff_map]
  have hH : map e H₀ = H := by
    ext i
    simp [H₀, e, U, coeff_map]
  have hmap_subst (F : U⟦X⟧) : map e (F.subst Y₀) = (map e F).subst (map e Y₀) :=
    map_subst (hasSubst_of_fixedPoint hY₀) F
  have hmapY : map e Y₀ = Y := by
    apply fixedPoint_unique _ hY
    simpa [hmap_subst, hP] using congrArg (map e) hY₀
  simpa [← coeff_map, hmap_subst, map_derivative, hH, hP, hmapY] using congrArg e hcoeff

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

end CommRing

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

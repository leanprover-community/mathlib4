/-
Copyright (c) 2026 Seiichi Manyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seiichi Manyama
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Fixed points of power series substitution

For a formal power series `P`, the equation `Y = X * P.subst Y` has a unique solution
over any commutative ring. Its coefficients are obtained by iterating `Y ↦ X * P.subst Y`
from zero; the coefficient of degree `n` stabilizes after `n + 1` iterations.

## Main results

* `PowerSeries.existsUnique_fixedPoint`: existence and uniqueness of a solution of
  `Y = X * P.subst Y`.
* `PowerSeries.fixedPoint_unique`: any two solutions of the fixed-point equation are equal.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

private lemma coeff_pow_congr {f g : R⟦X⟧} (n k : ℕ)
    (h : ∀ j ≤ n, f.coeff j = g.coeff j) : (f ^ k).coeff n = (g ^ k).coeff n := by
  have ht : f.trunc (n + 1) = g.trunc (n + 1) := by
    ext j
    by_cases hj : j < n + 1
    · simp [coeff_trunc, hj, h j (by omega)]
    · simp [coeff_trunc, hj]
  have hp : (f ^ k).trunc (n + 1) = (g ^ k).trunc (n + 1) := by
    rw [← trunc_trunc_pow f, ht, trunc_trunc_pow]
  simpa [coeff_trunc] using congrArg (fun p : Polynomial R ↦ p.coeff n) hp

private lemma coeff_subst_congr {f g : R⟦X⟧} (hf : f.constantCoeff = 0)
    (hg : g.constantCoeff = 0) (P : R⟦X⟧) (n : ℕ)
    (h : ∀ j ≤ n, f.coeff j = g.coeff j) : coeff n (P.subst f) = coeff n (P.subst g) := by
  rw [coeff_subst_of_constantCoeff_zero hf, coeff_subst_of_constantCoeff_zero hg]
  exact Finset.sum_congr rfl fun k _ ↦ congrArg (P.coeff k * ·) (coeff_pow_congr n k h)

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
    | zero => simp only [coeff_zero_eq_constantCoeff_apply, constantCoeff_fixedPointApprox]
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
    nth_rw 1 [fixedPointSolution]
    rw [coeff_mk, fixedPointApprox, coeff_succ_X_mul, coeff_succ_X_mul]
    apply coeff_subst_congr (constantCoeff_fixedPointApprox P (n + 1))
      (constantCoeff_fixedPointSolution P)
    intro j hj
    exact (coeff_fixedPointSolution_eq_approx P (by omega : j < n + 1)).symm

private theorem eq_fixedPointSolution_of_fixedPoint {P Y : R⟦X⟧}
    (hY : Y = X * P.subst Y) : Y = fixedPointSolution P := by
  have hY₀ : Y.constantCoeff = 0 := by simpa using congrArg constantCoeff hY
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using hY₀
    | succ n =>
      nth_rw 1 [hY]
      rw [fixedPointSolution_fixedPoint P, coeff_succ_X_mul, coeff_succ_X_mul]
      apply coeff_subst_congr hY₀ (constantCoeff_fixedPointSolution P)
      intro j hj
      exact ih j (by omega)

/-- Existence and uniqueness of a solution of `Y = X * P(Y)`. -/
theorem existsUnique_fixedPoint (P : R⟦X⟧) : ∃! Y : R⟦X⟧, Y = X * P.subst Y :=
  ⟨fixedPointSolution P, fixedPointSolution_fixedPoint P, fun _ hY ↦
    eq_fixedPointSolution_of_fixedPoint hY⟩

/-- Solutions of `Y = X * P(Y)` over a commutative ring are unique. -/
theorem fixedPoint_unique {P Y Z : R⟦X⟧} (hY : Y = X * P.subst Y)
    (hZ : Z = X * P.subst Z) : Y = Z :=
  (eq_fixedPointSolution_of_fixedPoint hY).trans (eq_fixedPointSolution_of_fixedPoint hZ).symm

end PowerSeries

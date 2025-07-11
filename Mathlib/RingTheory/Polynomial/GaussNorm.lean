/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

import Mathlib.RingTheory.PowerSeries.GaussNorm

/-!
# Gauss norm for polynomials
This file defines the Gauss norm for polynomials. Given a polynomial `p` in `R[X]`, a function
`v : R → ℝ` and a real number `c`, the Gauss norm is defined as the supremum of the set of all
values of `v (p.coeff i) * c ^ i` for all `i` in the support of `p`.

In the file `Mathlib/RingTheory/PowerSeries/GaussNorm.lean`, the Gauss norm is defined for power
series. This is a generalization of the Gauss norm defined in this file in case `v` is a
non-negative function with `v 0 = 0` and `c ≥ 0`.

## Main Definitions and Results
* `Polynomial.gaussNorm` is the supremum of the set of all values of `v (p.coeff i) * c ^ i`
  for all `i` in the support of `p`, where `p` is a polynomial in `R[X]`, `v : R → ℝ` is a function
  and `c` is a  real number.
* `Polynomial.gaussNorm_coe_powerSeries`: if `v` is a non-negative function with `v 0 = 0` and `c`
  is nonnegative, the Gauss norm of a polynomial is equal to its Gauss norm as a power series.
* `Polynomial.gaussNorm_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.
* `Polynomial.gaussNorm_eq_zero_iff`: if `v x = 0 ↔ x = 0` for all `x : R`, then the Gauss
  norm is zero if and only if the polynomial is zero.
-/
variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ)

namespace Polynomial

variable (p : R[X])

/-- Given a polynomial `p` in `R[X]`, a function `v : R → ℝ` and a real number `c`, the Gauss norm
is defined as the supremum of the set of all values of `v (p.coeff i) * c ^ i` for all `i` in the
support of `p`. -/
def gaussNorm : ℝ := if h : p.support.Nonempty then p.support.sup' h fun i ↦
    (v (p.coeff i) * c ^ i) else 0

@[simp]
lemma gaussNorm_zero : gaussNorm v c 0 = 0 := by simp [gaussNorm]

theorem exists_eq_gaussNorm [ZeroHomClass F R ℝ] :
    ∃ i, p.gaussNorm v c = v (p.coeff i) * c ^ i := by
  by_cases h_supp : p.support.Nonempty
  · simp only [gaussNorm, h_supp]
    obtain ⟨i, hi1, hi2⟩ := Finset.exists_mem_eq_sup' h_supp fun i ↦ (v (p.coeff i) * c ^ i)
    exact ⟨i, hi2⟩
  · simp_all

@[simp]
lemma gaussNorm_C [ZeroHomClass F R ℝ] (r : R) : (C r).gaussNorm v c = v r := by
  by_cases hr : r = 0 <;> simp [gaussNorm, support_C, hr]

@[simp]
theorem gaussNorm_monomial [ZeroHomClass F R ℝ] (n : ℕ) (r : R) :
    (monomial n r).gaussNorm v c = v r * c ^ n := by
  by_cases hr : r = 0 <;> simp [gaussNorm, support_monomial, hr]

variable {c}

private lemma sup'_nonneg_of_ne_zero [NonnegHomClass F R ℝ] {p : R[X]} (h : p.support.Nonempty)
    (hc : 0 ≤ c) : 0 ≤ p.support.sup' h fun i ↦ (v (p.coeff i) * c ^ i) := by
  simp only [Finset.le_sup'_iff, mem_support_iff]
  use p.natDegree
  simp_all only [support_nonempty, ne_eq, coeff_natDegree, leadingCoeff_eq_zero, not_false_eq_true,
    true_and]
  positivity

private lemma aux_bdd [ZeroHomClass F R ℝ] : BddAbove {x | ∃ i, v (p.coeff i) * c ^ i = x} := by
  let f : p.support → ℝ := fun i ↦ v (p.coeff i) * c ^ i.val
  have h_fin : (f '' ⊤ ∪ {0}).Finite := by
    apply Set.Finite.union _ <| Set.finite_singleton 0
    apply Set.Finite.image f
    rw [Set.top_eq_univ, Set.finite_univ_iff, ← @Finset.coe_sort_coe]
    exact Finite.of_fintype p.support
  apply Set.Finite.bddAbove <| Set.Finite.subset h_fin _
  intro x hx
  obtain ⟨i, hi⟩ := hx
  rw [← hi]
  by_cases hi : i ∈ p.support
  · left
    use ⟨i, hi⟩
    simp [f]
  · right
    simp [Polynomial.notMem_support_iff.mp hi]

@[simp]
theorem gaussNorm_coe_powerSeries [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]
    (hc : 0 ≤ c) : (p.toPowerSeries).gaussNorm v c = p.gaussNorm v c := by
  by_cases hp : p = 0
  · simp [hp]
  · simp only [PowerSeries.gaussNorm, coeff_coe, gaussNorm, support_nonempty, ne_eq, hp,
      not_false_eq_true, ↓reduceDIte]
    apply le_antisymm
    · apply ciSup_le
      intro n
      by_cases h : n ∈ p.support
      · exact Finset.le_sup' (fun j ↦ v (p.coeff j) * c ^ j) h
      · simp_all [sup'_nonneg_of_ne_zero v (support_nonempty.mpr hp) hc]
    · obtain ⟨i, hi⟩ := exists_eq_gaussNorm v c p
      simp only [gaussNorm, support_nonempty.mpr hp, ↓reduceDIte] at hi
      rw [hi]
      exact le_ciSup (aux_bdd v p) i

@[simp]
theorem gaussNorm_eq_zero_iff [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : 0 < c) : p.gaussNorm v c = 0 ↔ p = 0 := by
  rw [← gaussNorm_coe_powerSeries _ _ (le_of_lt hc),
    PowerSeries.gaussNorm_eq_zero_iff h_eq_zero hc (by simpa only [coeff_coe] using aux_bdd v p),
    coe_eq_zero_iff]

theorem gaussNorm_nonneg (hc : 0 ≤ c) [NonnegHomClass F R ℝ] : 0 ≤ p.gaussNorm v c := by
  by_cases hp : p.support.Nonempty <;>
  simp_all [gaussNorm, sup'_nonneg_of_ne_zero, -Finset.le_sup'_iff]

lemma le_gaussNorm [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] (hc : 0 ≤ c) (i : ℕ) :
    v (p.coeff i) * c ^ i ≤ p.gaussNorm v c := by
  rw [← gaussNorm_coe_powerSeries _ _ hc, ← coeff_coe]
  apply PowerSeries.le_gaussNorm
  simpa using aux_bdd v p

end Polynomial

namespace PowerSeries

variable {c} (r : R)

@[simp]
theorem gaussNorm_C [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] (hc : 0 ≤ c) :
    (C R r).gaussNorm v c = v r := by
  simp [← Polynomial.coe_C, hc]

@[simp]
theorem gaussNorm_monomial [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] (hc : 0 ≤ c) (n : ℕ) :
    (monomial R n r).gaussNorm v c = v r * c ^ n := by
  simp [← Polynomial.coe_monomial, hc]

end PowerSeries

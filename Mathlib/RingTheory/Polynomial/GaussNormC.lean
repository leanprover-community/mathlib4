/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
--import Mathlib
import Mathlib.RingTheory.PowerSeries.GaussNormC
/-!
# Gauss norm for polynomials
This file defines the Gauss norm for polynomials. Given a polynomial `p` in `R[X]`, a function
`v : R → ℝ` and a real number `c`, the Gauss norm is defined as the supremum of the set of all
values of `v (p.coeff i) * c ^ i` for all `i` in the support of `p`.

## Main Definitions and Results
* `Polynomial.gaussNormC` is the supremum of the set of all values of `v (p.coeff i) * c ^ i`
  for all `i` in the support of `p`, where `p` is a polynomial in `R[X]`, `v : R → ℝ` is a function
  and `c` is a  real number.
* `Polynomial.gaussNormC_coe_powerSeries`: the Gauss norm of a polynomial is equal to its
  Gauss norm as a power series.
* `Polynomial.gaussNormC_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.
* `Polynomial.gaussNormC_eq_zero_iff`: if `v x = 0 ↔ x = 0` for all `x : R`, then the Gauss
  norm is zero if and only if the polynomial is zero.
-/
variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ)

namespace Polynomial

variable (p : R[X])

/-- Given a polynomial `p` in `R[X]`, a function `v : R → ℝ` and a real number `c`, the Gauss norm
is defined as the supremum of the set of all values of `v (p.coeff i) * c ^ i` for all `i` in the
support of `p`. -/
def gaussNormC : ℝ := if h : p.support.Nonempty then p.support.sup' h fun i ↦
    (v (p.coeff i) * c ^ i) else 0

@[simp]
lemma gaussNormC_zero : gaussNormC v c 0 = 0 := by simp [gaussNormC]

theorem exists_eq_gaussNormC [ZeroHomClass F R ℝ] :
    ∃ i, p.gaussNormC v c = v (p.coeff i) * c ^ i := by
  by_cases h_supp : p.support.Nonempty
  · simp only [gaussNormC, h_supp]
    obtain ⟨i, hi1, hi2⟩ := Finset.exists_mem_eq_sup' h_supp fun i ↦ (v (p.coeff i) * c ^ i)
    exact ⟨i, hi2⟩
  · simp_all

private lemma sup'_nonneg_of_ne_zero [NonnegHomClass F R ℝ] {p : R[X]} (h : p.support.Nonempty)
    {c : ℝ} (hc : 0 ≤ c) : 0 ≤ p.support.sup' h fun i ↦ (v (p.coeff i) * c ^ i) := by
  simp only [Finset.le_sup'_iff, mem_support_iff]
  use p.natDegree
  simp_all only [support_nonempty, ne_eq, coeff_natDegree, leadingCoeff_eq_zero, not_false_eq_true,
    true_and]
  positivity

private lemma aux_bdd [ZeroHomClass F R ℝ] : BddAbove {x | ∃ i, v (p.coeff i) * c ^ i = x} := by
  let f : p.support → ℝ := fun i ↦ v (p.coeff i) * c ^ i.1
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
    simp [not_mem_support_iff.mp hi]

@[simp]
theorem gaussNormC_coe_powerSeries [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]
    {c : ℝ} (hc : 0 ≤ c) : (p.toPowerSeries).gaussNormC v c = p.gaussNormC v c:= by
  by_cases hp : p = 0
  · simp [hp]
  · have h_supp : p.support.Nonempty := support_nonempty.mpr hp
    simp only [PowerSeries.gaussNormC, coeff_coe, gaussNormC, support_nonempty, ne_eq, hp,
      not_false_eq_true, ↓reduceDIte]
    apply le_antisymm
    · apply ciSup_le
      intro n
      by_cases h : n ∈ p.support
      · exact Finset.le_sup' (fun j ↦ v (p.coeff j) * c ^ j) h
      · simp_all [sup'_nonneg_of_ne_zero v h_supp hc]
    · obtain ⟨i, hi⟩ := exists_eq_gaussNormC v c p
      simp only [gaussNormC, h_supp, ↓reduceDIte] at hi
      rw [hi]
      exact le_ciSup (aux_bdd v c p) i

@[simp]
theorem gaussNormC_eq_zero_iff [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) {c : ℝ} (hc : 0 < c) : p.gaussNormC v c = 0 ↔ p = 0 := by
  rw [← gaussNormC_coe_powerSeries _ _ (le_of_lt hc),
    PowerSeries.gaussNormC_eq_zero_iff h_eq_zero hc (by simpa only [coeff_coe] using aux_bdd v c p),
    coe_eq_zero_iff]

theorem gaussNormC_nonneg {c : ℝ} (hc : 0 ≤ c) [NonnegHomClass F R ℝ] : 0 ≤ p.gaussNormC v c := by
  by_cases hp : p.support.Nonempty
  · simp_all [gaussNormC, sup'_nonneg_of_ne_zero, -Finset.le_sup'_iff]
  · simp [gaussNormC, hp]

@[simp]
lemma gaussNormC_C [ZeroHomClass F R ℝ] (r : R) : (C r).gaussNormC v c = v r := by
  by_cases hr : r = 0 <;> simp [gaussNormC, support_C, hr]

@[simp]
theorem gaussNormC_monomial [ZeroHomClass F R ℝ] (n : ℕ) (r : R) :
    (monomial n r).gaussNormC v c = v r * c ^ n := by
  by_cases hr : r = 0 <;> simp [gaussNormC, support_monomial, hr]

lemma le_gaussNormC [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] (p : R[X]) {c : ℝ}
    (hc : 0 ≤ c) (i : ℕ) : v (p.coeff i) * c ^ i ≤ p.gaussNormC v c := by
  rw [← gaussNormC_coe_powerSeries _ _ hc, ← coeff_coe]
  apply PowerSeries.le_gaussNormC
  simpa using aux_bdd v c p

end Polynomial

namespace PowerSeries

@[simp]
theorem gaussNormC_C [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] {c : ℝ} (hc : 0 ≤ c) (r : R) :
    (C R r).gaussNormC v c = v r := by
  simp [← @Polynomial.coe_C, hc]

@[simp]
theorem gaussNormC_monomial [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] {c : ℝ} (hc : 0 ≤ c)
    (n : ℕ) (r : R) : (monomial R n r).gaussNormC v c = v r * c ^ n := by
  simp [← @Polynomial.coe_monomial, hc]

end PowerSeries

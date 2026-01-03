/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.Algebra.MvPolynomial.Division

/-! # Some lemmas about the degree lexicographic monomial order on multivariate polynomials -/

@[expose] public section

namespace MvPolynomial

open MonomialOrder Finsupp

open scoped MonomialOrder

variable {σ : Type*} {R : Type*}

section CommSemiring

variable [CommSemiring R] {f g : MvPolynomial σ R}

section LinearOrder

variable [LinearOrder σ] [WellFoundedGT σ]

theorem degree_degLexDegree : (degLex.degree f).degree = f.totalDegree := by
  by_cases hf : f = 0
  · simp [hf]
  apply le_antisymm
  · exact le_totalDegree (degLex.degree_mem_support hf)
  · unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro b hb
    exact DegLex.monotone_degree (degLex.le_degree hb)

theorem degLex_totalDegree_monotone (h : degLex.degree f ≼[degLex] degLex.degree g) :
    f.totalDegree ≤ g.totalDegree := by
  simp only [← MvPolynomial.degree_degLexDegree]
  exact DegLex.monotone_degree h

end LinearOrder

section IsCancelMulZero

variable [NoZeroDivisors R]

theorem totalDegree_mul_of_isDomain (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  cases exists_wellOrder σ
  rw [← degree_degLexDegree (σ := σᵒᵈ), ← degree_degLexDegree (σ := σᵒᵈ),
    ← degree_degLexDegree (σ := σᵒᵈ), MonomialOrder.degree_mul hf hg]
  simp

theorem totalDegree_le_of_dvd_of_isDomain (h : f ∣ g) (hg : g ≠ 0) :
    f.totalDegree ≤ g.totalDegree := by
  obtain ⟨r, rfl⟩ := h
  rw [totalDegree_mul_of_isDomain]
  · exact Nat.le_add_right f.totalDegree r.totalDegree
  · exact fun h ↦ hg (by simp [h])
  · exact fun h ↦ hg (by simp [h])

theorem dvd_C_iff_exists {a : R} (ha : a ≠ 0) :
    f ∣ C a ↔ ∃ b, b ∣ a ∧ f = C b := by
  constructor
  · intro hf
    use MvPolynomial.coeff 0 f
    suffices f.totalDegree = 0 by
      rw [totalDegree_eq_zero_iff_eq_C] at this
      refine ⟨?_, this⟩
      rw [this, C_dvd_iff_dvd_coeff] at hf
      convert hf 0
      simp
    apply Nat.eq_zero_of_le_zero
    convert totalDegree_le_of_dvd_of_isDomain hf (by simp [ha])
    simp
  · rintro ⟨b, hab, rfl⟩
    exact _root_.map_dvd MvPolynomial.C hab

end IsCancelMulZero

end CommSemiring

section CommRing

variable [CommRing R] [NoZeroDivisors R] {p q r : MvPolynomial σ R}

theorem dvd_monomial_iff_exists {n : σ →₀ ℕ} {a : R} (ha : a ≠ 0) :
    p ∣ monomial n a ↔ ∃ m b, m ≤ n ∧ b ∣ a ∧ p = monomial m b := by
  rw [show monomial n a = monomial n 1 * C a by rw [mul_comm, C_mul_monomial, mul_one],
    dvd_monomial_mul_iff_exists]
  apply exists_congr
  intro m
  constructor
  · rintro ⟨r, hmn, hr, h⟩
    rw [dvd_C_iff_exists ha] at hr
    obtain ⟨b, hb, hr⟩ := hr
    use b, hmn, hb
    rw [h, mul_comm, hr, C_mul_monomial, mul_one]
  · rintro ⟨b, hmn, hb, h⟩
    use C b, hmn, map_dvd C hb
    rwa [mul_comm, C_mul_monomial, mul_one]

theorem dvd_monomial_one_iff_exists {n : σ →₀ ℕ} :
    p ∣ monomial n 1 ↔ ∃ m u, m ≤ n ∧ IsUnit u ∧ p = monomial m u := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · suffices ∃ m, m ≤ n by simpa [Subsingleton.elim _ p]
    use n
  rw [dvd_monomial_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro m
  simp_rw [isUnit_iff_dvd_one]

theorem dvd_X_iff_exists {i : σ} :
    p ∣ X i ↔ ∃ r, IsUnit r ∧ (p = C r ∨ p = r • X i) := by
  rw [X, dvd_monomial_one_iff_exists, exists_comm]
  apply exists_congr
  intro b
  constructor
  · rintro ⟨m, hmn, hb, rfl⟩
    simp only [hb, true_and]
    suffices m = 0 ∨ m = Finsupp.single i 1 by
      apply this.imp <;> simp +contextual [smul_monomial, smul_eq_mul, mul_one]
    by_cases hm : m i = 0
    · left
      ext j
      simp only [Finsupp.coe_zero, Pi.zero_apply, ← Nat.le_zero]
      by_cases hj : j = i
      · rw [← hm, hj]
      · exact (hmn j).trans (Finsupp.single_eq_of_ne hj).le
    · right
      ext j
      apply le_antisymm (hmn j)
      by_cases hj : j = i
      · simpa [hj, Nat.one_le_iff_ne_zero]
      · simp [Finsupp.single_eq_of_ne hj]
  · rintro ⟨hb, hp | hp⟩
    · use 0; simp [hb, hp]
    · use Finsupp.single i 1, le_rfl, hb
      simp [hp, smul_monomial]

end CommRing

end MvPolynomial

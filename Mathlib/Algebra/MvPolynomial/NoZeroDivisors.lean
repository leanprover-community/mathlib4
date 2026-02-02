/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Bolton Bailey
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
public import Mathlib.Algebra.MvPolynomial.Division

/-!
# Multivariate polynomials over integral domains

This file proves results about multivariate polynomials
that hold when the coefficient (semi)ring has no zero divisors.

-/

public section

open Finset Equiv

variable {R : Type*}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R]

variable {p q : MvPolynomial σ R}

section NoZeroDivisors

variable [NoZeroDivisors R]

section DegreeOf

lemma degreeOf_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) :
    degreeOf n (p * q) = degreeOf n p + degreeOf n q := by
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul] <;> simpa [-renameEquiv_apply, EmbeddingLike.map_eq_zero_iff]

lemma degreeOf_prod_eq {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R)
    (h : ∀ i ∈ s, f i ≠ 0) :
    degreeOf n (∏ i ∈ s, f i) = ∑ i ∈ s, degreeOf n (f i) := by
  rcases subsingleton_or_nontrivial (MvPolynomial σ R) with nontrivial | nontrivial
  · simp [Subsingleton.eq_zero]
  · classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s a_not_mem ih =>
      simp only [mem_insert, ne_eq, forall_eq_or_imp] at h
      obtain ⟨ha, hs⟩ := h
      simp [a_not_mem, not_false_eq_true, prod_insert, sum_insert, degreeOf_mul_eq ha
        (by rw [prod_ne_zero_iff]; exact hs), ih hs]

theorem degreeOf_pow_eq (i : σ) (p : MvPolynomial σ R) (n : ℕ) (hp : p ≠ 0) :
    degreeOf i (p ^ n) = n * degreeOf i p := by
  rw [pow_eq_prod_const, degreeOf_prod_eq (range n) (fun _ ↦ p) (fun _ _ ↦ hp)]
  simp

end DegreeOf

section Degrees

lemma degrees_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) :
    degrees (p * q) = degrees p + degrees q := by
  classical
  ext s
  simp_rw [Multiset.count_add, ← degreeOf_def, degreeOf_mul_eq hp hq]

end Degrees

theorem totalDegree_mul_of_isDomain {f g : MvPolynomial σ R}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  cases exists_wellOrder σ
  simp [← degree_degLexDegree (σ := σᵒᵈ), MonomialOrder.degree_mul hf hg]

theorem totalDegree_le_of_dvd_of_isDomain {f g : MvPolynomial σ R}
    (h : f ∣ g) (hg : g ≠ 0) :
    f.totalDegree ≤ g.totalDegree := by
  obtain ⟨r, rfl⟩ := h
  rw [totalDegree_mul_of_isDomain (by aesop) (by aesop)]
  lia

theorem dvd_C_iff_exists {f : MvPolynomial σ R} {a : R} (ha : a ≠ 0) :
    f ∣ C a ↔ ∃ b, b ∣ a ∧ f = C b := by
  constructor
  · intro hf
    use coeff 0 f
    suffices f.totalDegree = 0 by
      rw [totalDegree_eq_zero_iff_eq_C] at this
      refine ⟨?_, this⟩
      rw [this, C_dvd_iff_dvd_coeff] at hf
      simpa using hf 0
    apply Nat.eq_zero_of_le_zero
    simpa using totalDegree_le_of_dvd_of_isDomain hf (by simp [ha])
  · rintro ⟨b, hab, rfl⟩
    exact map_dvd C hab

end NoZeroDivisors

section nonZeroDivisors

open nonZeroDivisors

theorem degreeOf_C_mul (j : σ) (c : R) (hc : c ∈ R⁰) : degreeOf j (C c * p) = degreeOf j p := by
  by_cases hp : p = 0
  · simp [hp]
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul']
  · simp
  · have hp' : (optionEquivLeft R _ ((rename (optionSubtypeNe j).symm) p)).leadingCoeff ≠ 0 := by
      intro h
      exact hp (rename_injective _ (Equiv.injective _) (by simpa using h))
    simp_rw [ne_eq, renameEquiv_apply, algHom_C, algebraMap_eq, optionEquivLeft_C,
      Polynomial.leadingCoeff_C]
    contrapose! hp'
    ext m
    apply hc.1
    simpa using congr_arg (coeff m) hp'

end nonZeroDivisors

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

theorem dvd_smul_X_iff_exists {i : σ} {r : R} (hr : r ≠ 0) :
    p ∣ r • X i ↔ ∃ s, s ∣ r ∧ (p = C s ∨ p = s • X i) := by
  rw [X, smul_monomial, smul_eq_mul, mul_one, dvd_monomial_iff_exists hr, exists_comm]
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

theorem dvd_X_iff_exists {i : σ} :
    p ∣ X i ↔ ∃ r, IsUnit r ∧ (p = C r ∨ p = r • X i) := by
  nontriviality R
  rw [← one_smul R (X i), dvd_smul_X_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro r
  rw [isUnit_iff_dvd_one, one_smul]

end CommRing

end MvPolynomial

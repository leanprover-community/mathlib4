/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-! # Some lemmas about the deglex monomial order on multivariate polynomials -/

namespace MvPolynomial

open MonomialOrder Finsupp

open scoped MonomialOrder

variable {σ : Type*} {R : Type*} [CommSemiring R] {f g : MvPolynomial σ R}

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

variable [NoZeroDivisors R]

theorem totalDegree_mul_of_noZeroDivisors (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  cases exists_wellOrder σ
  rw [← degree_degLexDegree (σ := σᵒᵈ), ← degree_degLexDegree (σ := σᵒᵈ),
    ← degree_degLexDegree (σ := σᵒᵈ), MonomialOrder.degree_mul hf hg]
  simp

@[deprecated (since := "2025-07-19")]
alias totalDegree_mul_of_isDomain := totalDegree_mul_of_noZeroDivisors

theorem totalDegree_mul_of_mul_ne_zero (h : f * g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  rw [mul_ne_zero_iff] at h
  exact totalDegree_mul_of_noZeroDivisors h.1 h.2

theorem isUnit_iff_eq_C_of_noZeroDivisors : IsUnit f ↔ ∃ r : R, IsUnit r ∧ f = C r where
  mp h := by
    nontriviality R
    have ⟨g, eq⟩ := h.exists_right_inv
    have eq' := congr(totalDegree $eq)
    rw [totalDegree_mul_of_mul_ne_zero (eq ▸ one_ne_zero),
      totalDegree_one, add_eq_zero, totalDegree_eq_zero_iff_eq_C] at eq'
    exact ⟨_, h.map constantCoeff, eq'.1⟩
  mpr := by rintro ⟨r, hr, rfl⟩; exact hr.map C

theorem totalDegree_eq_zero_of_isUnit (h : IsUnit f) : totalDegree f = 0 := by
  obtain ⟨r, -, rfl⟩ := isUnit_iff_eq_C_of_noZeroDivisors.mp h
  exact totalDegree_C r

-- TODO: introduce MvPolynomial.IsPrimitive for the RHS condition
theorem irreducible_iff_of_totalDegree_eq_one (h : totalDegree f = 1) :
    Irreducible f ↔ ∀ r : R, C r ∣ f → IsUnit r where
  mp irr r := by
    have : f ≠ 0 := by rintro rfl; simp at h
    rintro ⟨g, rfl⟩
    rw [totalDegree_mul_of_mul_ne_zero this, totalDegree_C, zero_add] at h
    exact isUnit_C_iff.mp <| (irr.2 rfl).resolve_right
      (fun hg ↦ one_ne_zero (h.symm.trans (totalDegree_eq_zero_of_isUnit hg)))
  mpr prim := by
    refine ⟨fun hf ↦ one_ne_zero (h.symm.trans (totalDegree_eq_zero_of_isUnit hf)), fun p q eq ↦ ?_⟩
    have hf : p * q ≠ 0 := eq ▸ fun hf ↦ one_ne_zero (h.symm.trans <| hf ▸ totalDegree_zero)
    have eq' := congr(totalDegree $eq)
    simp_rw [totalDegree_mul_of_mul_ne_zero hf, h, eq_comm,
      Nat.add_eq_one_iff, totalDegree_eq_zero_iff_eq_C] at eq'
    obtain ⟨eq', -⟩ | ⟨-, eq'⟩ := eq' <;> rw [eq'] at eq ⊢
    · exact .inl ((prim _ (eq ▸ dvd_mul_right _ q)).map C)
    · exact .inr ((prim _ (eq ▸ dvd_mul_left _ p)).map C)

theorem irreducible_X [Nontrivial R] (i : σ) : Irreducible (X (R := R) i) :=
  (irreducible_iff_of_totalDegree_eq_one (totalDegree_X i)).mpr fun _r dvd ↦
    isUnit_of_dvd_one <| ((C_dvd_iff_dvd_coeff ..).mp dvd _).trans (coeff_X i).dvd

end MvPolynomial

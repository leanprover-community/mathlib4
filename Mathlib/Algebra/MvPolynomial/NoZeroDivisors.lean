/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Multivariate polynomials over `NoZeroDivisors`

This file proves results about multivariate polynomials
that hold when the coefficient semiring has no zero divisors.

## TODOs

* Add a `totalDegree_mul_eq` theorem, which states that the total degree of a product of two
nonzero multivariate polynomials is the sum of their total degrees. (See also
`MvPolynomial.totalDegree_mul_of_isDomain`, which proves this
under the assumption that the coefficient semiring has cancellative multiplication.)

-/

@[expose] public section

variable {R : Type*}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R]

variable {p q : MvPolynomial σ R}

section DegreeOf

lemma degreeOf_mul_eq [NoZeroDivisors R] (hp : p ≠ 0) (hq : q ≠ 0) :
    degreeOf n (p * q) = degreeOf n p + degreeOf n q := by
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul] <;> simpa [-renameEquiv_apply, EmbeddingLike.map_eq_zero_iff]

lemma degreeOf_prod_eq [NoZeroDivisors R] {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R)
    (h : ∀ i ∈ s, f i ≠ 0) :
    degreeOf n (∏ i ∈ s, f i) = ∑ i ∈ s, degreeOf n (f i) := by
  by_cases nontrivial : Nontrivial (MvPolynomial σ R)
  · classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s a_not_mem ih =>
      simp only [Finset.mem_insert, ne_eq, forall_eq_or_imp] at h
      obtain ⟨ha, hs⟩ := h
      specialize ih hs
      simp only [a_not_mem, not_false_eq_true, Finset.prod_insert, Finset.sum_insert]
      rw [degreeOf_mul_eq ha (by rw [Finset.prod_ne_zero_iff]; exact hs), ih]
  · push_neg at nontrivial
    have (x : MvPolynomial σ R) : x = 0 := Subsingleton.eq_zero x
    simp only [degreeOf_zero, Finset.sum_const_zero, this]

theorem degreeOf_pow_eq [NoZeroDivisors R] (i : σ) (p : MvPolynomial σ R) (n : ℕ) (hp : p ≠ 0) :
    degreeOf i (p ^ n) = n * degreeOf i p := by
  rw [Finset.pow_eq_prod_const, degreeOf_prod_eq (Finset.range n) (fun _ ↦ p) (fun _ _ ↦ hp)]
  simp

end DegreeOf

section Degrees

-- TODO: Can `NoZeroDivisors` be weakened to `IsCancelMulZero` here?
lemma degrees_mul_eq [NoZeroDivisors R] (hp : p ≠ 0) (hq : q ≠ 0) :
    degrees (p * q) = degrees p + degrees q := by
  classical
  apply Multiset.ext'
  intro s
  simp_rw [Multiset.count_add, ← degreeOf_def, degreeOf_mul_eq hp hq]

end Degrees

open nonZeroDivisors

theorem degreeOf_C_mul (j : σ) (c : R) (hc : c ∈ R⁰) :
    MvPolynomial.degreeOf j (MvPolynomial.C c * p) = MvPolynomial.degreeOf j p := by
  by_cases hp : p = 0
  · simp [hp]
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul]
  simp only [← renameEquiv_apply]
  rw [Polynomial.natDegree_mul']
  · simp
  · have hp' :
        ((optionEquivLeft R { b // ¬b = j })
          ((rename (Equiv.optionSubtypeNe j).symm) p)).leadingCoeff ≠ 0 := by
      simp only [ne_eq, Polynomial.leadingCoeff_ne_zero, EmbeddingLike.map_eq_zero_iff]
      intro h
      exact
        hp
          (rename_injective (⇑(Equiv.optionSubtypeNe j).symm)
            (Equiv.injective (Equiv.optionSubtypeNe j).symm) h)
    simp_rw [ne_eq, renameEquiv_apply, algHom_C, algebraMap_eq, optionEquivLeft_C,
      Polynomial.leadingCoeff_C]
    contrapose! hp'
    ext m
    have h' := congr_arg (coeff m) hp'
    simp only [coeff_C_mul] at h'
    exact hc.1 _ h'

end MvPolynomial

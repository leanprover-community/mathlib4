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

Many results about polynomials hold when the coefficient ring has no zero divisors.

This file does not define any new operations, but proves some of these stronger results.

## TODOs

* Add a `totalDegree_mul_eq` theorem, which states that the total degree of a product of two
nonzero multivariate polynomials is the sum of their total degrees. (See also
`MvPolynomial.totalDegree_mul_of_isDomain`, which proves this
under the assumption that the coefficient ring has cancellative multiplication.)

-/

@[expose] public section

variable {R : Type*}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [NoZeroDivisors R]

variable {p q : MvPolynomial σ R}

section DegreeOf

lemma degreeOf_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) :
    degreeOf n (p * q) = degreeOf n p + degreeOf n q := by
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul]
  rw [Polynomial.natDegree_mul] <;> simpa [← renameEquiv_apply, EmbeddingLike.map_eq_zero_iff]

lemma degreeOf_prod_eq {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R)
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

theorem degreeOf_C_mul (j : σ) (c : R) (hc : c ≠ 0) :
    MvPolynomial.degreeOf j (MvPolynomial.C c * p) = MvPolynomial.degreeOf j p := by
  by_cases hp : p = 0
  · simp [hp]
  rw [degreeOf_mul_eq (C_eq_zero.not.mpr hc) hp, degreeOf_C, zero_add]

theorem degreeOf_pow_eq (i : σ) (p : MvPolynomial σ R) (n : ℕ) (hp : p ≠ 0) :
    degreeOf i (p ^ n) = n * degreeOf i p := by
  rw [Finset.pow_eq_prod_const, degreeOf_prod_eq (Finset.range n) (fun _ ↦ p) (fun _ _ ↦ hp)]
  simp

end DegreeOf

section Degrees

lemma degrees_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) :
    degrees (p * q) = degrees p + degrees q := by
  classical
  apply Multiset.ext'
  intro s
  simp_rw [Multiset.count_add, ← degreeOf_def, degreeOf_mul_eq hp hq]

end Degrees

end MvPolynomial

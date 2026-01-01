/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Monic

/-!

# Free monic polynomial

We define the free monic polynomial of degree `n`. Given a family of variables `e : Fin n → σ`,
this is `Xⁿ + aₑ₍ₙ₋₁₎ Xⁿ⁻¹ + ⋯ + aₑ₍₁₎ X + aₑ₍₀₎` in `(MvPolynomial σ R)[X]`.

-/

@[expose] public noncomputable section

variable (R : Type*) {S σ : Type*} [CommRing R] [CommRing S]
variable {n : ℕ} (k : ℕ) (e : Fin n → σ)

namespace Polynomial

/-- The free monic polynomial of degree `n`. Given a family of variables `e : Fin n → σ`,
this is `Xⁿ + aₑ₍ₙ₋₁₎ Xⁿ⁻¹ + ⋯ + aₑ₍₁₎ X + aₑ₍₀₎` in `(MvPolynomial σ R)[X]`. -/
def freeMonic : (MvPolynomial σ R)[X] :=
  .X ^ n + ∑ i : Fin n, .C (.X (e i)) * .X ^ (i : ℕ)

lemma coeff_freeMonic :
    (freeMonic R e).coeff k =
      if h : k < n then .X (e ⟨k, h⟩) else if k = n then 1 else 0 := by
  simp only [freeMonic, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases h : k < n
  · simp +contextual [Finset.sum_eq_single (ι := Fin n) (a := ⟨k, h⟩),
      Fin.ext_iff, @eq_comm _ k, h, h.ne']
  · rw [Finset.sum_eq_zero fun x _ ↦ if_neg (by cases x; lia), add_zero, dif_neg h]

lemma degree_freeMonic [Nontrivial R] : (freeMonic R e).degree = n :=
  Polynomial.degree_eq_of_le_of_coeff_ne_zero ((Polynomial.degree_le_iff_coeff_zero _ _).mpr
    (by simp +contextual [coeff_freeMonic, LT.lt.not_gt, LT.lt.ne']))
    (by simp [coeff_freeMonic])

lemma natDegree_freeMonic [Nontrivial R] : (freeMonic R e).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_freeMonic R e)

lemma monic_freeMonic : (freeMonic R e).Monic := by
  nontriviality R
  simp [Polynomial.Monic, ← Polynomial.coeff_natDegree, natDegree_freeMonic, coeff_freeMonic]

variable {R} in
lemma map_map_freeMonic (f : R →+* S) :
    (freeMonic R e).map (MvPolynomial.map f) = freeMonic S e := by
  simp [freeMonic, Polynomial.map_sum]

open Polynomial (MonicDegreeEq)

variable (n) in
/-- The free monic polynomial of degree `n`, as a `MonicDegreeEq` in `R[X₁,...,Xₙ][X]`. -/
@[simps]
def MonicDegreeEq.freeMonic : MonicDegreeEq (MvPolynomial (Fin n) R) n :=
  ⟨.freeMonic R id, by simp +contextual [coeff_freeMonic, not_lt_of_gt, LT.lt.ne']⟩

end Polynomial

/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.ConstantTermRelations
import Archive.GaussianMomentConjecture.MomentTransport
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.Defs

/-!
# Integral models of the Wick-moment and face constant-term relations

All multinomial and factorial coefficients in the GMC(2) proof are integers.
These `ℤ`-polynomial models allow the entire complex null point and nonzero
face seed to be specialized directly through a finite-type `ℤ`-algebra.  This
removes denominator bookkeeping and supports a characteristic-`p` maximal
quotient without first choosing a number field prime.
-/

open MvPolynomial Finset

namespace GMC2.IntegralRelations

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

/-- Integral universal Wick-moment relation. -/
noncomputable def momentRelationInt
    (exponent : ι → Fin 2 →₀ ℕ) (m : ℕ) : MvPolynomial ι ℤ :=
  ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
    if (GMC2.MomentRelations.channelExponent exponent r) 0 =
        (GMC2.MomentRelations.channelExponent exponent r) 1 then
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm r)
        ((Nat.multinomial Finset.univ r : ℤ) *
          Nat.factorial ((GMC2.MomentRelations.channelExponent exponent r) 0))
    else 0

/-- Integral universal face constant-term relation. -/
noncomputable def constantTermRelationInt
    (q : ι → ℤ) (m : ℕ) : MvPolynomial ι ℤ :=
  ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
    if GMC2.ConstantTermRelations.totalCharge q r = 0 then
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm r)
        (Nat.multinomial Finset.univ r : ℤ)
    else 0

theorem aeval_momentRelationInt
    [CommRing R] [Algebra ℤ R]
    (exponent : ι → Fin 2 →₀ ℕ) (c : ι → R) (m : ℕ) :
    MvPolynomial.aeval c (momentRelationInt exponent m) =
      ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
        if (GMC2.MomentRelations.channelExponent exponent r) 0 =
            (GMC2.MomentRelations.channelExponent exponent r) 1 then
          (Nat.multinomial Finset.univ r : R) *
            (∏ i, c i ^ r i) *
              (Nat.factorial
                ((GMC2.MomentRelations.channelExponent exponent r) 0) : R)
        else 0 := by
  classical
  simp only [momentRelationInt, map_sum, MvPolynomial.aeval_def]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs with hbalanced
  · simp only [eval₂_monomial, map_mul]
    rw [map_natCast, map_natCast]
    rw [Finsupp.prod_fintype]
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
      ring
    · intro i
      simp
  · simp

theorem aeval_constantTermRelationInt
    [CommRing R] [Algebra ℤ R]
    (q : ι → ℤ) (c : ι → R) (m : ℕ) :
    MvPolynomial.aeval c (constantTermRelationInt q m) =
      ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
        if GMC2.ConstantTermRelations.totalCharge q r = 0 then
          (Nat.multinomial Finset.univ r : R) * ∏ i, c i ^ r i
        else 0 := by
  classical
  simp only [constantTermRelationInt, map_sum, MvPolynomial.aeval_def]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs with hbalanced
  · simp only [eval₂_monomial]
    rw [map_natCast]
    rw [Finsupp.prod_fintype]
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
    · intro i
      simp
  · simp

/-- Over `ℂ`, the integral and rational models of the same face
constant-term polynomial have identical values.  This is the cast bridge
from the rational DvdK interface to denominator-free specialization. -/
theorem aeval_constantTermRelationInt_eq_rat
    (q : ι → ℤ) (c : ι → ℂ) (m : ℕ) :
    MvPolynomial.aeval c (constantTermRelationInt q m) =
      MvPolynomial.aeval c
        (GMC2.ConstantTermRelations.constantTermRelation q m) := by
  rw [aeval_constantTermRelationInt,
    GMC2.ConstantTermRelations.aeval_constantTermRelation]

/-- The complex Gaussian moment is also the evaluation of the integral
universal moment polynomial. -/
theorem E_indexedPolynomial_pow_eq_aeval_momentRelationInt
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → ℂ) (m : ℕ) :
    GMC2.E ((GMC2.MomentTransport.indexedPolynomial exponent coefficient) ^ m) =
      MvPolynomial.aeval coefficient (momentRelationInt exponent m) := by
  rw [aeval_momentRelationInt]
  unfold GMC2.MomentTransport.indexedPolynomial
  rw [Finset.sum_pow_eq_sum_piAntidiag, GMC2.E_finset_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [GMC2.MomentTransport.prod_indexed_monomial_pow]
  change GMC2.E
      ((Nat.multinomial Finset.univ r : MvPolynomial (Fin 2) ℂ) *
        MvPolynomial.monomial
          (GMC2.MomentRelations.channelExponent exponent r)
          (∏ i, coefficient i ^ r i)) = _
  rw [GMC2.natCast_mul_monomial, GMC2.E_monomial]
  unfold GMC2.wt
  split_ifs <;> simp

end GMC2.IntegralRelations


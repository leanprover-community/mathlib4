/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.MomentRelations
import Archive.GaussianMomentConjecture.WickChannels
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Defs

/-!
# Transport between Gaussian moments and universal rational relations

For a finite indexed list of bidegrees and complex coefficients, the Gaussian
moment of the corresponding polynomial is exactly the evaluation of the
universal rational polynomial from `MomentRelations`.  This removes the
coefficient-ring mismatch between the analytic `ℂ` definition of `GMC2.E` and
the algebraic descent over `ℚ`.
-/

open MvPolynomial Finset

namespace GMC2.MomentTransport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Polynomial represented by a finite indexed monomial list. -/
noncomputable def indexedPolynomial
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  ∑ i, MvPolynomial.monomial (exponent i) (coefficient i)

omit [Fintype ι] [DecidableEq ι] in
/-- Product arithmetic for one indexed multinomial channel. -/
theorem prod_indexed_monomial_pow
    (S : Finset ι) (exponent : ι → Fin 2 →₀ ℕ)
    (coefficient : ι → ℂ) (r : ι → ℕ) :
    (∏ i ∈ S,
      (MvPolynomial.monomial (exponent i) (coefficient i) :
        MvPolynomial (Fin 2) ℂ) ^ r i) =
      MvPolynomial.monomial
        (∑ i ∈ S, r i • exponent i)
        (∏ i ∈ S, coefficient i ^ r i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi, ih]
      simp [hi, MvPolynomial.monomial_pow, MvPolynomial.monomial_mul]

/-- The exact bridge from complex Gaussian moments to the evaluation of a
universal rational moment relation.  No injectivity or nonzero-coefficient
assumption is needed: the multinomial expansion is indexed before equal
monomials are collected. -/
theorem E_indexedPolynomial_pow_eq_aeval_momentRelation
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → ℂ) (m : ℕ) :
    GMC2.E ((indexedPolynomial exponent coefficient) ^ m) =
      MvPolynomial.aeval coefficient
        (GMC2.MomentRelations.momentRelation exponent m) := by
  classical
  rw [GMC2.MomentRelations.aeval_momentRelation]
  unfold indexedPolynomial
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  rw [GMC2.E_finset_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [prod_indexed_monomial_pow]
  change GMC2.E
      ((Nat.multinomial Finset.univ r : MvPolynomial (Fin 2) ℂ) *
        MvPolynomial.monomial
          (GMC2.MomentRelations.channelExponent exponent r)
          (∏ i, coefficient i ^ r i)) = _
  rw [GMC2.natCast_mul_monomial, GMC2.E_monomial]
  unfold GMC2.wt
  split_ifs <;> simp

end GMC2.MomentTransport

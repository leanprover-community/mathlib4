/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.NullconeDescent
import Mathlib

set_option linter.minImports true

/-!
# Exact-support specialization of the GMC(2) nullcone descent

The generic indexed descent becomes a theorem for every concrete
`MvPolynomial` by indexing variables with its exact support.  Support
coefficients are automatically nonzero, so no auxiliary torus hypothesis is
needed beyond the definition of support.
-/

open MvPolynomial Finset

namespace GMC2SupportDescent

/-- Re-expanding a polynomial over its support as an indexed monomial sum
recovers the polynomial exactly. -/
theorem indexedPolynomial_support_eq (P : MvPolynomial (Fin 2) ℂ) :
    GMC2MomentTransport.indexedPolynomial
      (fun s : ↥P.support => (s : Fin 2 →₀ ℕ))
      (fun s : ↥P.support => P.coeff s) = P := by
  classical
  unfold GMC2MomentTransport.indexedPolynomial
  rw [Finset.univ_eq_attach]
  calc
    (∑ i ∈ P.support.attach,
        MvPolynomial.monomial (i : Fin 2 →₀ ℕ) (P.coeff i)) =
        ∑ s ∈ P.support, MvPolynomial.monomial s (P.coeff s) := by
      simpa using
        (Finset.sum_attach P.support
          (fun s ↦ MvPolynomial.monomial s (P.coeff s)))
    _ = P := MvPolynomial.support_sum_monomial_coeff P

/-- Every concrete complex moment-null polynomial descends, on its exact
support, to a nonzero coefficient point over a number field satisfying all of
the same universal rational Wick-moment relations. -/
theorem exists_numberField_moment_null_point_of_polynomial
    (P : MvPolynomial (Fin 2) ℂ)
    (hnull : ∀ m : ℕ, 1 ≤ m → GMC2.E (P ^ m) = 0) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K),
      Module.Finite ℚ K ∧
        ∃ coefficientK : ↥P.support → K,
          (∀ i, coefficientK i ≠ 0) ∧
            ∀ m : ℕ,
              MvPolynomial.aeval coefficientK
                (GMC2MomentRelations.momentRelation
                  (fun s : ↥P.support => (s : Fin 2 →₀ ℕ)) (m + 1)) = 0 := by
  apply GMC2NullconeDescent.exists_numberField_moment_null_point
    (fun s : ↥P.support => (s : Fin 2 →₀ ℕ))
    (fun s : ↥P.support => P.coeff s)
  · intro s
    simpa only [MvPolynomial.mem_support_iff] using s.property
  · intro m hm
    rw [indexedPolynomial_support_eq]
    exact hnull m hm

end GMC2SupportDescent


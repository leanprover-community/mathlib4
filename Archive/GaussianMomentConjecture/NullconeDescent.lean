/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.MomentTransport
import Archive.GaussianMomentConjecture.TorusDescent
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# End-to-end algebraic descent of the indexed GMC(2) nullcone

This module composes the universal rational moment relations, their exact
complex Gaussian interpretation, and the torus-to-number-field theorem.  It
formalizes Section 2 of the lowest-balanced-face theorem without a hidden coordinate-ring axiom.
-/

open MvPolynomial

namespace GMC2.NullconeDescent

/-- A complex indexed polynomial with nonzero coefficients and all positive
Gaussian moments zero yields a torus point over a number field at which every
universal rational moment relation vanishes. -/
theorem exists_numberField_moment_null_point
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → ℂ)
    (hcoefficient : ∀ i, coefficient i ≠ 0)
    (hnull : ∀ m : ℕ, 1 ≤ m →
      GMC2.E
        ((GMC2.MomentTransport.indexedPolynomial exponent coefficient) ^ m) = 0) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K),
      Module.Finite ℚ K ∧
        ∃ coefficientK : ι → K,
          (∀ i, coefficientK i ≠ 0) ∧
            ∀ m : ℕ,
              MvPolynomial.aeval coefficientK
                (GMC2.MomentRelations.momentRelation exponent (m + 1)) = 0 := by
  apply GMC2.TorusDescent.exists_numberField_torus_point_of_complex_relations
    (fun m => GMC2.MomentRelations.momentRelation exponent (m + 1))
    coefficient hcoefficient
  intro m
  calc
    MvPolynomial.aeval coefficient
        (GMC2.MomentRelations.momentRelation exponent (m + 1)) =
      GMC2.E
        ((GMC2.MomentTransport.indexedPolynomial exponent coefficient) ^ (m + 1)) :=
      (GMC2.MomentTransport.E_indexedPolynomial_pow_eq_aeval_momentRelation
        exponent coefficient (m + 1)).symm
    _ = 0 := hnull (m + 1) (by omega)

end GMC2.NullconeDescent

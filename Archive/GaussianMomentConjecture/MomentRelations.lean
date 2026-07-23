/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib

set_option linter.minImports true

/-!
# Universal rational Wick-moment relations

For a fixed finite list of exact bidegrees, every Gaussian moment is a
polynomial with rational (indeed natural) coefficients in the corresponding
monomial coefficients.  This module defines that polynomial independently of
the coefficient ring and proves its evaluation formula.  It is the transport
object used by the algebraic-torus descent.
-/

open MvPolynomial Finset

namespace GMC2MomentRelations

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact accumulated bidegree of an indexed multiplicity channel. -/
noncomputable def channelExponent (exponent : ι → Fin 2 →₀ ℕ)
    (r : ι → ℕ) : Fin 2 →₀ ℕ :=
  ∑ i, r i • exponent i

/-- The universal rational polynomial whose value is the `m`-th Wick moment
of the indexed monomial sum. -/
noncomputable def momentRelation (exponent : ι → Fin 2 →₀ ℕ) (m : ℕ) :
    MvPolynomial ι ℚ :=
  ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
    if (channelExponent exponent r) 0 = (channelExponent exponent r) 1 then
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm r)
        ((Nat.multinomial Finset.univ r : ℚ) *
          Nat.factorial ((channelExponent exponent r) 0))
    else 0

/-- Evaluating the universal relation gives the exact balanced-channel sum in
any commutative `ℚ`-algebra. -/
theorem aeval_momentRelation
    [CommRing R] [Algebra ℚ R]
    (exponent : ι → Fin 2 →₀ ℕ) (c : ι → R) (m : ℕ) :
    MvPolynomial.aeval c (momentRelation exponent m) =
      ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
        if (channelExponent exponent r) 0 = (channelExponent exponent r) 1 then
          (Nat.multinomial Finset.univ r : R) *
            (∏ i, c i ^ r i) *
              (Nat.factorial ((channelExponent exponent r) 0) : R)
        else 0 := by
  classical
  simp only [momentRelation, map_sum, MvPolynomial.aeval_def]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs with hbalanced
  · simp only [eval₂_monomial, map_mul, map_natCast]
    rw [Finsupp.prod_fintype]
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
      ring
    · intro i
      simp
  · simp

end GMC2MomentRelations


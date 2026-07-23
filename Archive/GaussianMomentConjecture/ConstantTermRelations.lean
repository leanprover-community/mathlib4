/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Finite.Polynomial

set_option linter.minImports true

/-!
# Universal rational constant-term relations on a charge face

For a finite Laurent support with integral charges, the constant term of its
`m`-th power is a rational polynomial in the support coefficients.  This is
the algebraic face seed supplied nonvanishing by the one-variable
Duistermaat--van der Kallen theorem.
-/

open MvPolynomial Finset

namespace GMC2.ConstantTermRelations

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

/-- Total Laurent charge of an indexed multiplicity channel. -/
def totalCharge (q : ι → ℤ) (r : ι → ℕ) : ℤ :=
  ∑ i, (r i : ℤ) * q i

/-- Universal coefficient polynomial for the constant term of the `m`-th
power of an indexed Laurent polynomial. -/
noncomputable def constantTermRelation (q : ι → ℤ) (m : ℕ) :
    MvPolynomial ι ℚ :=
  ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
    if totalCharge q r = 0 then
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm r)
        (Nat.multinomial Finset.univ r : ℚ)
    else 0

/-- Evaluation of the universal constant-term relation in any commutative
`ℚ`-algebra. -/
theorem aeval_constantTermRelation
    [CommRing R] [Algebra ℚ R]
    (q : ι → ℤ) (c : ι → R) (m : ℕ) :
    MvPolynomial.aeval c (constantTermRelation q m) =
      ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
        if totalCharge q r = 0 then
          (Nat.multinomial Finset.univ r : R) * ∏ i, c i ^ r i
        else 0 := by
  classical
  simp only [constantTermRelation, map_sum, MvPolynomial.aeval_def]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs with hbalanced
  · simp only [eval₂_monomial, map_natCast]
    rw [Finsupp.prod_fintype]
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
    · intro i
      simp
  · simp

end GMC2.ConstantTermRelations


/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/

import Mathlib.Algebra.Polynomial.Resultant.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous


/-!
# Universal Resultant

The resultant can be seen as a polynomial in `ℤ[a₀, ..., aₘ, b₀, ..., bₙ]` where `aᵢ` and `bⱼ` are
the "universal coefficients" of the polynomial `p(x) = a₀ + a₁ x + ... + aₘ xᵐ` and
`q(x) = b₀ + b₁ x + ... + bₙ xⁿ`. This is implemented as either
`MvPolynomial (Fin (m+1) ⊕ Fin (n+1)) ℤ`, or `MvPolynomial (ℕ ⊕ ℕ) ℤ` to unify
the different polynomials.

The universal construction allows one to reason about the resultant more abstractly, and to prove
certain identities involving the resultant.

-/


noncomputable section

namespace Polynomial

section universal

variable (m n : ℕ)

/-- The universal polynomial `aₙ xⁿ + aₙ₋₁ xⁿ⁻¹ + ... + a₁ x + a₀`. -/
def universal : (MvPolynomial (Fin (n+1)) ℤ)[X] :=
  ∑ i : Fin (n+1), .C (.X i) * .X ^ i.1

/-- The universal polynomial `aₙ xⁿ + aₙ₋₁ xⁿ⁻¹ + ... + a₁ x + a₀`. -/
def universal' : (MvPolynomial ℕ ℤ)[X] :=
  .map (MvPolynomial.rename Fin.val).toRingHom (.universal n)

/-- The universal monic polynomial `xⁿ + aₙ₋₁ xⁿ⁻¹ + ... + a₁ x + a₀`. -/
def universalMonic : (MvPolynomial (Fin n) ℤ)[X] :=
  (universal n).map (MvPolynomial.aeval <| Fin.lastCases 1 MvPolynomial.X).toRingHom

/-- The universal monic polynomial `xⁿ + aₙ₋₁ xⁿ⁻¹ + ... + a₁ x + a₀`. -/
def universalMonic' : (MvPolynomial ℕ ℤ)[X] :=
  .map (MvPolynomial.rename Fin.val).toRingHom (.universalMonic n)

def universalPair : (MvPolynomial (Fin (m+1) ⊕ Fin (n+1)) ℤ)[X] ×
    (MvPolynomial (Fin (m+1) ⊕ Fin (n+1)) ℤ)[X] :=
  (.map (MvPolynomial.rename Sum.inl).toRingHom (.universal m),
   .map (MvPolynomial.rename Sum.inr).toRingHom (.universal n))

def universalResultant : MvPolynomial (Fin (m+1) ⊕ Fin (n+1)) ℤ :=
  resultant (universalPair m n).1 (universalPair m n).2

-- I don't know what simp lemmas I need yet.

end universal


section IsHomogeneous

variable (m n : ℕ)

theorem resultant_IsHomogeneous :
    (universalResultant m n).IsHomogeneous (m + n) := by
  sorry

theorem resultant_IsWeightedHomogeneous :
    (universalResultant m n).IsWeightedHomogeneous
      (Sum.elim (fun i ↦ m - i : Fin (m+1) → ℤ) (fun i ↦ n - i : Fin (n+1) → ℤ))
      (m * n) := by
  sorry

end IsHomogeneous

end Polynomial

#check bind
#lint

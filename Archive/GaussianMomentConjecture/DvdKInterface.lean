/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.ConstantTermRelations
import Archive.GaussianMomentConjecture.LowestFaceExistence
import Mathlib

set_option linter.minImports true

/-!
# Narrow interface to the one-variable Duistermaat--van der Kallen theorem

The analytic theorem is external to Mathlib.  Rather than hiding it as an
axiom, this module records the exact proposition consumed by the GMC(2)
formalization.  All downstream theorems take a proof of `DvdK1` explicitly.
-/

namespace GMC2DvdKInterface

/-- One-variable DvdK in the finite exact-support form needed here: an
injectively indexed Laurent polynomial with nonzero coefficients and charge
support meeting/straddling zero has a nonzero constant term in some positive
power. -/
def DvdK1 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (q : ι → ℤ) (c : ι → ℂ),
    Function.Injective q →
    (∀ i, c i ≠ 0) →
    GMC2LowestFaceExistence.ChargesStraddleZero Finset.univ
      (fun i => (q i : ℚ)) →
    ∃ m : ℕ, 1 ≤ m ∧
      MvPolynomial.aeval c
        (GMC2ConstantTermRelations.constantTermRelation q m) ≠ 0

/-- Named elimination rule for the external input. -/
theorem exists_nonzero_face_seed
    (hDvdK : DvdK1)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (q : ι → ℤ) (c : ι → ℂ)
    (hq : Function.Injective q)
    (hc : ∀ i, c i ≠ 0)
    (hstraddle :
      GMC2LowestFaceExistence.ChargesStraddleZero Finset.univ
        (fun i => (q i : ℚ))) :
    ∃ m : ℕ, 1 ≤ m ∧
      MvPolynomial.aeval c
        (GMC2ConstantTermRelations.constantTermRelation q m) ≠ 0 :=
  hDvdK ι q c hq hc hstraddle

end GMC2DvdKInterface


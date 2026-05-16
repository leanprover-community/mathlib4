/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.NumberTheory.Height.MvPolynomial

/-!
# The naïve height and the approximate parallelogram law

This file defines the *naïve height* on an elliptic curve (over a field `K` with a theory of
heights, i.e., satisfying `[Height.AdmissibleAbsValues K]`).

The final goal of this file is to prove the *approximate parallelogram law* for (affine) points
on elliptic curves,
```
  |h(P+Q) + h(P-Q) - 2*(h(P) + h(Q))| ≤ C
```
whre `h` is the naïve height, `P` and `Q` are affine points on a `WeierstrassCurve` and `C`
is some real constant depending only on the Weierstrass model.

### TODO

* Define the naïve height
* Add the further ingredients needed for the approximate parallelogram law
* Add the statement and proof of the approximate parallelogram law
-/

public section

namespace WeierstrassCurve

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {a b : K}
  (hab : 32 * a ^ 3 + 216 * b ^ 2 ≠ 0)

open MvPolynomial

include hab in
/-- If `a b : K` and  `D := 32*a^3 + 216*b^2` is nonzero, then the map `F : ℙ² → ℙ²` given by
`(s : t : u) ↦ (s^2 - 2*a*s*u - 4*b*t*u + a²*u² : 2*s*t + 2*a*t*u + 4*b*u² : t² - 4*s*u)`
(called `addSubMap` here) is a morphism.

This implies that `|logHeight (F x) - 2 * logHeight x| ≤ C` for a constant `C`,
where `x = ![s, t, u]` and `F` acts on the coordinate vector. -/
theorem abs_logHeight_addSubMap_sub_two_mul_logHeight_le :
    ∃ C, ∀ x : Fin 3 → K,
      |logHeight (fun i ↦ (addSubMap a b i).eval x) - 2 * logHeight x| ≤ C := by
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, ∀ x : Fin 3 → K,
      logHeight (fun i ↦ (addSubMap a b i).eval x) ≤ C₁ + 2 * logHeight x :=
    logHeight_eval_le' <| isHomogeneous_addSubMap a b
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, ∀ x : Fin 3 → K,
      logHeight (fun i ↦ (addSubMap a b i).eval x) ≥ C₂ + 2 * logHeight x := by
    have H (ij : Fin 3 × Fin 3) :
        (C ((32 * a ^ 3 + 216 * b ^ 2)⁻¹) * addSubMapCoeff a b ij).IsHomogeneous 2 :=
      IsHomogeneous.C_mul (isHomogenous_addSubMapCoeff a b ij) _
    obtain ⟨C₂, h⟩ := logHeight_eval_ge' H
    exact ⟨C₂, fun x ↦ h _ <| addSubMapCoeff_condition hab x⟩
  refine ⟨max C₁ (-C₂), fun x ↦ abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩ <;> grind

end WeierstrassCurve

end

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
where `h` is the naïve height, `P` and `Q` are affine points on a `WeierstrassCurve` and `C`
is some real constant depending only on the Weierstrass model.

### TODO

* Define the naïve height
* Add the further ingredients needed for the approximate parallelogram law
* Add the statement and proof of the approximate parallelogram law
-/

public section

namespace WeierstrassCurve

open Height MvPolynomial

variable {K : Type*} [Field K] [AdmissibleAbsValues K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- If `W` is a Weierstrass curve over `K`, then the map `F : ℙ² → ℙ²` given by `addSubMap W`
is a morphism.

This implies that `|logHeight (F x) - 2 * logHeight x| ≤ C` for a constant `C`,
where `x = ![s, t, u]` and `F` acts on the coordinate vector. -/
theorem abs_logHeight_addSubMap_sub_two_mul_logHeight_le :
    ∃ C, ∀ x : Fin 3 → K,
      |logHeight (fun i ↦ (addSubMap W i).eval x) - 2 * logHeight x| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := logHeight_eval_le' <| isHomogeneous_addSubMap W
  obtain ⟨C₂, h⟩ := logHeight_eval_ge' (N := 2)
    fun ij ↦ (isHomogeneous_addSubMapCoeff W ij).C_mul ↑W.Δ'⁻¹
  have hC₂ := fun x ↦ h _ <| addSubMapCoeff_condition W x
  refine ⟨max C₁ (-C₂), fun x ↦ abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩ <;> grind

end WeierstrassCurve

end

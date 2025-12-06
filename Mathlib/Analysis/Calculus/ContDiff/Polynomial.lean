/-
Copyright (c) 2025 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Higher smoothness of polynomials

We prove that polynomials are `C^∞`.
-/

@[expose] public section

namespace Polynomial

/-- Polynomials are smooth -/
lemma contDiff_aeval
    {R 𝕜 : Type*} [CommSemiring R] [NontriviallyNormedField 𝕜] [Algebra R 𝕜]
    (f : Polynomial R) : ContDiff 𝕜 ⊤ (fun x : 𝕜 ↦ f.aeval x) := by
  induction f using Polynomial.induction_on' with
  | add f g fc gc =>
    simp only [map_add]
    exact fc.add gc
  | monomial n a =>
    simp only [Polynomial.aeval_monomial]
    exact contDiff_const.mul (contDiff_id.pow _)

end Polynomial

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Gauss AI (Math.Inc).
-/

module

public import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
# MDifferentiability of the weight 2 Eisenstein series

We show that the weight 2 Eisenstein series `E2` is MDifferentiable (i.e. holomorphic as a
function `ℍ → ℂ`). The proof uses the relation between `E2` and the logarithmic derivative of
the Dedekind eta function.
-/

@[expose] public section

open UpperHalfPlane hiding I
open Real Complex EisensteinSeries ModularForm Manifold

local notation "η" => ModularForm.eta

--This proof was provided by Gauss to the sphere packing project.
/-- The weight 2 Eisenstein series `E2` is MDifferentiable -/
lemma E2_mdifferentiable : MDiff E2 := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hη : DifferentiableOn ℂ η _ :=
    fun z hz ↦ (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt
  have hlog : DifferentiableOn ℂ (logDeriv η) _ :=
    (hη.deriv isOpen_upperHalfPlaneSet).div hη fun _ hz ↦ by simpa using eta_ne_zero hz
  exact (hlog.const_mul (π * I / 12)⁻¹).congr fun z hz => by
    simp [ofComplex_apply_of_im_pos hz,
      show logDeriv η z = (π * I / 12) * E2 ⟨z, hz⟩ by simpa using logDeriv_eta_eq_E2 ⟨z, hz⟩]
    field_simp

end

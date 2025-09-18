/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Semisimple

/-!
# Semisimple operators on inner product spaces

This file is a place to gather results related to semisimplicity of linear operators on inner
product spaces.

-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap.IsSymmetric

variable {T : Module.End 𝕜 E} {p : Submodule 𝕜 E} (hT : T.IsSymmetric)

include hT

/-- The orthogonal complement of an invariant submodule is invariant. -/
lemma orthogonalComplement_mem_invtSubmodule (hp : p ∈ T.invtSubmodule) :
    pᗮ ∈ T.invtSubmodule :=
  fun x hx y hy ↦ hT y x ▸ hx (T y) (hp hy)

/-- Symmetric operators are semisimple on finite-dimensional subspaces. -/
theorem isFinitelySemisimple :
    T.IsFinitelySemisimple := by
  refine Module.End.isFinitelySemisimple_iff.mpr fun p hp₁ hp₂ q hq₁ hq₂ ↦
    ⟨qᗮ ⊓ p, inf_le_right, Module.End.invtSubmodule.inf_mem ?_ hp₁, ?_, ?_⟩
  · exact orthogonalComplement_mem_invtSubmodule hT hq₁
  · simp [disjoint_iff, ← inf_assoc, Submodule.inf_orthogonal_eq_bot q]
  · suffices q ⊔ qᗮ = ⊤ by rw [← sup_inf_assoc_of_le _ hq₂, this, top_inf_eq p]
    replace hp₂ : Module.Finite 𝕜 q := Submodule.finiteDimensional_of_le hq₂
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

end LinearMap.IsSymmetric

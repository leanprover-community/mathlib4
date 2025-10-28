/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Strict
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# (Pre)images of strict convex sets under continuous linear equivalences

In this file we prove that the (pre)image of a strict convex set
under a continuous linear equivalence is a strict convex set.
-/

variable {𝕜 E F : Type*}
  [Field 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

namespace ContinuousLinearEquiv

@[simp]
lemma strictConvex_preimage {s : Set F} (e : E ≃L[𝕜] F) :
    StrictConvex 𝕜 (e ⁻¹' s) ↔ StrictConvex 𝕜 s :=
  ⟨fun h ↦ Function.LeftInverse.preimage_preimage e.right_inv s ▸
    h.linear_preimage e.symm.toLinearMap e.symm.continuous e.symm.injective,
    fun h ↦ h.linear_preimage e.toLinearMap e.continuous e.injective⟩

@[simp]
lemma strictConvex_image {s : Set E} (e : E ≃L[𝕜] F) :
    StrictConvex 𝕜 (e '' s) ↔ StrictConvex 𝕜 s := by
  rw [e.image_eq_preimage, e.symm.strictConvex_preimage]

end ContinuousLinearEquiv

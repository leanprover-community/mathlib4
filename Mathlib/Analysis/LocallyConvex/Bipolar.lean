/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.Dual

/-!

# Bipolar Theorem

-/

variable {𝕜 E F : Type*}

namespace LinearMap


-- `RCLike 𝕜` and `IsScalarTower ℝ 𝕜 E` needed for `RCLike.geometric_hahn_banach_closed_point`
variable [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

-- See `LinearMap.dualPairing_nondegenerate` in Mathlib/LinearAlgebra/Dual
-- `WeakBilin B` is `E` with the σ(E,F)-topology`
-- `((WeakBilin B) →L[𝕜] 𝕜)` is the topological dual of `E` with the σ(E,F)-topology, from
--   Topology/Algebra/Module/WeadDual
-- `WeakBilin.isEmbedding` - topological

variable [Module ℝ E]



variable  [IsScalarTower ℝ 𝕜 E]

-- See Bourbaki TVS II.43 or Rudin Theorem 3.10
lemma dualEmbedding_isSurjective : Function.Surjective (WeakBilin.eval B) := by
  rw [Function.Surjective]
  intro f₁
  sorry

/-
def dualEquiv : F ≃ₗ[𝕜] (WeakBilin B) →L[𝕜] 𝕜 where
  toLinearMap := WeakBilin.eval B


def strictEquiv2 : E ≃ₗ[𝕜] (WeakBilin B.flip) →L[𝕜] 𝕜 where
  toLinearMap := B
-/

open scoped ComplexOrder
theorem Bipolar {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {s : Set E} [Nonempty s] (h : B.Nondegenerate):
    B.flip.polar (B.polar s) = closedAbsConvexHull (E := WeakBilin B) 𝕜 s := by
  apply le_antisymm
  · simp only [Set.le_eq_subset]
    rw [← Set.compl_subset_compl]
    intro x hx
    rw [Set.mem_compl_iff] at hx
    obtain ⟨f,⟨u,⟨hf₁,hf₂⟩⟩⟩ :=
      RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) (E := WeakBilin B)
        absConvex_convexClosedHull.2 isClosed_closedAbsConvexHull hx
    have e3 : RCLike.re (f 0) < u :=
      (hf₁ 0) (absConvexHull_subset_closedAbsConvexHull zero_mem_absConvexHull)
    rw [map_zero, map_zero] at e3
    let g := (1/u : ℝ) • f
    have fg : g = (1/u : ℝ) • f := rfl
    have hg₁ : ∀ a ∈ (closedAbsConvexHull (E := WeakBilin B) 𝕜) s, RCLike.re (g a) < 1 := by
      intro a ha
      rw [fg]
      simp only [ ContinuousLinearMap.coe_smul', Pi.smul_apply]
      rw [RCLike.smul_re]
      have t1 : RCLike.re (f a) < u := hf₁ a ha
      simp [t1]
      rw [← (inv_mul_cancel₀ (lt_iff_le_and_ne.mp e3).2.symm)]
      exact mul_lt_mul_of_pos_left ((hf₁ a) ha) (inv_pos_of_pos e3)
    --have hg₃ : g ∈ B.polar (E := WeakBilin B) s := sorry
    sorry

  · exact closedAbsConvexHull_min (subset_bipolar B s) (polar_AbsConvex _) (polar_isClosed B.flip _)

end LinearMap

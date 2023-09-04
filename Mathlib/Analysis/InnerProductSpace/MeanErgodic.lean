/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Dynamics.BirkhoffSum.NormedSpace

/-!
# Mean Ergodic Theorem in a Hilbert Space

In this file we prove the von Neumann Mean Ergodic Theorem for an operator in a Hilbert space.
It says that for a linear isometry `f : E →ₗᵢ[𝕜] E` of a Hilbert space,
the Birkhoff averages
```
birkhoffAverage 𝕜 f id N x = (N : 𝕜)⁻¹ • ∑ n in Finset.range N, f^[n] x
```
converge to the orthogonal projection of `x` to the subspace of fixed points of `f`.
-/

open Filter Finset Function
open scoped BigOperators Topology

variable {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E]

theorem LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure [NormedSpace 𝕜 E]
    (f : E →ₗ[𝕜] E) (hf : LipschitzWith 1 f) (g : E →L[𝕜] LinearMap.eqLocus f 1)
    (hg_proj : ∀ x : LinearMap.eqLocus f 1, g x = x)
    (hg_ker : (LinearMap.ker g : Set E) ⊆ closure (LinearMap.range (f - 1))) (x : E) :
    Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (𝓝 (g x)) := by
  obtain ⟨y, hy, z, hz, rfl⟩ : ∃ y, g y = 0 ∧ ∃ z, IsFixedPt f z ∧ x = y + z :=
    ⟨x - g x, by simp [hg_proj], g x, (g x).2, by simp⟩
  suffices : Tendsto (birkhoffAverage 𝕜 f _root_.id · y) atTop (𝓝 0)
  · have hgz : g z = z := congr_arg Subtype.val (hg_proj ⟨z, hz⟩)
    simpa [hy, hgz, birkhoffAverage, birkhoffSum, Finset.sum_add_distrib, smul_add]
      using this.add (hz.tendsto_birkhoffAverage 𝕜 _root_.id)
  have : IsClosed {x | Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (𝓝 0)} :=
    isClosed_setOf_tendsto_birkhoffAverage 𝕜 hf uniformContinuous_id continuous_const
  refine closure_minimal (Set.forall_range_iff.2 fun x ↦ ?_) this (hg_ker hy)
  have : Metric.Bounded (Set.range (_root_.id <| f^[·] x)) :=
    bounded_iff_forall_norm_le.2 ⟨‖x‖, Set.forall_range_iff.2 fun n ↦ by
      have H : f^[n] 0 = 0 := (f : E →+ E).iterate_map_zero n
      simpa [H] using (hf.iterate n).dist_le_mul x 0⟩
  have H : ∀ n x y, f^[n] (x - y) = f^[n] x - f^[n] y := (f : E →+ E).iterate_map_sub
  simpa [birkhoffAverage, birkhoffSum, Finset.sum_sub_distrib, smul_sub, H]
    using tendsto_birkhoffAverage_apply_sub_birkhoffAverage 𝕜 this

variable  [InnerProductSpace 𝕜 E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

theorem LinearIsometry.tendsto_birkhoffAverage_orthogonalProjection (f : E →ₗᵢ[𝕜] E) (x : E) :
    Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop
      (𝓝 <| orthogonalProjection (LinearMap.eqLocus f 1) x) := by
  apply (f : E →ₗ[𝕜] E).tendsto_birkhoffAverage_of_ker_subset_closure f.lipschitz
  · exact orthogonalProjection_mem_subspace_eq_self (K := LinearMap.eqLocus f 1)
  · clear x
    rw [ker_orthogonalProjection, ← Submodule.topologicalClosure_coe, SetLike.coe_subset_coe,
      ← Submodule.orthogonal_orthogonal_eq_closure]
    refine Submodule.orthogonal_le fun x hx ↦ ?_
    replace hx : ∀ y, ⟪f y, x⟫ = ⟪y, x⟫ := by
      simpa [Submodule.mem_orthogonal, inner_sub_left, sub_eq_zero] using hx
    suffices ⟪f x - x, f x - x⟫ = 0 by simpa [sub_eq_zero] using this
    rw [inner_sub_right, inner_sub_left, inner_sub_left, f.inner_map_map, hx,
      ← inner_conj_symm x (f x), hx, inner_self_conj, sub_self]

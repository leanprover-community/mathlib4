/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Dynamics.Flow

/-!
# Integral curves on compact manifolds

On a compact boundaryless $C^1$ manifold, every $C^1$ vector field admits a global flow. This is
because compactness provides a uniform lower bound on the existence time of local integral curves
across all points, which allows the local-to-global extension machinery of `UniformTime` to apply.

## Main results

* `exist_uniform_time_of_compactSpace`: Compactness gives a uniform `ε > 0` such that every point
  admits an integral curve on `Ioo (-ε) ε`.
* `exist_isMIntegralCurve_of_compactSpace`: Every point admits a global integral curve.
* `exist_global_flow_of_compactSpace`: There exists a global flow `γ : ℝ → M → M`.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field, compact manifold, global flow
-/

open scoped Manifold Topology

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [T2Space M] [Nonempty M] [CompactSpace M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x}

omit [T2Space M] in
/-- $C^1$ vector fields on compact manifolds satisfy the hypothesis of the uniform time lemma for
the existence of global integral curves. -/
lemma exist_uniform_time_of_compactSpace
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    ∃ ε > 0, ∀ x, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  have (x : M) := exists_mem_nhds_isMIntegralCurveOn_Ioo_of_contMDiffAt 0 (hv.contMDiffAt (x := x))
    BoundarylessManifold.isInteriorPoint
  choose u hu ε hε h using this
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover u hu
  -- pick a point `x₀ ∈ t` minimising `ε`
  obtain ⟨x₀, hx₀, hle⟩ : ∃ x ∈ t, ∀ x' ∈ t, ε x ≤ ε x' := by
    apply Finset.exists_min_image
    exact nonempty_of_union_eq_top_of_nonempty t u (by infer_instance) ht
  refine ⟨ε x₀, hε x₀, fun x ↦ ?_⟩
  obtain ⟨x₁, hx₁, hx⟩ := mem_iUnion₂.mp (show x ∈ ⋃ x₁ ∈ t, u x₁ from ht ▸ mem_univ x)
  obtain ⟨γ, hγ⟩ := h x₁
  obtain ⟨hγ0, hγ, -⟩ := hγ x hx
  exact ⟨fun s ↦ γ ⟨x, s⟩, hγ0,
    hγ.mono (Ioo_subset_Ioo (by linarith [hle x₁ hx₁]) (by linarith [hle x₁ hx₁]))⟩

/-- Given a $C^1$ vector field on a compact manifold and a point `x` on the manifold, there exists
an integral curve starting at `x` that exists for all time. -/
theorem exist_isMIntegralCurve_of_compactSpace
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  have ⟨ε, hε, h⟩ := exist_uniform_time_of_compactSpace hv
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε h x

/-- $C^1$ vector fields on compact manifolds admit global flows. -/
theorem exist_global_flow_of_compactSpace
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    ∃ γ : ℝ → M → M, ∀ x, γ 0 x = x ∧ IsMIntegralCurve (γ · x) v := by
  choose γ hγ using exist_isMIntegralCurve_of_compactSpace hv
  refine ⟨fun t x ↦ γ x t, fun x ↦ hγ x⟩

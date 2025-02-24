/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
# Vector fields with compact support


## Main definitions


## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field
-/

open scoped Manifold Topology

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [T2Space M] [Nonempty M] [CompactSpace M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x}

/-
Use `exists_isIntegralCurve_of_isIntegralCurveOn`

-/

example (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    ∃ ε > 0, ∀ x, ∃ γ : ℝ → M, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-ε) ε) := by
  have (x : M) := exists_mem_nhds_isIntegralCurveOn_Ioo_of_contMDiffAt 0 (hv.contMDiffAt (x := x))
    BoundarylessManifold.isInteriorPoint
  choose u hu ε hε h using this
  have ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover u hu
  -- extract `εmin` as minimum of `{ ε x | x ∈ t }`
  have ht' : t.Nonempty := by
    have : (⊤ : Set M).Nonempty := univ_nonempty
    rw [← ht] at this
    simp only [nonempty_iUnion, exists_prop] at this
    have ⟨x, hx⟩ := this -- missing lemma? `Finset.nonempty_of_exists_mem`
    exact ⟨x, hx.1⟩
  let εmin := Finset.image ε t |>.min' (Finset.image_nonempty.mpr ht')
  have hpos : 0 < εmin := sorry
  have hle (x) (hx : x ∈ t) : εmin ≤ ε x := by
    apply Finset.min'_le
    exact Finset.mem_image_of_mem _ hx
  refine ⟨εmin, hpos, fun x ↦ ?_⟩
  have hx := mem_univ x
  rw [← top_eq_univ, ← ht, mem_iUnion] at hx
  simp only [mem_iUnion, exists_prop] at hx
  replace ⟨x₀, hx₀, hx⟩ := hx
  have ⟨γ, hγ⟩ := h x₀
  replace ⟨hγ0, hγ⟩ := hγ x hx
  refine ⟨γ x, hγ0, ?_⟩
  apply IsIntegralCurveOn.mono hγ
  replace hle := hle x₀ hx₀
  exact Ioo_subset_Ioo (by linarith) (by linarith)







example (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsIntegralCurve γ v := by
  -- construct `ε`


  apply exists_isIntegralCurve_of_isIntegralCurveOn hv


  sorry

/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Topology.Constructions.Graph

/-!
# Graphs of Continuous Functions as Manifolds

This file proves that the graph of a continuous function `f : M → M'` between manifolds
inherits a manifold structure from the domain, and that the inclusion of the graph into
the product `M × M'` is smooth if and only if `f` is smooth.

The homeomorphism between a graph and its domain is in
`Mathlib.Topology.Constructions.Graph`.

## Main Results

* `Set.graphOn.instChartedSpace`: The graph inherits a `ChartedSpace` structure from the domain.
* `Set.graphOn.instIsManifold`: The graph is a smooth manifold when the domain is.
* `Set.graphOn.contMDiff_subtype_val_iff`: Smoothness of graph inclusion into `M × M'` is
  equivalent to smoothness of the graph function on the domain manifold.

## Implementation Notes

The charted space structure on the graph is obtained via `Homeomorph.chartedSpace` applied to
`Set.graphOn.homeomorph`. Chart transitions factor through this homeomorphism, and since the
homeomorphism cancels in the composition, chart compatibility follows from compatibility in
the domain.
-/

@[expose] public section

open Set Topology

namespace Set.graphOn


section Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {M : Type*} [TopologicalSpace M] {M' : Type*} [TopologicalSpace M']
  (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  {n : WithTop ℕ∞}

/--
The graph of a continuous function inherits a `ChartedSpace` structure from the domain.

Given `f : M → M'` continuous on `s ⊆ M`, the graph `s.graphOn f` is charted over `H`
via the homeomorphism `Set.graphOn.homeomorph` and `Homeomorph.chartedSpace`.
-/
def instChartedSpace {s : Set M} {f : M → M'} (hf : ContinuousOn f s) [ChartedSpace H s] :
    ChartedSpace H (s.graphOn f) :=
  (homeomorph hf).chartedSpace

omit [NormedSpace 𝕜 E'] in
/--
The graph of a continuous function on a manifold is itself a manifold.

This follows from the fact that the graph is homeomorphic to the domain,
so chart transitions factor through the homeomorphism which cancels.
-/
theorem instIsManifold {s : Set M} {f : M → M'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    let _ := instChartedSpace (H := H) hf
    IsManifold I n (s.graphOn f) := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace (H := H) hf
  have compat : ∀ {e e' : OpenPartialHomeomorph (s.graphOn f) H},
      e ∈ atlas H (s.graphOn f) →
        e' ∈ atlas H (s.graphOn f) → e.symm.trans e' ∈ contDiffGroupoid n I := by
    rintro e e' ⟨e0, he0_mem, rfl⟩ ⟨e0', he0'_mem, rfl⟩
    have h_grp := (contDiffGroupoid n I).compatible he0_mem he0'_mem
    apply (contDiffGroupoid n I).mem_of_eqOnSource h_grp
    refine ⟨?_, ?_⟩
    · -- source equality
      ext x
      simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
                 OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
                 univ_inter]
      constructor <;> rintro ⟨hx1, hx2⟩
      · exact ⟨hx1.1, hx2⟩
      · exact ⟨⟨hx1, trivial⟩, hx2⟩
    · -- function equality on source
      intro x hx; simp
  haveI : HasGroupoid (H := H) (M := s.graphOn f) (contDiffGroupoid n I) := ⟨compat⟩
  exact IsManifold.mk' I n (s.graphOn f)

omit [NormedSpace 𝕜 E'] in
private theorem homeomorph_liftPropOn {s : Set M} {f : M → M'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    letI := instChartedSpace (H := H) hf
    ChartedSpace.LiftPropOn
      (contDiffGroupoid n I).IsLocalStructomorphWithinAt
      (homeomorph hf).toOpenPartialHomeomorph
      (homeomorph hf).toOpenPartialHomeomorph.source := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace (H := H) hf
  letI : IsManifold I n (s.graphOn f) := instIsManifold I hf
  let h := (homeomorph hf).toOpenPartialHomeomorph
  change ChartedSpace.LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt h h.source
  intro x hx
  refine ⟨h.continuousAt hx |>.continuousWithinAt, fun _ ↦ ?_⟩
  let e : OpenPartialHomeomorph H H := (chartAt H x).symm.trans (h.trans (chartAt H (h x)))
  refine ⟨e, ?_, (by intro y hy; simp [e, h] at hy ⊢), by simp [e, h]⟩
  exact (contDiffGroupoid n I).compatible (chart_mem_atlas H x) (by
    dsimp [h, e]
    exact ⟨chartAt H (homeomorph hf x), chart_mem_atlas H (homeomorph hf x), rfl⟩)

omit [NormedSpace 𝕜 E'] in
/-- Smoothness of the graph-domain homeomorphism for the induced manifold structure on the
graph. -/
theorem contMDiff_homeomorph_toFun {s : Set M} {f : M → M'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    letI := instChartedSpace (H := H) hf
    ContMDiff I I n (homeomorph hf) := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace (H := H) hf
  letI : IsManifold I n (s.graphOn f) := instIsManifold I hf
  let h := (homeomorph hf).toOpenPartialHomeomorph
  simpa [h, contMDiffOn_univ] using
    ((isLocalStructomorphOn_contDiffGroupoid_iff h).1 (homeomorph_liftPropOn I hf)).1

omit [NormedSpace 𝕜 E'] in
/-- Smoothness of the inverse graph-domain homeomorphism for the induced manifold structure on the
graph. -/
theorem contMDiff_homeomorph_invFun {s : Set M} {f : M → M'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    letI := instChartedSpace (H := H) hf
    ContMDiff I I n (homeomorph hf).symm := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace (H := H) hf
  letI : IsManifold I n (s.graphOn f) := instIsManifold I hf
  let h := (homeomorph hf).toOpenPartialHomeomorph
  simpa [h, contMDiffOn_univ] using
    ((isLocalStructomorphOn_contDiffGroupoid_iff h).1 (homeomorph_liftPropOn I hf)).2

/--
If `s` is a `C^n` manifold and `m ≤ n`, then the inclusion map from the graph into the ambient
product space `M × M'` is `C^m` if and only if the graph function is `C^m` on `s`.

This characterizes when the graph, with the manifold structure inherited from the domain,
is a `C^m` embedded submanifold of the product space `M × M'`, assuming
`Subtype.val : s → M` is `C^m`.
-/
theorem contMDiff_subtype_val_iff {s : Set M} {f : M → M'} (hf : ContinuousOn f s)
    {m n : WithTop ℕ∞} [ChartedSpace H M] [ChartedSpace H' M']
    [ChartedSpace H s] [IsManifold I n s] (hmn : m ≤ n)
    (hval : ContMDiff I I m (Subtype.val : s → M)) :
    let _ := instChartedSpace (H := H) hf
    ContMDiff I (I.prod I') m
      (Subtype.val : s.graphOn f → M × M') ↔
    ContMDiff I I' m (fun x : s ↦ f x) := by
  letI : IsManifold I m s := IsManifold.of_le hmn
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace (H := H) hf
  -- The inclusion factors: Subtype.val = (fun x ↦ (x, f x)) ∘ homeomorph
  have factorization : (Subtype.val : s.graphOn f → M × M') =
      (fun x : s ↦ (x.val, f x.val)) ∘ (homeomorph hf) := by
    ext z <;> rcases z with ⟨⟨x, y⟩, hxy⟩ <;>
      simp [Function.comp_apply, (mem_graphOn.mp hxy).2]
  rw [factorization]
  constructor
  · intro h
    have hcomp := h.comp (contMDiff_homeomorph_invFun I hf)
    simp only [Function.comp_assoc, Homeomorph.self_comp_symm, Function.comp_id] at hcomp
    rw [contMDiff_prod_iff] at hcomp
    simpa [Function.comp_apply] using hcomp.2
  · intro hf_smooth
    apply ContMDiff.comp _ (contMDiff_homeomorph_toFun I hf)
    rw [contMDiff_prod_iff]
    constructor
    · simpa [Function.comp_apply] using hval
    · simpa [Function.comp_apply] using hf_smooth

end Manifold

end Set.graphOn

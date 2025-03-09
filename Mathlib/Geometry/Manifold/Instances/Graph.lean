/-
Copyright (c) 2023 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# The graph of a continuous function on a `C^k` manifold is a `C^k` manifold

We show that for manifold `M` which has the structure groupoid `G`, the graph of any continuous
function `f : M → M'`, defined as `{(x, f x) | x ∈ M} ⊆ M × M'`, has manifold structure with the
structure groupoid `G` that is equivalent to the one on `M`.

## TODO

Revisit this once we have a more developed theory of embedded submanifolds. Show that if `f` is
`C^k` and `M'` is a `C^k` manifold, the graph is an embedded submanifold of `M × M'`.
-/


noncomputable section

open Function Set TopologicalSpace

open scoped Manifold

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
  [TopologicalSpace M] [HM : ChartedSpace H M] {M' : Type _} [TopologicalSpace M']
  {G : StructureGroupoid H} {hM : HasGroupoid M G} (f : M → M') (hf : Continuous f)

/-- A structure to hold the graph of a continuous function on a manifold -/
structure cont_graph :=
  (f : M → M')
  (hf : Continuous f)
  (graph : Set (M × M'))
  (graphMap : M → graph)
  (graphMap_cont : Continuous graphMap)

/-- Constructor for `cont_graph` -/
def cont_graph.mk' (f : M → M') (hf : Continuous f) :
    @cont_graph M _ M' _ :=
  {
    f := f
    hf := hf
    graph := setOf (fun x => x.snd = f x.fst),
    graphMap := fun x => ⟨(x, f x), rfl⟩,
    graphMap_cont := by
      simp only [graphMap]
      apply (continuous_id.prod_mk hf).subtype_mk,
  }

/-- This provides a one-to-one corresondence between the atlas on `M` and the atlas on the graph of
  `f : M → M'`. -/
def projChart (ch : LocalHomeomorph M H) : LocalHomeomorph (cont_graph.mk' f hf).graph H where
  source := setOf (fun x => x.1.fst ∈ ch.source)
  target := ch.target
  toFun x := ch.toFun x.1.fst
  invFun x := ⟨(ch.invFun x, f (ch.invFun x)), rfl⟩
  map_source' := by
    simp only [Subtype.forall, Prod.forall]
    intro a b _
    apply ch.map_source'
  map_target' := by
    intro x
    apply ch.map_target'
  left_inv' := by
    simp only [Subtype.forall, Subtype.mk.injEq, Prod.forall, Prod.mk.injEq]
    intro a b ab ha
    simp only [cont_graph.mk'] at ab
    have hinva := ch.left_inv ha
    exact And.intro hinva (Eq.subst (motive := fun a => b = f a) hinva.symm ab).symm
  right_inv' := by apply LocalHomeomorph.right_inv
  open_source := ch.open_source.preimage continuous_id.subtype_val.fst
  open_target := ch.open_target
  continuous_toFun := by
    simp only []
    apply ContinuousOn.comp
    · exact ch.continuous_toFun
    · exact continuous_id.subtype_val.fst.continuousOn
    · simp [MapsTo]
  continuous_invFun := by
    simp only [cont_graph.mk']
    have hch := continuousOn_iff'.mp ch.continuous_invFun
    apply continuousOn_iff'.mpr
    intro t ht
    have hu := hch (t.preimage ((cont_graph.mk' f hf).graphMap))
      (ht.preimage ((cont_graph.mk' f hf).graphMap_cont))
    cases hu with
    | intro u hu =>
      use u
      apply And.intro
      · exact hu.1
      · rw [← hu.2]
        apply ext
        intro x
        simp only [cont_graph.mk', mem_inter_iff, mem_preimage]

/-- The graph of `f : M → M'` is a `ChartedSpace` with the same model space as `M`. -/
instance cont_graph_charted : ChartedSpace H (cont_graph.mk' f hf).graph where
  atlas := {projChart f hf ch | ch ∈ HM.atlas}
  chartAt x := projChart f hf (HM.chartAt x.1.fst)
  mem_chart_source x := by simp [projChart]
  chart_mem_atlas x := by
    use HM.chartAt x.1.fst
    simp

/-- The graph of `f : M → M'` has an atlas in the same groupoid as `M`. -/
theorem cont_graph_mfld : HasGroupoid (cont_graph.mk' f hf).graph G where
  compatible := by
    intro e e' he he'
    cases he with
    | intro e1 he1 => cases he' with
      | intro e1' he1' => rw [← he1.2, ← he1'.2]; exact hM.compatible he1.1 he1'.1

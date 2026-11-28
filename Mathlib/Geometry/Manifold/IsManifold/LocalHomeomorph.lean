/-
Copyright (c) 2026 Pepa Montero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pepa Montero
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Notation

/-!
# Manifold structure induced by a local homeomorphism

Let `M` be a `C^n` manifold and let `f : M → M'` be a local homeomorphism with a right inverse`g`.

Pushing the charts of `M` forward along `f` gives a charted space structure
`IsLocalHomeomorph.chartedSpaceOfRightInverse` on `M'`, where the chart at `y : M'` is the local
inverse of `f` at `g y : M`, followed by the chart of `M` at `g y`.

This file shows that, for this structure, if `f` satisfies a certain condition
`ContMDiffTransitions I n f`, then `M'` is a `C^n` manifold. It also shows that `f` and its local
inverses are then `C^n`, and characterizes the `C^n` maps out of `M'`.

## Main definitions

* `ContMDiffTransitions I n f`: any two points `x`, `y` with `f x = f y` are related by a map
  `σ : M → M` with `σ x = y` which preserves `f` near `x` and is `C^n` at `x`.

## Main results

All results are for the charted space structure `hf.chartedSpaceOfRightInverse hg` on `M'`:

* `IsLocalHomeomorph.isManifold_of_rightInverse`: if `M` is a `C^n` manifold and
  `ContMDiffTransitions I n f` holds, then `M'` is a `C^n` manifold.
* `IsLocalHomeomorph.contMDiff_of_rightInverse`: if `ContMDiffTransitions I n f` holds, then `f`
  is `C^n`.
* `IsLocalHomeomorph.contMDiffOn_localInverseAt_rightInverse`: if `ContMDiffTransitions I n f`
  holds, then the local inverses of `f` are `C^n` on their sources.
* `IsLocalHomeomorph.contMDiff_iff_contMDiff_comp`: if `ContMDiffTransitions I n f` holds, then a
  map `φ : M' → N` is `C^n` if and only if `φ ∘ f : M → N` is.

## TODO

* Show that `f` is a local diffeomorphism. This follows from the results above, but the current
  API for `IsLocalDiffeomorphAt` is limited I believe.
* I believe the converse is true: if `f` is a `C^n` local diffeomorphism for this structure,
  then `ContMDiffTransitions I n f` holds.

## Tags

smooth manifold, local homeomorphism, charted space
-/

public noncomputable section

open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M' : Type*} [TopologicalSpace M']
  {f : M → M'} (hf : IsLocalHomeomorph f)
  {g : M' → M} (hg : Function.RightInverse g f)

/-! ### The ContMDiffTransitions condition -/

variable (I n f) in
/-- Any two points `x`, `y` with `f x = f y` are related by a map `σ : M → M` with `σ x = y`
which preserves `f` near `x` and is `C^n` at `x`. -/
def ContMDiffTransitions : Prop :=
  ∀ {x y : M}, f x = f y → ∃ σ : M → M, σ x = y ∧ CMDiffAt n σ x ∧ f ∘ σ =ᶠ[𝓝 x] f

namespace IsLocalHomeomorph

/-- If `ContMDiffTransitions I n f` holds, the transition map between two local inverses of `f`
is `C^n` on its source. -/
lemma contMDiffOn_localInverseAt_symm_trans
    (h : ContMDiffTransitions I n f) (x y : M) :
    CMDiff[((hf.localInverseAt x).symm ≫ₕ hf.localInverseAt y).source] n
      ((hf.localInverseAt x).symm ≫ₕ hf.localInverseAt y) := by
  set τ := (hf.localInverseAt x).symm ≫ₕ hf.localInverseAt y
  have hτ {z : M} (hz : z ∈ τ.source) : f (τ z) = f z := by
    simpa [τ] using hf.apply_localInverseAt_of_mem (by simpa using hz.2)
  intro z hz
  obtain ⟨σ, hσz, hσ, hfσ⟩ := h (hτ hz).symm
  refine (hσ.congr_of_eventuallyEq ?_).contMDiffWithinAt
  have ht : (hf.localInverseAt y).target ∈ 𝓝 (σ z) :=
    (hf.localInverseAt y).open_target.mem_nhds (hσz ▸ (τ.map_source hz).1)
  filter_upwards [τ.open_source.mem_nhds hz, hσ.continuousAt.preimage_mem_nhds ht, hfσ]
    with z' hz' hσz' hfσz'
  exact hf.injOn_localInverseAt_target (τ.map_source hz').1 hσz' ((hτ hz').trans hfσz'.symm)

/-! ### Manifold structure -/

/-- If `M` is a `C^n` manifold and `ContMDiffTransitions I n f` holds, then `M'` is a `C^n`
manifold for the charts `hf.chartedSpaceOfRightInverse hg` pushed forward from `M`. -/
theorem isManifold_of_rightInverse [IsManifold I n M]
    (h : ContMDiffTransitions I n f) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    IsManifold I n M' := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  refine { compatible := ?_ }
  rintro - - ⟨y, rfl⟩ ⟨y', rfl⟩
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, (chartAt H (g y)).symm.trans_assoc,
    ← (hf.localInverseAt (g y)).symm.trans_assoc]
  exact symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
    (IsManifold.chart_mem_maximalAtlas _) (IsManifold.chart_mem_maximalAtlas _)
    (hf.contMDiffOn_localInverseAt_symm_trans h _ _)
    (hf.contMDiffOn_localInverseAt_symm_trans h _ _)

/-! ### Smoothness of `f` -/

/-- If `g` is a right inverse of `f`, `f` is `C^n` at `g y`. -/
lemma contMDiffAt_of_rightInverse (y : M') :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiffAt n f (g y) := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  suffices CMDiffAt n (hf.localInverseAt (g y)).symm (g y) by rwa [hf.localInverseAt_symm] at this
  rw [contMDiffAt_iff]
  constructor
  · exact OpenPartialHomeomorph.continuousAt _ (by simp)
  · rw [show (hf.localInverseAt (g y)).symm (g y) = y by simpa using hg y]
    refine contDiffWithinAt_id.congr_of_eventuallyEq_of_mem ?_ (Set.mem_range_self _)
    have hgy : extChartAt I (g y) (g y) ∈ (extChartAt I y).target := by
      have := mem_extChartAt_target (I := I) y
      change extChartAt I (g y) (hf.localInverseAt (g y) y) ∈ _ at this
      rwa [show hf.localInverseAt (g y) y = g y by
        simpa [hg y] using hf.localInverseAt_apply_self (x := g y)] at this
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hgy] with z hz
    exact (extChartAt I y).right_inv hz

/-- If `ContMDiffTransitions I n f` holds, then `f` is `C^n`. -/
theorem contMDiff_of_rightInverse (h : ContMDiffTransitions I n f) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiff n f := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  intro x
  obtain ⟨σ, hσx, hσ, hfσ⟩ := h (hg (f x)).symm
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hfσ.symm
  refine ContMDiffAt.comp x ?_ hσ
  rw [hσx]
  exact hf.contMDiffAt_of_rightInverse hg (f x)

/-! ### Maps out of `M'` -/

variable {H' : Type*} [TopologicalSpace H']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners 𝕜 E' H'}

-- TODO: this and `contMDiffAt_of_rightInverse` use a very similar argument. can this be simplified?
/-- If `g` is a right inverse of `f`, the local inverse of `f` at `g y` is `C^n` at `y`. -/
lemma contMDiffAt_localInverseAt_rightInverse (y : M') :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiffAt n (hf.localInverseAt (g y)) y := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  rw [contMDiffAt_iff]
  constructor
  · apply OpenPartialHomeomorph.continuousAt
    simpa [hg y] using hf.apply_self_mem_localInverseAt_source (x := g y)
  · rw [show hf.localInverseAt (g y) y = g y by
      simpa [hg y] using hf.localInverseAt_apply_self (x := g y)]
    refine contDiffWithinAt_id.congr_of_eventuallyEq_of_mem ?_ (Set.mem_range_self _)
    filter_upwards [extChartAt_target_mem_nhdsWithin y] with z hz
    exact (extChartAt I y).right_inv hz

/-- If `g` is a right inverse of `f` and `φ ∘ f` is `C^n` at `g y`,
then `φ : M' → N` is `C^n` at `y`. -/
lemma contMDiffAt_of_contMDiffAt_comp {φ : M' → N} {y : M'} (hφ : CMDiffAt n (φ ∘ f) (g y)) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiffAt n φ y := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  have : φ =ᶠ[𝓝 y] (φ ∘ f) ∘ hf.localInverseAt (g y) := by
    have hs : (hf.localInverseAt (g y)).source ∈ 𝓝 y := by
      refine (hf.localInverseAt (g y)).open_source.mem_nhds ?_
      simpa [hg y] using hf.apply_self_mem_localInverseAt_source (x := g y)
    filter_upwards [hs] with y' hy'
    simp [hf.apply_localInverseAt_of_mem hy']
  refine ContMDiffAt.congr_of_eventuallyEq ?_ this
  refine ContMDiffAt.comp y ?_ (hf.contMDiffAt_localInverseAt_rightInverse hg y)
  rwa [show hf.localInverseAt (g y) y = g y by
    simpa [hg y] using hf.localInverseAt_apply_self (x := g y)]

/-- If `φ ∘ f` is `C^n`, then so is `φ : M' → N`. -/
lemma contMDiff_of_contMDiff_comp {φ : M' → N} (hφ : CMDiff n (φ ∘ f)) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiff n φ :=
  fun y ↦ hf.contMDiffAt_of_contMDiffAt_comp hg (hφ (g y))

/-- If `ContMDiffTransitions I n f` holds, then `φ : M' → N` is `C^n` if and only if `φ ∘ f`
is. -/
theorem contMDiff_iff_contMDiff_comp
    (h : ContMDiffTransitions I n f) {φ : M' → N} :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiff n φ ↔ CMDiff n (φ ∘ f) :=
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  ⟨fun hφ ↦ hφ.comp (hf.contMDiff_of_rightInverse hg h), hf.contMDiff_of_contMDiff_comp hg⟩

/-- If `F : M → N` is `C^n` and factors through `f`, then `F ∘ g : M' → N` is `C^n`,
for `g` a right inverse of `f`. -/
lemma contMDiff_comp_rightInverse_of_contMDiff {F : M → N}
    (hFf : F.FactorsThrough f) (hF : CMDiff n F) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiff n (F ∘ g) :=
  hf.contMDiff_of_contMDiff_comp hg <| hF.congr fun x ↦ hFf (hg (f x))

/-! ### Smoothness of the local inverses of `f` -/

/-- If `ContMDiffTransitions I n f` holds, then for every `x : M` the local inverse of `f` at `x`
is `C^n` on its source. -/
theorem contMDiffOn_localInverseAt_rightInverse
    (h : ContMDiffTransitions I n f) (x : M) :
    letI : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
    CMDiff[(hf.localInverseAt x).source] n (hf.localInverseAt x) := by
  let : ChartedSpace H M' := hf.chartedSpaceOfRightInverse hg
  intro y hy
  refine (hf.contMDiffAt_of_contMDiffAt_comp hg ?_).contMDiffWithinAt
  simpa using (hf.contMDiffOn_localInverseAt_symm_trans h (g y) x).contMDiffAt <|
    (OpenPartialHomeomorph.open_source _).mem_nhds (by simpa [hg y] using hy)

end IsLocalHomeomorph

end

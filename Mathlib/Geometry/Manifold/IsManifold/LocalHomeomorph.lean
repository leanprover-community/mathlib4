/-
Copyright (c) 2026 Pepa Montero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pepa Montero
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Notation

/-!
# Manifold structure induced by a local homeomorphism

Let `M` be a `C^n` manifold and let `f : M → M'` be a local homeomorphism with a right inverse `g`.

Pushing the charts of `M` forward along `f` gives a charted space structure
`IsLocalHomeomorph.chartedSpaceOfRightInverse` on `M'`, where the chart at `y : M'` is the local
inverse of `f` at `g y : M`, followed by the chart of `M` at `g y`.

This file shows that, for this structure, if `f` satisfies a certain condition
`ContMDiffTransitions I n f`, then `M'` is a `C^n` manifold.

## Main definitions

* `ContMDiffTransitions I n f`: any two points `x`, `y` with `f x = f y` are related by a map
  `σ : M → M` with `σ x = y` which preserves `f` near `x` and is `C^n` at `x`.

## Main results

* `IsLocalHomeomorph.isManifold_of_rightInverse`: if `M` is a `C^n` manifold and
  `ContMDiffTransitions I n f` holds, then `M'` is a `C^n` manifold for the charted space
  structure `hf.chartedSpaceOfRightInverse hg`.

## TODO

* Show that, under `ContMDiffTransitions I n f`, the map `f` and its local inverses are `C^n`,
  and that a map `φ : M' → N` is `C^n` if and only if `φ ∘ f` is.
* Show that `f` is then a local diffeomorphism.
* Show the converse: if `f` is a `C^n` local diffeomorphism for this structure, then
  `ContMDiffTransitions I n f` holds.
* Use this to construct manifold structures on quotients `M ⧸ G` by suitable group actions.

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

end IsLocalHomeomorph

end

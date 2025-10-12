/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # Local properties of smooth functions which depend on both the source and target

In this file, we consider local properties of functions between manifolds, which depend on both the
source and the target: more precisely, properties `P` of functions `f : M → N` such that
`f` has property `P` if and only if there is a suitable pair of charts on `M` and `N`, respectively,
such that `f` read in these charts has a particular form.
The motivating example of this general description are immersions and submersions:
`f : M → N` is an immersion at `x` iff there are charts `φ` and `ψ` of `M` and `N` around `x` and
`f x`, respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`. Similarly, `f` is a
submersion at `x` iff it looks like a projection `(u, v) ↦ u` in suitable charts near `x` and `f x`.

Studying such local properties allows proving several lemmas about immersions and submersions
only once. In `IsImmersionEmbedding.lean`, we prove that being an immersion at `x` is indeed a
local property of this form.

## Main definitions and results

* `Manifold.LocalSourceTargetPropertyAt` captures a local property of the above form:
  for each `f : M → N`, and pair of charts `φ` of `M` and `ψ` of `N`, the local property is either
  safisfied or not.
  We ask that the property be stable under congruence and under restriction of `φ`.
* `Manifold.LiftSourceTargetPropertyAt f x P`, where `P` is a `LocalSourceTargetPropertyAt`,
  defines a local property of functions of the above shape:
  `f` has this property at `x` if there exist charts `φ` and `ψ` such that `P f φ ψ` holds.
* `Manifold.LiftSourceTargetPropertyAt.congr_of_eventuallyEq`: if `f` has property `P` at `x`
  and `g` equals `f` near `x`, then `g` also has property `P` at `x`.

-/

open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 E E' F F' H H' G G' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}

variable {M M' N N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}

namespace Manifold

/-- Structure recording good behaviour of a property of functions `M → N` w.r.t. to compatible
choices of both a chart on `M` and `N`. Currently, we ask for the property being stable under
restriction of the domain chart, and local in the target.

Motivating examples are immersions and submersions of smooth manifolds. -/
structure IsLocalSourceTargetProperty
    (P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop) : Prop where
  mono_source : ∀ {f : M → N}, ∀ {φ : OpenPartialHomeomorph M H}, ∀ {ψ : OpenPartialHomeomorph N G},
    ∀ {s : Set M}, IsOpen s → P f φ ψ → P f (φ.restr s) ψ
  -- Note: the analogous `mono_target` statement is true for both immersions and submersions.
  -- If and when a future lemma requires it, add this here.
  congr : ∀ {f g : M → N}, ∀ {φ : OpenPartialHomeomorph M H}, ∀ {ψ : OpenPartialHomeomorph N G},
    ∀ {s : Set M}, EqOn f g s → IsOpen s → φ.source ⊆ s → P f φ ψ → P g φ ψ

variable (I J n) in
/-- Data witnessing the fact that `f` has local property `P` at `x` -/
structure LocalPresentationAt (f : M → N) (x : M)
    (P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop) where
  /-- A choice of chart on the domain `M` of the local property `P` of `f` at `x`:
  w.r.t. this chart and `codChart`, `f` has the local property `P` at `x`. -/
  domChart : OpenPartialHomeomorph M H
  /-- A choice of chart on the target `N` of the local property `P` of `f` at `x`:
  w.r.t. this chart and `domChart`, `f` has the local property `P` at `x`. -/
  codChart : OpenPartialHomeomorph N G
  mem_domChart_source : x ∈ domChart.source
  mem_codChart_source : f x ∈ codChart.source
  domChart_mem_maximalAtlas : domChart ∈ IsManifold.maximalAtlas I n M
  codChart_mem_maximalAtlas : codChart ∈ IsManifold.maximalAtlas J n N
  source_subset_preimage_source : domChart.source ⊆ f ⁻¹' codChart.source
  property : P f domChart codChart

variable (I J n) in
/-- A property of smooth functions `M → N` which is local at both the source and target:
a property `P` is local at `x` iff there exist charts `φ` and `ψ` of `M` and `N` around
`x` and `f x`, respectively, such that `f` satisfies the property w.r.t. `φ` and `ψ`.

The motivating example are smooth immersions and submersions: the corresponding condition is that
`f` look like the inclusion `u ↦ (u, 0)` (resp. a projection `(u, v) ↦ u`)
in the charts `φ` and `ψ`.
-/
def LiftSourceTargetPropertyAt (f : M → N) (x : M)
    (P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop) : Prop :=
  Nonempty (LocalPresentationAt I J n f x P)

namespace LiftSourceTargetPropertyAt

variable {f g : M → N} {x : M}
  {P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop}

/-- A choice of charts witnessing the local property `P` of `f` at `x`. -/
noncomputable def localPresentationAt (h : LiftSourceTargetPropertyAt I J n f x P) :
    LocalPresentationAt I J n f x P :=
  Classical.choice h

/-- A choice of chart on the domain `M` of a local property of `f` at `x`:
w.r.t. this chart and `h.codChart`, `f` has the local property `P` at `x`.
The particular chart is arbitrary, but this choice matches the witness given by `h.codChart`. -/
noncomputable def domChart (h : LiftSourceTargetPropertyAt I J n f x P) :
    OpenPartialHomeomorph M H :=
  h.localPresentationAt.domChart

/-- A choice of chart on the co-domain `N` of a local property of `f` at `x`:
w.r.t. this chart and `h.domChart`, `f` has the local property `P` at `x`
The particular chart is arbitrary, but this choice matches the witness given by `h.domChart`. -/
noncomputable def codChart (h : LiftSourceTargetPropertyAt I J n f x P) :
    OpenPartialHomeomorph N G :=
  h.localPresentationAt.codChart

lemma mem_domChart_source (h : LiftSourceTargetPropertyAt I J n f x P) :
    x ∈ h.domChart.source :=
  h.localPresentationAt.mem_domChart_source

lemma mem_codChart_source (h : LiftSourceTargetPropertyAt I J n f x P) :
    f x ∈ h.codChart.source :=
  h.localPresentationAt.mem_codChart_source

lemma domChart_mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  h.localPresentationAt.domChart_mem_maximalAtlas

lemma codChart_mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) :
    h.codChart ∈ IsManifold.maximalAtlas J n N :=
  h.localPresentationAt.codChart_mem_maximalAtlas

lemma source_subset_preimage_source
 (h : LiftSourceTargetPropertyAt I J n f x P) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source :=
  h.localPresentationAt.source_subset_preimage_source

lemma property (h : LiftSourceTargetPropertyAt I J n f x P) : P f h.domChart h.codChart :=
  h.localPresentationAt.property

omit [ChartedSpace H M] [ChartedSpace G N] in
lemma congr_iff (hP : IsLocalSourceTargetProperty P)
    {f g : M → N} {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph N G} {s : Set M}
    (hs : IsOpen s) (hφ : φ.source ⊆ s) (hfg : EqOn f g s) :
    P f φ ψ ↔ P g φ ψ :=
  ⟨hP.congr hfg hs hφ, hP.congr hfg.symm hs hφ⟩

-- XXX: should `OpenPartialHomeomorph.restr_source'` be tagged with grind?
/-- If `P` is a local property, by monotonicity w.r.t. restricting `domChart`,
if `f` is continuous at `x`, to prove `LiftSourceTargetPropertyAt I I' n f x P`
we need not check the condition `f '' domChart.source ⊆ codChart.source`. -/
lemma mk_of_continuousAt (hf : ContinuousAt f x)
    (hP : IsLocalSourceTargetProperty P)
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hfP : P f domChart codChart) : LiftSourceTargetPropertyAt I J n f x P := by
  obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp <|
    hf.preimage_mem_nhds (codChart.open_source.mem_nhds hfx)
  exact ⟨domChart.restr s, codChart, by grind [OpenPartialHomeomorph.restr_source'], hfx,
    restr_mem_maximalAtlas (contDiffGroupoid n I) hdomChart hsopen, hcodChart,
    by grind [OpenPartialHomeomorph.restr_source'], hP.mono_source hsopen hfP⟩

/-- If `P` is monotone w.r.t. restricting `domChart` and closed under congruence,
if `f` has property `P` at `x` and `f` and `g` are eventually equal near `x`,
then `g` has property `P` at `x`. -/
lemma congr_of_eventuallyEq (hP : IsLocalSourceTargetProperty P)
    (hf : LiftSourceTargetPropertyAt I J n f x P)
    (h' : f =ᶠ[𝓝 x] g) : LiftSourceTargetPropertyAt I J n g x P := by
  obtain ⟨s', hxs', hfg⟩ := h'.exists_mem
  obtain ⟨s, hss', hs, hxs⟩ := mem_nhds_iff.mp hxs'
  refine ⟨hf.domChart.restr s, hf.codChart, ?_, ?_, ?_, hf.codChart_mem_maximalAtlas, ?_, ?_⟩
  · simpa using ⟨mem_domChart_source hf, by rwa [interior_eq_iff_isOpen.mpr hs]⟩
  · exact hfg (mem_of_mem_nhds hxs') ▸ mem_codChart_source hf
  · exact restr_mem_maximalAtlas _ hf.domChart_mem_maximalAtlas hs
  · trans s' ∩ f ⁻¹' hf.codChart.source
    · apply subset_inter
      · exact Subset.trans (by simp [interior_eq_iff_isOpen.mpr hs]) hss'
      · exact Subset.trans (by simp) hf.source_subset_preimage_source
    · rw [hfg.inter_preimage_eq]; exact inter_subset_right
  · apply hP.congr (hfg.mono hss') hs
    · grind [OpenPartialHomeomorph.restr_source']
    exact hP.mono_source hs hf.property

/-- If `P` is monotone w.r.t. restricting `domChart` and closed under congruence,
and `f` and `g` are eventually equal near `x`,
then `f` has property `P` at `x` if and only if `g` has property `P` at `x`. -/
lemma congr_iff_eventuallyEq (hP : IsLocalSourceTargetProperty P) (h' : f =ᶠ[nhds x] g) :
    LiftSourceTargetPropertyAt I J n f x P ↔ LiftSourceTargetPropertyAt I J n g x P :=
  ⟨fun hf ↦ hf.congr_of_eventuallyEq hP h', fun hg ↦ hg.congr_of_eventuallyEq hP h'.symm⟩

lemma prodMap [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    {Q : (M' → N') → OpenPartialHomeomorph M' H' → OpenPartialHomeomorph N' G' → Prop}
    {R : ((M × M') → (N × N')) → OpenPartialHomeomorph (M × M') (H × H') →
      OpenPartialHomeomorph (N × N') (G × G') → Prop}
    -- TODO: reorder so hf is the first explicit argument
    (h : ∀ {f : M → N}, ∀ {φ₁ : OpenPartialHomeomorph M H}, ∀ {ψ₁ : OpenPartialHomeomorph N G},
      ∀ {g : M' → N'}, ∀ {φ₂ : OpenPartialHomeomorph M' H'}, ∀ {ψ₂ : OpenPartialHomeomorph N' G'},
      P f φ₁ ψ₁ → Q g φ₂ ψ₂ → R (Prod.map f g) (φ₁.prod φ₂) (ψ₁.prod ψ₂))
    (hf : LiftSourceTargetPropertyAt I J n f x P) {g : M' → N'} {x' : M'}
    (hg : LiftSourceTargetPropertyAt I' J' n g x' Q) :
    LiftSourceTargetPropertyAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') R := by
  use hf.domChart.prod hg.domChart, hf.codChart.prod hg.codChart
  · simp [hf.mem_domChart_source, hg.mem_domChart_source]
  · simp [mem_codChart_source hf, mem_codChart_source hg]
  · exact IsManifold.mem_maximalAtlas_prod
      (domChart_mem_maximalAtlas hf) (domChart_mem_maximalAtlas hg)
  · apply IsManifold.mem_maximalAtlas_prod
      (codChart_mem_maximalAtlas hf) (codChart_mem_maximalAtlas hg)
  · simp only [OpenPartialHomeomorph.prod_toPartialEquiv, PartialEquiv.prod_source,
      preimage_prod_map_prod]
    exact prod_mono hf.source_subset_preimage_source hg.source_subset_preimage_source
  · exact h hf.property hg.property

end LiftSourceTargetPropertyAt

end Manifold

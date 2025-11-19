/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.LocalSourceTargetProperty

/-! # Smooth immersions and embeddings

In this file, we define `C^n` immersions and embeddings between `C^n` manifolds.
The correct definition in the infinite-dimensional setting differs from the standard
finite-dimensional definition (concerning the `mfderiv` being injective): future pull requests will
prove that our definition implies the latter, and that both are equivalent for finite-dimensional
manifolds.

This definition can be conveniently formulated in terms of local properties: `f` is an immersion at
`x` iff there exist suitable charts near `x` and `f x` such that `f` has a nice form w.r.t. these
charts. Most results below can be deduced from more abstract results about such local properties.
This shortens the overall argument, as the definition of submersions has the same general form.

## Main definitions
* `IsImmersionAt F I J n f x` means a map `f : M → N` between `C^n` manifolds `M` and `N`
  is an immersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`, w.r.t. some equivalence
  `E' ≃L[𝕜] E × F`. We do not demand that `f` be differentiable (this follows from this definition).
* `IsImmersion F I J n f` means `f : M → N` is an immersion at every point `x : M`.

## Main results
* `IsImmersionAt.congr_of_eventuallyEq`: being an immersion is a local property.
  If `f` and `g` agree near `x` and `f` is an immersion at `x`, so is `g`

## TODO
* `IsImmersionAt.contMDiffAt`: if f is an immersion at `x`, it is `C^n` at `x`.
* `IsImmersion.contMDiff`: if f is an immersion, it is `C^n`.
* `IsImmersionAt.prodMap`: the product of two immersions is an immersion
* If `f` is an immersion at `x`, its differential splits, hence is injective.
* If `f : M → N` is a map between Banach manifolds, `mfderiv I J f x` splitting implies `f` is an
  immersion at `x`. (This requires the inverse function theorem.)
* `IsImmersionAt.comp`: if `f : M → N` and `g: N → N'` are maps between Banach manifolds such that
  `f` is an immersion at `x : M` and `g` is an immersion at `f x`, then `g ∘ f` is an immersion
  at `x`.
* `IsImmersion.comp`: the composition of immersions (between Banach manifolds) is an immersion
* If `f : M → N` is a map between finite-dimensional manifolds, `mfderiv I J f x` being injective
  implies `f` is an immersion at `x`.
* define smooth embeddings, and deduce analogous results for these

## References

* [Juan Margalef-Roig and Enrique Outerelo Dominguez, *Differential topology*][roigdomingues2012]

-/

open scoped Topology ContDiff
open Function Set Manifold

namespace Manifold

universe u
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E''' : Type*} {E'' F F' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}

variable (F I J M N) in
/-- The local property of being an immersion at a point: `f : M → N` is an immersion at `x` if
there exist charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively, such that in these
charts, `f` looks like the inclusion `u ↦ (u, 0)`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`. -/
def ImmersionAtProp : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop :=
  fun f domChart codChart ↦ ∃ equiv : (E × F) ≃L[𝕜] E'',
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- Being an immersion at `x` is a local property. -/
lemma isLocalSourceTargetProperty_immersionAtProp :
    IsLocalSourceTargetProperty (ImmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs hf := by
    obtain ⟨equiv, hf⟩ := hf
    exact ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg hf := by
    obtain ⟨equiv, hf⟩ := hf
    refine ⟨equiv, EqOn.trans (fun x hx ↦ ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x ∈ φ.source := by simp_all
    grind

variable (F I J n) in
/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`.
-/
irreducible_def IsImmersionAt (f : M → N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N)

-- Lift the universe from E'', to avoid a free universe parameter.
variable (I J n) in
irreducible_def IsImmersionAt2 (f : M → N) (x : M) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F), IsImmersionAt F I J n f x

variable {f g : M → N} {x : M}

namespace IsImmersionAt2

-- Note: this lemma becomes more cumbersome to state, as F must live in the same universe as E'' now!
lemma mk_of_charts (equiv : (E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph M H)
    (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt2 I J n f x := by
  simp_rw [IsImmersionAt2_def, IsImmersionAt_def]
  use F, (by infer_instance), (by infer_instance), domChart, codChart
  use equiv

/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt2 I J n f x := by
  simp_rw [IsImmersionAt2_def, IsImmersionAt_def]
  use F, (by infer_instance), (by infer_instance)
  exact LiftSourceTargetPropertyAt.mk_of_continuousAt hf isLocalSourceTargetProperty_immersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

/-- Choice of complement yada yada -/
def complement (h : IsImmersionAt2 I J n f x) : Type u := by
  rw [IsImmersionAt2_def] at h
  exact Classical.choose h

noncomputable instance (h : IsImmersionAt2 I J n f x) : NormedAddCommGroup h.complement := by
  rw [IsImmersionAt2_def] at h
  exact Classical.choose <| Classical.choose_spec h

noncomputable instance (h : IsImmersionAt2 I J n f x) : NormedSpace 𝕜 h.complement := by
  rw [IsImmersionAt2_def] at h
  exact Classical.choose <| Classical.choose_spec <| Classical.choose_spec h

lemma isImmersionAt_complement (h : IsImmersionAt2 I J n f x) :
    IsImmersionAt h.complement I J n f x := by
  rw [IsImmersionAt2_def] at h
  exact Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

/-- A choice of chart on the domain `M` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
noncomputable def domChart (h : IsImmersionAt2 I J n f x) : OpenPartialHomeomorph M H := by
  let e := h.isImmersionAt_complement
  rw [IsImmersionAt_def] at e
  exact e.domChart

/-- A choice of chart on the co-domain `N` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
noncomputable def codChart (h : IsImmersionAt2 I J n f x) : OpenPartialHomeomorph N G := by
  let e := h.isImmersionAt_complement
  rw [IsImmersionAt_def] at e
  exact e.codChart

lemma mem_domChart_source (h : IsImmersionAt2 I J n f x) : x ∈ h.domChart.source := by
  let e := h.isImmersionAt_complement
  rw [IsImmersionAt_def] at e
  exact e.mem_domChart_source

lemma mem_codChart_source (h : IsImmersionAt2 I J n f x) : f x ∈ h.codChart.source := by
  let e := h.isImmersionAt_complement
  rw [IsImmersionAt_def] at e
  exact e.mem_codChart_source

lemma domChart_mem_maximalAtlas (h : IsImmersionAt2 I J n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M := by
  let e := h.isImmersionAt_complement
  rw [IsImmersionAt_def] at e
  exact e.domChart_mem_maximalAtlas

lemma codChart_mem_maximalAtlas (h : IsImmersionAt2 I J n f x) :
    h.codChart ∈ IsManifold.maximalAtlas J n N := by
  let e := h.isImmersionAt_complement
  rw [IsImmersionAt_def] at e
  exact e.codChart_mem_maximalAtlas

lemma source_subset_preimage_source (h : IsImmersionAt2 I J n f x) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source := by
  let e := h.isImmersionAt_complement
  rw [IsImmersionAt_def] at e
  exact e.source_subset_preimage_source

/-- A linear equivalence `E × h.complement ≃L[𝕜] E''` which belongs to the data of an immersion `f`
at `x`: the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
noncomputable def equiv (h : IsImmersionAt2 I J n f x) : (E × h.complement) ≃L[𝕜] E'' := by
  let e := h.isImmersionAt_complement
  rw [IsImmersionAt_def] at e
  exact Classical.choose <| e.property

lemma writtenInCharts (h : IsImmersionAt2 I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target := by
  let e := h.isImmersionAt_complement
  rw [IsImmersionAt_def] at e
  exact Classical.choose_spec <| e.property

lemma property (h : IsImmersionAt2 I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp h.complement I J M N) := by
  let e := h.isImmersionAt_complement
  rwa [IsImmersionAt_def] at e

/--
If `f` is an immersion at `x`, it maps its domain chart's target to its codomain chart's target:
`(h.domChart.extend I).target` to `(h.domChart.extend J).target`.

Roig and Domingues' [roigdomingues1992] definition of immersions only asks for this inclusion
between the targets of the local charts: using mathlib's formalisation conventions, that condition
is *slightly* weaker than `source_subset_preimage_source`: the latter implies that
`h.codChart.extend J ∘ f` maps `h.domChart.source` to
`(h.codChart.extend J).target = (h.codChart.extend I) '' h.codChart.source`,
but that does *not* imply `f` maps `h.domChart.source` to `h.codChartSource`;
a priori `f` could map some point `f ∘ h.domChart.extend I x ∉ h.codChart.source` into the target.
Note that this difference only occurs because of our design using junk values;
this is not a mathematically meaningful difference.`

At the same time, this condition is fairly weak: it is implied, for instance, by `f` being
continuous at `x` (see `mk_of_continuousAt`), which is easy to ascertain in practice.
-/
lemma map_target_subset_target (h : IsImmersionAt2 I J n f x) :
    (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target := by
  rw [← h.writtenInCharts.image_eq, Set.image_comp, Set.image_comp,
    PartialEquiv.symm_image_target_eq_source, OpenPartialHomeomorph.extend_source,
    ← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source ⊆ h.codChart.source := by
    simp [h.source_subset_preimage_source]
  grw [this, OpenPartialHomeomorph.extend_source]

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
lemma congr_of_eventuallyEq {x : M} (hf : IsImmersionAt2 I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt2 I J n g x := by
  rw [IsImmersionAt2_def]
  use hf.complement, (by infer_instance), (by infer_instance)
  rw [IsImmersionAt_def]
  exact LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_immersionAtProp hf.property hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is an immersion at `x` if and only if `g` is an immersion at `x`. -/
lemma congr_iff {x : M} (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt2 I J n f x ↔ IsImmersionAt2 I J n g x :=
  ⟨fun h ↦ h.congr_of_eventuallyEq hfg, fun h ↦ h.congr_of_eventuallyEq hfg.symm⟩

-- lemma trans_F (h : IsImmersionAt F I J n f x) (e : F ≃L[𝕜] F') : IsImmersionAt F' I J n f x := by
--   rewrite [IsImmersionAt_def]
--   refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
--     h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
--   use ((ContinuousLinearEquiv.refl 𝕜 E).prodCongr e.symm).trans h.equiv
--   apply Set.EqOn.trans h.writtenInCharts
--   intro x hx
--   simp

-- /-- Being an immersion at `x` is stable under replacing `F` by an isomorphic copy. -/
-- lemma congr_F (e : F ≃L[𝕜] F') : IsImmersionAt F I J n f x ↔ IsImmersionAt F' I J n f x :=
--   ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/- The set of points where `IsImmersionAt` holds is open. -/
lemma isOpen_isImmersionAt : IsOpen {x | IsImmersionAt F I J n f x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  -- Suppose `f` is an immersion at `x`: choose slice charts φ near x and ψ near f x s.t.
  -- `f` looks like `u ↦ (u, 0)` in these charts. Then the same charts witness that `f` is an
  -- immersion at any `y ∈ φ.source`.
  simp only [mem_setOf_eq, IsImmersionAt_def] at hx
  refine ⟨hx.domChart.source, ?_, hx.domChart.open_source, hx.mem_domChart_source⟩
  intro x' hx'
  rw [mem_setOf_eq, IsImmersionAt_def]
  exact ⟨hx.domChart, hx.codChart, hx', hx.source_subset_preimage_source hx',
    hx.domChart_mem_maximalAtlas, hx.codChart_mem_maximalAtlas, hx.source_subset_preimage_source,
    hx.property⟩

end IsImmersionAt2

variable (I J n) in
/-- `f : M → N` is a `C^n` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

In other words, `f` is an immersion at each `x ∈ M`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`.
-/
def IsImmersion (f : M → N) : Prop := ∀ x, IsImmersionAt2 I J n f x

namespace IsImmersion

variable {f g : M → N}

/-- If `f` is an immersion, it is an immersion at each point. -/
lemma isImmersionAt (h : IsImmersion I J n f) (x : M) : IsImmersionAt2 I J n f x := h x

/-- If `f = g` and `f` is an immersion, so is `g`. -/
theorem congr (h : IsImmersion I J n f) (heq : f = g) : IsImmersion I J n g :=
  heq ▸ h

end IsImmersion

end Manifold

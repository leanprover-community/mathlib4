/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.LocalSourceTargetProperty

/-! # Smooth immersions and embeddings

In this file, we define `C^k` immersions and embeddings between `C^k` manifolds.
The correct definition in the infinite-dimensional setting differs from the standard
finite-dimensional definition (concerning the `mfderiv` being injective): future pull requests will
prove that our definition implies the latter, and that both are equivalent for finite-dimensional
manifolds.

This definition can be conveniently formulated in terms of local properties: `f` is an immersion at
`x` iff there exist suitable charts near `x` and `f x` such that `f` has a nice form w.r.t. these
charts. Most results below can be deduced from more abstract results about such local properties.
This shortens the overall argument, as the definition of submersions has the same general form.

## Main definitions
* `IsImmersionAt F I I' n f x` means a map `f : M → M'` between `C^n` manifolds `M` and `M'`
  is an immersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`, w.r.t. some equivalence
  `E' ≃L[𝕜] E × F`. We do not demand that `f` be differentiable (this follows from this definition).
* `IsImmersion F I I' n f` means `f: M → M'` is an immersion at every point `x : M`.

## Main results
* `IsImmersionAt.congr_of_eventuallyEq`: being an immersion is a local property.
  If `f` and `g` agree near `x` and `f` is an immersion at `x`, so is `g`

## TODO
* `IsImmersionAt.contMDiffAt`: if f is an immersion at `x`, it is `C^n` at `x`.
* `IsImmersion.contMDiff`: if f is an immersion, it is `C^n`.
* `IsImmersionAt.prodMap`: the product of two immersions is an immersion
* If `f` is an immersion at `x`, its differential splits, hence is injective.
* If `f: M → M'` is a map between Banach manifolds, `mfderiv I I' f x` splitting implies `f` is an
  immersion at `x`. (This requires the inverse function theorem.)
* `IsImmersionAt.comp`: if `f: M → M'` and `g: M' → N` are maps between Banach manifolds such that
  `f` is an immersion at `x : M` and `g` is an immersion at `f x`, then `g ∘ f` is an immersion
  at `x`.
* `IsImmersion.comp`: the composition of immersions (between Banach manifolds) is an immersion
* If `f: M → M'` is a map between finite-dimensional manifolds, `mfderiv I I' f x` being injective
  implies `f` is an immersion at `x`.
* define smooth embeddings, and deduce analogous results for these

## References

* [Juan Margalef-Roig and Enrique Outerelo Dominguez, *Differential topology*][roigdomingues2012]

-/

open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}

-- XXX: should the next three definitions be a class instead?
-- Are these slice charts canonical enough that we want the typeclass system to kick in?

variable (F I I' M M') in
/-- The local property of being an immersion at `x` -/
def ImmersionAtProp :
    ((M → M') → PartialHomeomorph M H → PartialHomeomorph M' H' → Prop) :=
  fun f domChart codChart ↦ ∃ equiv : (E × F) ≃L[𝕜] E',
    EqOn ((codChart.extend I') ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace H' M'] in
/-- Being an immersion at `x` is a "nice" local property. -/
lemma ImmersionAtPropIsNice : IsLocalSourceTargetProperty (ImmersionAtProp F I I' M M') where
  mono_source {f φ ψ s} hs hf := by
    have {a b c : Set E} : a ∩ (b ∩ c) ⊆ b := by intro; aesop
    obtain ⟨equiv, hf⟩ := hf
    use equiv
    exact hf.mono (by simpa using this)
  congr {f g φ ψ s} hfg hs hφ hf := by
    obtain ⟨equiv, hf⟩ := hf
    use equiv
    apply EqOn.trans ?_ (hf.mono (by simp))
    intro x hx
    set Φ := φ.extend I
    have aux : Φ.source ⊆ s := by simpa [Φ]
    have : (f ∘ Φ.symm) x = (g ∘ Φ.symm) x := hfg <| aux (PartialEquiv.map_target _ hx)
    rw [Function.comp_apply, ← this]
    simp [Φ]

variable (F I I' n) in
/-- `f : M → N` is a `C^k` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.
-/
def IsImmersionAt (f : M → M') (x : M) : Prop :=
  LiftSourceTargetPropertyAt I I' n f x (ImmersionAtProp F I I' M M')

namespace IsImmersionAt

variable {f g : M → M'} {x : M}

lemma mk_of_charts (equiv : (E × F) ≃L[𝕜] E') (domChart : PartialHomeomorph M H)
    (codChart : PartialHomeomorph M' H')
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas I' n M')
    (hsource : f '' domChart.source ⊆ codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend I') ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt F I I' n f x := by
  use domChart, codChart
  exact ⟨hx, hfx, hdomChart, hcodChart, hsource, equiv, hwrittenInExtend⟩

/-- `f : M → N` is a `C^k` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
lemma mk_of_continuousAt {f : M → M'} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E')
    (domChart : PartialHomeomorph M H) (codChart : PartialHomeomorph M' H')
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas I' n M')
    (hwrittenInExtend : EqOn ((codChart.extend I') ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt F I I' n f x :=
  LiftSourceTargetPropertyAt.mk_of_continuousAt hf ImmersionAtPropIsNice _ _ hx hfx hdomChart
    hcodChart ⟨equiv, hwrittenInExtend⟩

/-- A choice of chart on the domain `M` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
noncomputable def domChart (h : IsImmersionAt F I I' n f x) : PartialHomeomorph M H :=
  Classical.choose h

/-- A choice of chart on the co-domain `N` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
noncomputable def codChart (h : IsImmersionAt F I I' n f x) : PartialHomeomorph M' H' :=
  Classical.choose (Classical.choose_spec h)

lemma mem_domChart_source (h : IsImmersionAt F I I' n f x) : x ∈ h.domChart.source :=
  (Classical.choose_spec (Classical.choose_spec h)).1

lemma mem_codChart_source (h : IsImmersionAt F I I' n f x) : f x ∈ h.codChart.source :=
  (Classical.choose_spec (Classical.choose_spec h)).2.1

lemma domChart_mem_maximalAtlas (h : IsImmersionAt F I I' n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  (Classical.choose_spec (Classical.choose_spec h)).2.2.1

lemma codChart_mem_maximalAtlas (h : IsImmersionAt F I I' n f x) :
    h.codChart ∈ IsManifold.maximalAtlas I' n M' :=
  (Classical.choose_spec (Classical.choose_spec h)).2.2.2.1

lemma map_source_subset_source (h : IsImmersionAt F I I' n f x) :
    f '' h.domChart.source ⊆ h.codChart.source :=
  (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.1

/-- A linear equivalence `E × F ≃L[𝕜] E'` which belongs to the data of an immersion `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
noncomputable def equiv (h : IsImmersionAt F I I' n f x) : (E × F) ≃L[𝕜] E' :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.2

lemma writtenInCharts (h : IsImmersionAt F I I' n f x) :
    EqOn ((h.codChart.extend I') ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.2

lemma property (h : IsImmersionAt F I I' n f x) :
    LiftSourceTargetPropertyAt I I' n f x (ImmersionAtProp F I I' M M') :=
  ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.map_source_subset_source,
    (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.2⟩

/-- Roig and Domingues [roigdomingues1992] only require this condition on the local charts:
in our setting, this is *slightly* weaker than `map_source_subset_source`: the latter implies
that `h.codChart.extend I' ∘ f` maps `h.domChart.source` to
`(h.codChart.extend I').target = (h.codChart.extend I) '' h.codChart.source`,
but that does *not* imply `f` maps `h.domChart.source` to `h.codChartSource`;
a priori `f` could map some point `f ∘ h.domChart.extend I x ∉ h.codChart.source` into the target.
Note that this difference only occurs because of our design using junk values;
this is not a mathematically meaningful difference.`

At the same time, this condition is fairly weak: it is implied, for instance, by `f` being
continuous at `x` (see `mk_of_continuousAt`), which is easy to acertain in practice.
-/
-- TODO: can this proof be golfed further?
lemma map_target_subset_target (h : IsImmersionAt F I I' n f x) :
    (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).target ⊆ (h.codChart.extend I').target := by
  have : (h.domChart.extend I).target = (h.domChart.extend I) '' (h.domChart.extend I).source := by
    rw [PartialEquiv.image_source_eq_target]
  rw [this, PartialHomeomorph.extend_source]
  set Ψ := h.codChart.extend I'
  set Φ := h.domChart.extend I
  suffices (Ψ ∘ f ∘ Φ.symm) '' (Φ '' h.domChart.source) ⊆ Ψ.target by
    have aux : h.domChart.source = Φ.source := h.domChart.extend_source.symm
    rw [aux, PartialEquiv.image_source_eq_target] at this ⊢
    rwa [h.writtenInCharts.image_eq] at this
  calc
   _ = (Ψ ∘ f ∘ ↑Φ.symm ∘ Φ) '' h.domChart.source := by simp [← image_comp]
   _ = (Ψ ∘ f) '' ((Φ.symm ∘ Φ) '' h.domChart.source) := by simp [← image_comp]
   _ = (Ψ ∘ f) '' h.domChart.source := by rw [h.domChart.extend_left_inv' fun ⦃a⦄ a ↦ a]
   _ = Ψ '' (f '' h.domChart.source) := by rw [image_comp]
   _ ⊆ Ψ '' h.codChart.source := by gcongr; exact h.map_source_subset_source
   _ = Ψ '' Ψ.source := by rw [PartialHomeomorph.extend_source]
   _ ⊆ _ := Ψ.map_source''

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
lemma congr_of_eventuallyEq {x : M} (h : IsImmersionAt F I I' n f x) (h' : f =ᶠ[nhds x] g) :
    IsImmersionAt F I I' n g x :=
  LiftSourceTargetPropertyAt.congr_of_eventuallyEq ImmersionAtPropIsNice h.property h'

end IsImmersionAt

variable (F I I' n) in
/-- `f : M → N` is a `C^k` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

In other words, `f` is an immersion at each `x ∈ M`.
-/
def IsImmersion (f : M → M') : Prop := ∀ x, IsImmersionAt F I I' n f x

namespace IsImmersion

variable {f g : M → M'}

/-- If `f` is an immersion, it is an immersion at each point. -/
lemma isImmersionAt (h : IsImmersion F I I' n f) (x : M) : IsImmersionAt F I I' n f x := h x

/-- If `f = g` and `f` is an immersion, so is `g`. -/
theorem congr (h : IsImmersion F I I' n f) (heq : f = g) : IsImmersion F I I' n g :=
  heq ▸ h

end IsImmersion

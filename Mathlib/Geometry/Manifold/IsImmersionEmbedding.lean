/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

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
* `LocalSourceTargetPropertyAt` captures a local property of the above form: for each `f: M → N`,
  `x : M` and charts `φ` of `M` around `x` and `ψ` of `N` around `f x`, the local property is either
  safisfied or not. We ask that the property be stable under restriction of `φ` and local near `x`.
* `LiftSourceTargetPropertyAt f x P`, where `P` is a `LocalSourceTargetPropertyAt`,
   defines a local property of functions of the above shape:
  `f` has this property at `x` if there exist charts `φ` and `ψ` such that `P f φ ψ` holds.

* `IsImmersionAt F I I' n f x` means a map `f : M → M'` between `C^n` manifolds `M` and `M'`
  is an immersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`, w.r.t. some equivalence
  `E' ≃L[𝕜] E × F`. We do not demand that `f` be differentiable (this follows from this definition).
* `IsImmersion F I I' n f` means `f: M → M'` is an immersion at every point `x : M`.

## Main results
* `IsImmersionAt.congr_of_eventuallyEq`: being an immersion is a local property.
  If `f` and `g` agree near `x` and `f` is an immersion at `x`, so is `g`
* `IsImmersionAt.prodMap`: the product of two immersions at `x` is an immersion
* `IsImmersion.prodMap`: the product of two immersions is an immersion

## TODO
* `IsImmersionAt.contMDiffAt`: if f is an immersion at `x`, it is `C^n` at `x`.
* `IsImmersion.contMDiff`: if f is an immersion, it is `C^n`.
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

/-! Local properties which require a particular choice of both the source and target chart -/
section LocalProperties

/-- Structure recording good behaviour of a property of functions `M → M'` w.r.t. to choices
of a chart on both `M` and `M'`. Currently, good behaviour means being stable under restriction
of the domain chart, and locality in the target. (This list might be extended in the future.)

Motivating examples are immersions and submersions of smooth manifolds. -/
structure IsLocalSourceTargetProperty
    (P : (M → M') → PartialHomeomorph M H → PartialHomeomorph M' H' → Prop) : Prop where
  mono_source : ∀ f : M → M', ∀ φ : PartialHomeomorph M H, ∀ ψ : PartialHomeomorph M' H',
    ∀ s : Set M, IsOpen s → P f φ ψ → P f (φ.restr s) ψ
  congr : ∀ f g : M → M', ∀ φ : PartialHomeomorph M H, ∀ ψ : PartialHomeomorph M' H',
    ∀ s : Set M, IsOpen s → EqOn f g s → P f (φ.restr s) ψ → P g (φ.restr s) ψ

variable (I I' n) in
/-- A property of smooth functions `M → M'` which is local at both the source and target:
a property `P` is local at `x` iff there exist charts `φ` and `ψ` of `M` and `N` around
`x` and `f x`, respectively, such that `f` satisfies the property w.r.t. `φ` and `ψ`.

The motivating example are smooth immersions and submersions: the corresponding condition is that
`f` look like the inclusion `u ↦ (u, 0)` (resp. a projection `(u, v) ↦ u`)
in the charts `φ` and `ψ`.
-/
def LiftSourceTargetPropertyAt (f : M → M') (x : M)
    (P : (M → M') → PartialHomeomorph M H → PartialHomeomorph M' H' → Prop) : Prop :=
  ∃ domChart : PartialHomeomorph M H, ∃ codChart : PartialHomeomorph M' H',
    x ∈ domChart.source ∧ f x ∈ codChart.source ∧
    domChart ∈ IsManifold.maximalAtlas I n M ∧
    codChart ∈ IsManifold.maximalAtlas I' n M' ∧
    f '' domChart.source ⊆ codChart.source ∧
    P f domChart codChart

namespace LiftSourceTargetPropertyAt

variable {f g : M → M'} {x : M}
  {P : (M → M') → PartialHomeomorph M H → PartialHomeomorph M' H' → Prop}

/-- A choice of chart on the domain `M` of a local property of `f` at `x`:
w.r.t. this chart and `h.codChart`, `f` has the local property `P` at `x`.
The particular chart is arbitrary, but this choice matches the witness given by `h.codChart`. -/
noncomputable def domChart (h : LiftSourceTargetPropertyAt I I' n f x P) :
    PartialHomeomorph M H :=
  Classical.choose h

/-- A choice of chart on the co-domain `N` of a local property of `f` at `x`:
w.r.t. this chart and `h.domChart`, `f` has the local property `P` at `x`
The particular chart is arbitrary, but this choice matches the witness given by `h.domChart`. -/
noncomputable def codChart (h : LiftSourceTargetPropertyAt I I' n f x P) :
    PartialHomeomorph M' H' :=
  Classical.choose (Classical.choose_spec h)

lemma mem_domChart_source (h : LiftSourceTargetPropertyAt I I' n f x P) :
    x ∈ h.domChart.source :=
  (Classical.choose_spec (Classical.choose_spec h)).1

lemma mem_codChart_source (h : LiftSourceTargetPropertyAt I I' n f x P) :
    f x ∈ h.codChart.source :=
  (Classical.choose_spec (Classical.choose_spec h)).2.1

lemma domChart_mem_maximalAtlas (h : LiftSourceTargetPropertyAt I I' n f x P) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  (Classical.choose_spec (Classical.choose_spec h)).2.2.1

lemma codChart_mem_maximalAtlas (h : LiftSourceTargetPropertyAt I I' n f x P) :
    h.codChart ∈ IsManifold.maximalAtlas I' n M' :=
  (Classical.choose_spec (Classical.choose_spec h)).2.2.2.1

lemma map_source_subset_source (h : LiftSourceTargetPropertyAt I I' n f x P) :
    f '' h.domChart.source ⊆ h.codChart.source :=
  (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.1

lemma property (h : LiftSourceTargetPropertyAt I I' n f x P) : P f h.domChart h.codChart :=
  (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.2

/-- If `P` is monotone w.r.t. restricting `domChart`, then it suffices to prove continuity of `f`
at `x` (instead of a relation between the chart's sources). -/
lemma mk_of_continuousAt (hf : ContinuousAt f x)
    (hP : IsLocalSourceTargetProperty P)
    (domChart : PartialHomeomorph M H) (codChart : PartialHomeomorph M' H')
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas I' n M')
    (hfP : P f domChart codChart) : LiftSourceTargetPropertyAt I I' n f x P := by
  obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp <|
    hf.preimage_mem_nhds (codChart.open_source.mem_nhds hfx)
  have : f '' (domChart.restr s).source ⊆ codChart.source := by
    refine Subset.trans ?_ (image_subset_iff.mpr hs)
    gcongr
    rw [domChart.restr_source' _ hsopen]
    exact inter_subset_right
  have hmono : ((domChart.restr s).extend I).target ⊆ (domChart.extend I).target := by
    have {a b c : Set E} : a ∩ (b ∩ c) ⊆ b := by intro; aesop
    simpa using this
  exact ⟨domChart.restr s, codChart,
    by rw [domChart.restr_source, interior_eq_iff_isOpen.mpr hsopen]; exact mem_inter hx hxs, hfx,
    restr_mem_maximalAtlas (G := contDiffGroupoid n I) hdomChart hsopen, hcodChart, this,
    hP.mono_source _ _ _ _ hsopen hfP⟩

/-- If `P` is monotone w.r.t. restricting `domChart` and closed under congruence,
if `f` has property `P` at `x` and `f` and `g` are eventually equal near `x`,
then `g` has property `P` at `x`. -/
lemma congr_of_eventuallyEq (hP : IsLocalSourceTargetProperty P)
    (hf : LiftSourceTargetPropertyAt I I' n f x P)
    (h' : f =ᶠ[nhds x] g) : LiftSourceTargetPropertyAt I I' n g x P := by
  obtain ⟨s', hxs', hfg⟩ := h'.exists_mem
  obtain ⟨s, hss', hs, hxs⟩ := mem_nhds_iff.mp hxs'
  refine ⟨hf.domChart.restr s, hf.codChart, ?_, ?_, ?_, hf.codChart_mem_maximalAtlas, ?_, ?_⟩
  · simpa using ⟨mem_domChart_source hf, by rwa [interior_eq_iff_isOpen.mpr hs]⟩
  · exact hfg (mem_of_mem_nhds hxs') ▸ mem_codChart_source hf
  · exact restr_mem_maximalAtlas _ hf.domChart_mem_maximalAtlas hs
  · trans f '' (hf.domChart.restr s).source
    · have : (hf.domChart.restr s).source ⊆ s' :=
        Subset.trans (by simp [interior_eq_iff_isOpen.mpr hs]) hss'
      exact (hfg.mono this).image_eq.symm.le
    · exact Subset.trans (image_mono (by simp)) hf.map_source_subset_source
  · apply hP.congr _ _ _ _ _ hs (hfg.mono hss')
    exact hP.mono_source _ _ _ _ hs hf.property

end LiftSourceTargetPropertyAt

end LocalProperties

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
  mono_source f φ ψ s hs hf := by
    have {a b c : Set E} : a ∩ (b ∩ c) ⊆ b := by intro; aesop
    obtain ⟨equiv, hf⟩ := hf
    use equiv
    exact hf.mono (by simpa using this)
  congr f g φ ψ s hs hfg hf := by
    obtain ⟨equiv, hf⟩ := hf
    use equiv
    apply EqOn.trans ?_ (hf.mono (by simp))
    intro x hx
    set Φ := (φ.restr s).extend I
    have aux : Φ.source ⊆ s := by
      simpa only [Φ, PartialHomeomorph.extend_source, PartialHomeomorph.restr_source,
        interior_eq_iff_isOpen.mpr hs] using inter_subset_right
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

section

-- Can grind prove the next two lemmas, after sufficient future tagging?
-- Which of these two proofs is better?
lemma aux1 {α β γ δ : Type*} {f f' : α → γ} {g g' : β → δ} {s : Set α} {t : Set β}
    (h : EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t)) (ht : Set.Nonempty t) :
    EqOn f f' s := by
  choose x0 hx0 using ht
  have a : f = (Prod.fst) ∘ (Prod.map f g) ∘ (·, x0) := by ext x; simp
  have b : f' = Prod.fst ∘ (Prod.map f' g') ∘ (·, x0) := by ext x; simp
  rw [a, b]
  exact (eqOn_comp_right_iff.mpr <| h.mono (image_prodMk_subset_prod_left hx0)).comp_left

lemma aux2 {α β γ δ : Type*} {f f' : α → γ} {g g' : β → δ} {s : Set α} {t : Set β}
    (h : EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t)) (hs : Set.Nonempty s) :
    EqOn g g' t := by
  choose xs hxs using hs
  intro x hx
  have h' := h <| mk_mem_prod hxs hx
  simp at h'
  exact h'.2

-- TODO: move to Data.Set.Operations
lemma Set.EqOn.prodMap {α β γ δ : Type*}
    {f f' : α → γ} {g g' : β → δ} {s : Set α} {t : Set β}
    (hf : EqOn f f' s) (hg : EqOn g g' t) : EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t) := by
  rintro ⟨x, x'⟩ ⟨hx, hx'⟩
  simp [hf hx, hg hx']

end

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
lemma mk_of_continuousAt (f : M → M') (x : M) (hf : ContinuousAt f x)
    (equiv : (E × F) ≃L[𝕜] E')
    (domChart : PartialHomeomorph M H)
    (codChart : PartialHomeomorph M' H')
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

lemma aux {α β γ δ : Type*} {f f' : α → γ} {g g' : β → δ}
    {s : Set α} {t : Set β} (hs : Set.Nonempty s) (ht : Set.Nonempty t) :
    EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t) ↔ EqOn f f' s ∧ EqOn g g' t :=
  --⟨fun h ↦ aux1 h hs ht, fun ⟨h, h'⟩ ↦ aux2 h h'⟩
  ⟨fun h ↦ ⟨aux1 h ht, aux2 h hs⟩, fun ⟨h, h'⟩ ↦ h.prodMap h'⟩

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (h : IsImmersionAt F I J n f x) (h' : IsImmersionAt F' I' J' n g x') :
    IsImmersionAt (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  sorry
  /- use (ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' F F').trans (h.equiv.prodCongr h'.equiv)
  use h.domChart.prod h'.domChart, h.codChart.prod h'.codChart
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h.mem_domChart_source, h'.mem_domChart_source]
  · simp [mem_codChart_source h, mem_codChart_source h']
  · exact IsManifold.mem_maximalAtlas_prod
      (domChart_mem_maximalAtlas h) (domChart_mem_maximalAtlas h')
  · apply IsManifold.mem_maximalAtlas_prod
      (codChart_mem_maximalAtlas h) (codChart_mem_maximalAtlas h')
  · rw [PartialHomeomorph.prod_toPartialEquiv, PartialEquiv.prod_source, prodMap_image_prod]
    exact prod_mono (map_source_subset_source h) (map_source_subset_source h')
  · rw [h.domChart.extend_prod h'.domChart, h.codChart.extend_prod, PartialEquiv.prod_target]
    set C := ((h.codChart.extend J).prod (h'.codChart.extend J')) ∘
      Prod.map f g ∘ ((h.domChart.extend I).prod (h'.domChart.extend I')).symm
    have hC : C = Prod.map ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm)
        ((h'.codChart.extend J') ∘ g ∘ (h'.domChart.extend I').symm) := by
      ext x <;> simp [C]
    set Φ := (((ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' F F').trans
      (h.equiv.prodCongr h'.equiv)) ∘ (·, 0))
    have hΦ: Φ = Prod.map (h.equiv ∘ (·, 0)) (h'.equiv ∘ (·, 0)) := by ext x <;> simp [Φ]
    rw [hC, hΦ]
    exact aux2 (writtenInCharts h) (writtenInCharts h')
    exact (writtenInCharts h).prodMap (writtenInCharts h') -/

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

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (h : IsImmersion F I J n f) (h' : IsImmersion F' I' J' n g) :
    IsImmersion (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun ⟨x, x'⟩ ↦ (h x).prodMap (h' x')

end IsImmersion

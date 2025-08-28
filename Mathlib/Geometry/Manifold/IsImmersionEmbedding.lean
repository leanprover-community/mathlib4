/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Smooth immersions and embeddings

In this file, we define `C^k` immersions and embeddings between `C^k` manifolds.
The correct definition in the infinite-dimensional setting differs from the standard
finite-dimensional definition (concerning the `mfderiv` being injective): future pull requests will
prove that our definition implies the latter, and that both are equivalent for finite-dimensional
manifolds.

## Main definitions
* `IsImmersionAt F I I' n f x` means a map `f : M → M'` between `C^n` manifolds `M` and `M'`
  is an immersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`, w.r.t. some equivalence
  `E' ≃L[𝕜] E × F`. We do not demand that `f` be differentiable (this follows from this definition).
* `IsImmersion F I I' n f` means `f: M → M'` is an immersion at every point `x : M`.

## Main results
* `IsImmersionAt.congr_of_eventuallyEq`: being an immersion is a local property.
  If `f` and `g` agree near `x` and `f` is an immersion at `x`, so is `g`
* `IsImmersionAt.contMDiffAt`: if f is an immersion at `x`, it is `C^n` at `x`.
* `IsImmersion.contMDiff`: if f is an immersion, it is `C^n`.
* `IsImmersionAt.prodMap`: the product of two immersions at `x` is an immersion
* `IsImmersion.prodMap`: the product of two immersions is an immersion
* `IsImmersionAt.exists_nbhd_restr_isEmbedding`: if `f` is immersion at `x`,
  there is a neighbourhood `u` of `f` such that `f` restricted to `u` is an embedding

## TODO
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

-- XXX: does NontriviallyNormedField also work? Splits seems to require more...
variable {𝕜 : Type*} [RCLike 𝕜]
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

variable (F I I' n) in
/-- `f : M → N` is a `C^k` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.
-/
def IsImmersionAt (f : M → M') (x : M) : Prop :=
  ∃ equiv : (E × F) ≃L[𝕜] E',
  ∃ domChart : PartialHomeomorph M H, ∃ codChart : PartialHomeomorph M' H',
    x ∈ domChart.source ∧ f x ∈ codChart.source ∧
    domChart ∈ IsManifold.maximalAtlas I n M ∧
    codChart ∈ IsManifold.maximalAtlas I' n M' ∧
    f '' domChart.source ⊆ codChart.source ∧
    EqOn ((codChart.extend I') ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

namespace IsImmersionAt

variable {f g : M → M'} {x : M}

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
      (domChart.extend I).target) : IsImmersionAt F I I' n f x := by
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
  exact ⟨equiv, domChart.restr s, codChart,
    by rw [domChart.restr_source, interior_eq_iff_isOpen.mpr hsopen]; exact mem_inter hx hxs, hfx,
    restr_mem_maximalAtlas (G := contDiffGroupoid n I) hdomChart hsopen, hcodChart, this,
    hwrittenInExtend.mono hmono⟩

/-- A linear equivalence `E × F ≃L[𝕜] E'` which belongs to the data of an immersion `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
noncomputable def equiv (h : IsImmersionAt F I I' n f x) : (E × F) ≃L[𝕜] E' :=
  Classical.choose h

/-- A choice of chart on the domain `M` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
noncomputable def domChart (h : IsImmersionAt F I I' n f x) : PartialHomeomorph M H :=
  Classical.choose (Classical.choose_spec h)

/-- A choice of chart on the co-domain `N` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
noncomputable def codChart (h : IsImmersionAt F I I' n f x) : PartialHomeomorph M' H' :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec h))

lemma mem_domChart_source (h : IsImmersionAt F I I' n f x) : x ∈ h.domChart.source :=
  (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec h)))).1

lemma mem_codChart_source (h : IsImmersionAt F I I' n f x) : f x ∈ h.codChart.source :=
  (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec h)))).2.1

lemma domChart_mem_maximalAtlas (h : IsImmersionAt F I I' n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec h)))).2.2.1

lemma codChart_mem_maximalAtlas (h : IsImmersionAt F I I' n f x) :
    h.codChart ∈ IsManifold.maximalAtlas I' n M' :=
  (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec h)))).2.2.2.1

lemma map_source_subset_source (h : IsImmersionAt F I I' n f x) :
    f '' h.domChart.source ⊆ h.codChart.source :=
  (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec h)))).2.2.2.2.1

lemma writtenInCharts (h : IsImmersionAt F I I' n f x) :
    EqOn ((h.codChart.extend I') ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target :=
  (Classical.choose_spec ((Classical.choose_spec (Classical.choose_spec h)))).2.2.2.2.2

/-- This result is a "dual version" of `h.writtenInCharts`, which applies to `f` directly. -/
theorem eqOn_domChart_source (h : IsImmersionAt F I I' n f x) :
    letI rhs := (h.codChart.extend I').symm ∘ (h.equiv ∘ fun x ↦ (x, 0)) ∘ (h.domChart.extend I);
    EqOn f rhs h.domChart.source := by
  have : EqOn f (((h.codChart.extend I').symm ∘
      ((h.codChart.extend I') ∘ f ∘ (h.domChart.extend I).symm) ∘ (h.domChart.extend I)))
      h.domChart.source := by
    intro x hx
    symm
    trans f ((h.domChart.extend I).symm ((h.domChart.extend I) x))
    · simp only [PartialHomeomorph.extend, PartialEquiv.coe_trans_symm,
        PartialHomeomorph.coe_coe_symm, ModelWithCorners.toPartialEquiv_coe_symm,
        PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe,
        PartialHomeomorph.toFun_eq_coe, comp_apply, ModelWithCorners.left_inv]
      refine h.codChart.left_inv ?_
      apply h.map_source_subset_source
      apply mem_image_of_mem
      rwa [h.domChart.left_inv hx]
    · simp [h.domChart.left_inv hx]
  apply this.trans
  apply EqOn.comp_left
  apply EqOn.comp_right h.writtenInCharts
  rw [h.domChart.extend_target_eq_image_source]
  exact mapsTo_image _ h.domChart.source

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
-- TODO: golf this proof!
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
   _ = (Ψ ∘ f ∘ ↑Φ.symm ∘ Φ) '' h.domChart.source := by rw [← image_comp]; congr
   _ = (Ψ ∘ f) '' ((Φ.symm ∘ Φ) '' h.domChart.source) := by simp [← image_comp]
   _ = (Ψ ∘ f) '' h.domChart.source := by rw [h.domChart.extend_left_inv' fun ⦃a⦄ a ↦ a]
   _ = Ψ '' (f '' h.domChart.source) := by rw [image_comp]
   _ ⊆ Ψ '' h.codChart.source := by gcongr; exact h.map_source_subset_source
   _ = Ψ '' Ψ.source := by rw [PartialHomeomorph.extend_source]
   _ ⊆ _ := Ψ.map_source''

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
lemma congr_of_eventuallyEq {x : M} (h : IsImmersionAt F I I' n f x) (h' : f =ᶠ[nhds x] g) :
    IsImmersionAt F I I' n g x := by
  obtain ⟨s', hxs', hfg⟩ := h'.exists_mem
  obtain ⟨s, hss', hs, hxs⟩ := mem_nhds_iff.mp hxs'
  refine ⟨h.equiv, h.domChart.restr s, h.codChart, ?_, ?_, ?_, h.codChart_mem_maximalAtlas, ?_, ?_⟩
  · simpa using ⟨mem_domChart_source h, by rwa [interior_eq_iff_isOpen.mpr hs]⟩
  · exact hfg (mem_of_mem_nhds hxs') ▸ mem_codChart_source h
  · exact restr_mem_maximalAtlas _ h.domChart_mem_maximalAtlas hs
  · have := h.map_source_subset_source
    trans f '' (h.domChart.restr s).source
    · have : (h.domChart.restr s).source ⊆ s' :=
        Subset.trans (by simp [interior_eq_iff_isOpen.mpr hs]) hss'
      exact (hfg.mono this).image_eq.symm.le
    · exact Subset.trans (image_mono (by simp)) this
  · have : f '' (h.domChart.restr s).source ⊆ h.codChart.source := by
      refine Subset.trans (image_mono ?_) h.map_source_subset_source
      rw [h.domChart.restr_source' _ hs]
      exact inter_subset_left
    have hmono : ((h.domChart.restr s).extend I).target ⊆ (h.domChart.extend I).target := by
      have {a b c : Set E} : a ∩ (b ∩ c) ⊆ b := by intro; aesop
      simpa using this
    apply EqOn.trans ?_ (h.writtenInCharts.mono hmono)
    intro x hx
    set Φ := (h.domChart.restr s).extend I
    have aux : Φ.source ⊆ s := by
      simpa only [Φ, PartialHomeomorph.extend_source, PartialHomeomorph.restr_source,
        interior_eq_iff_isOpen.mpr hs] using inter_subset_right
    have : (f ∘ Φ.symm) x = (g ∘ Φ.symm) x := hfg <| hss' <| aux (PartialEquiv.map_target _ hx)
    rw [Function.comp_apply, ← this]
    simp [Φ]

/-- If `f` an immersion at `x`, then `x` has an open neighbourhood `s` such that the restriction
of `f` to `s` is an embedding. -/
lemma exists_nbhd_restr_isEmbedding (h : IsImmersionAt F I I' n f x) :
    ∃ s : Set M, IsOpen s ∧ s ∈ 𝓝 x ∧ Topology.IsEmbedding (s.restrict f) := by
  have := h.writtenInCharts
  use h.domChart.source
  refine ⟨h.domChart.open_source, h.domChart.open_source.mem_nhds h.mem_domChart_source, ?_⟩
  have hj : Topology.IsEmbedding (h.equiv ∘ fun x ↦ (x, 0)) :=
    h.equiv.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft 0)
  letI rhs := (h.codChart.extend I').symm ∘ (h.equiv ∘ fun x ↦ (x, 0)) ∘ (h.domChart.extend I)
  have : h.domChart.source.restrict f = h.domChart.source.restrict rhs := by
    ext ⟨x, hx⟩
    simpa using h.eqOn_domChart_source hx
  have hrhs : Topology.IsEmbedding (h.domChart.source.restrict rhs) := by
    -- Local notation for readability.
    set s := h.domChart.source
    set φ := h.domChart.extend I
    set ψ := h.codChart.extend I'
    /- We write s.restrict rhs as the composition of three embeddings:
    - ψ restricted to its target (TODO! is this true?)
    - (h.equiv ∘ fun x ↦ (x, 0)) (which is an embedding, see above)
    - φ restricted to its source. -/
    let floc := (h.equiv ∘ fun x ↦ (x, (0 : F)))
    have aux (x : s): (floc ∘ (s.restrict φ)) x ∈ ψ.target := by
      obtain ⟨x, hx⟩ := x
      -- XXX: replace by the right rewrite!
      change (⇑h.equiv ∘ fun x ↦ (x, 0)) ((s.restrict φ) ⟨x, hx⟩) ∈ ψ.target
      have : (s.restrict φ) ⟨x, hx⟩ ∈ φ.target := by
        simp only [restrict_apply]
        apply (h.domChart.extend I).map_source
        rwa [PartialHomeomorph.extend_source]
      rw [← h.writtenInCharts this]
      rw [h.codChart.extend_target_eq_image_source]
      apply mem_image_of_mem
      apply h.map_source_subset_source
      apply mem_image_of_mem
      simp only [restrict_apply]
      simp_rw [← h.domChart.extend_source (I := I)]
      exact (h.domChart.extend I).map_target this
    let bs : s → (h.codChart.extend I').target :=
      Set.codRestrict (floc ∘ (s.restrict φ)) (h.codChart.extend I').target aux
    have : s.restrict rhs = (ψ.target.restrict ψ.symm) ∘ bs := by
      ext ⟨x, hx⟩
      simp [bs, rhs, comp_apply, floc, φ, ψ]
    rw [this]
    refine h.codChart.isEmbedding_extend_symm_restrict.comp  ?_
    -- TODO: make fun_prop do this!
    exact (hj.comp h.domChart.isEmbedding_extend_restrict).codRestrict
      (h.codChart.extend I').target aux
  rw [this]
  exact hrhs

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
lemma _root_.Set.EqOn.prodMap {α β γ δ : Type*}
    {f f' : α → γ} {g g' : β → δ} {s : Set α} {t : Set β}
    (hf : EqOn f f' s) (hg : EqOn g g' t) : EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t) := by
  rintro ⟨x, x'⟩ ⟨hx, hx'⟩
  simp [hf hx, hg hx']

lemma aux {α β γ δ : Type*} {f f' : α → γ} {g g' : β → δ}
    {s : Set α} {t : Set β} (hs : Set.Nonempty s) (ht : Set.Nonempty t) :
    EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t) ↔ EqOn f f' s ∧ EqOn g g' t :=
  ⟨fun h ↦ ⟨aux1 h ht, aux2 h hs⟩, fun ⟨h, h'⟩ ↦ h.prodMap h'⟩

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (h : IsImmersionAt F I J n f x) (h' : IsImmersionAt F' I' J' n g x') :
    IsImmersionAt (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  use (ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' F F').trans (h.equiv.prodCongr h'.equiv)
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
    exact (writtenInCharts h).prodMap (writtenInCharts h')

/-- This lemma is marked private since `h.domChart` is an arbitrary representative:
`continuousAt` is part of the public API -/
private theorem continuousOn (h : IsImmersionAt F I I' n f x) :
    ContinuousOn f h.domChart.source := by
  have mapsto : MapsTo f h.domChart.source h.codChart.source :=
    fun x hx ↦ by apply h.map_source_subset_source; use x
  rw [← h.domChart.continuousOn_writtenInExtend_iff le_rfl mapsto (I' := I') (I := I),
    ← h.domChart.extend_target_eq_image_source]
  have : ContinuousOn (h.equiv ∘ fun x ↦ (x, 0)) (h.domChart.extend I).target := by fun_prop
  exact this.congr h.writtenInCharts

/-- A `C^k` immersion at `x` is continuous at `x`. -/
theorem continuousAt (h : IsImmersionAt F I I' n f x) : ContinuousAt f x :=
  h.continuousOn.continuousAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

variable [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N]

/-- This lemma is marked private since `h.domChart` is an arbitrary representative:
`contMDiffAt` is part of the public API -/
private theorem contMDiffOn (h : IsImmersionAt F I I' n f x) :
    ContMDiffOn I I' n f h.domChart.source := by
  have mapsto : MapsTo f h.domChart.source h.codChart.source :=
    fun x hx ↦ by apply h.map_source_subset_source; use x
  rw [← contMDiffOn_writtenInExtend_iff h.domChart_mem_maximalAtlas
    h.codChart_mem_maximalAtlas le_rfl mapsto,
    ← h.domChart.extend_target_eq_image_source]
  have : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n (h.equiv ∘ fun x ↦ (x, 0)) := by
    have : ContMDiff (𝓘(𝕜, E × F)) 𝓘(𝕜, E') n h.equiv := by
      rw [contMDiff_iff_contDiff]
      exact h.equiv.contDiff
    apply this.comp
    rw [contMDiff_iff_contDiff, contDiff_prod_iff]
    exact ⟨contDiff_id, contDiff_const (c := (0 : F))⟩
  exact this.contMDiffOn.congr h.writtenInCharts

/-- A `C^k` immersion at `x` is `C^k` at `x`. -/
theorem contMDiffAt (h : IsImmersionAt F I I' n f x) : ContMDiffAt I I' n f x :=
  h.contMDiffOn.contMDiffAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

end IsImmersionAt

lemma ContinuousAt.of_comp_iff_isEmbedding
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} {x : X} (hf' : Topology.IsEmbedding g) :
    ContinuousAt f x ↔ ContinuousAt (g ∘ f) x := by
  refine Topology.IsInducing.continuousAt_iff hf'.isInducing

lemma Continuous.of_comp_iff_isInducing_restr {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} {x : X} {s : Set Y} (hs : IsOpen s) (hs' : s ∈ 𝓝 (f x))
    (hg : Topology.IsInducing (s.restrict g)) :
    ContinuousAt f x ↔ ContinuousAt (g ∘ f) x := by
  have hg' : ContinuousAt (s.restrict g) ⟨f x, mem_of_mem_nhds hs'⟩ := hg.continuous.continuousAt
  have hg' : ContinuousAt g (f x) := by
    have := (Topology.IsEmbedding.subtypeVal (p := s)).isInducing
    have aux : g ∘ (Subtype.val (p := s)) = (s.restrict g) := sorry

    rw [← aux] at hg'

    rw [this.continuousAt_iff] at hg'
    --have := this.comp hg
    sorry
  -- have : ContinuousAt f x := by
  --   have : ContinuousAt (s.restrict g) ⟨f x, mem_of_mem_nhds hs'⟩ := hf'.continuous.continuousAt
  --   rw [ContinuousAt.of_comp_iff_isEmbedding hf']
  --   -- want Continuous.comp_isEmbedding, should be a lemma, right?
  --   sorry
  refine ⟨fun hf ↦ hg'.comp hf, fun h ↦ ?_⟩

  let s' : Set X := f ⁻¹' s
  have hxs' : x ∈ s' := by rw [@mem_preimage]; exact mem_of_mem_nhds hs'
  have hmaps : MapsTo f s' s := by simpa +contextual [s'] using fun ⦃x⦄ a ↦ a
  have : ContinuousAt (s'.restrict (g ∘ f)) ⟨x, hxs'⟩ := h.comp (by fun_prop)
  have : ContinuousAt (hmaps.restrict f) ⟨x, hxs'⟩ := hg.continuousAt_iff.mpr this
  -- subtype-restriction argument
  sorry

#exit

variable {x : M}
--- TODO: are the manifold hypotheses necessary now? think!
/-- A point-wise version of `Topology.IsInducing.nhds_eq_comap` -/
lemma nhds_eq_comap {f : M → N} (hf : ContinuousAt f x)
    {s : Set M} (hs : IsOpen s) (hs' : s ∈ 𝓝 x) (hf' : Topology.IsEmbedding (s.restrict f)) :
    𝓝 x = Filter.comap f (𝓝 (f x)) := by
  symm
  set x' : s := ⟨x, mem_of_mem_nhds hs'⟩
  have aux := hf'.isInducing.nhds_eq_comap (x := x')
  have : f x = (s.restrict f) x' := rfl
  rw [← map_nhds_subtype_coe_eq_nhds (mem_of_mem_nhds hs') hs', aux, ← this]
  rw [restrict_eq, ← Filter.comap_comap]
  set l' := Filter.comap f (𝓝 (f x))
  -- is this true? i is injective, but not surjective...
  -- does following my nose help?
  ext s2
  constructor
  · intro hs
    refine Filter.mem_map.mpr ?_
    exact Filter.preimage_mem_comap hs
  · intro hs
    rw [Filter.mem_map] at hs
    rw [Filter.mem_comap] at hs
    obtain ⟨t, ht, htl⟩ := hs
    -- very unsure if this is good!
    have : t ∩ s ⊆ s2 := by
      rw [← image_subset_iff] at htl

      --rw? at htl
      sorry
    have scifi : t ∩ s ∈ l' := by
      refine Filter.mem_comap.mpr ?_
      use f '' (t ∩ s)
      refine ⟨?_, ?_⟩
      · have : IsOpen t := by sorry -- by further shrinking t
        -- idea: f '' t ∩ s = (s.restrict f) (image of t);
        -- s.restrict f is an open map -> we're good, right?
        -- TROUBLE: we only have an embedding, not an open map...
        sorry
      · have : InjOn f (t ∩ s) := sorry -- something like this should hold. argh!
        sorry
    exact Filter.mem_of_superset (Filter.inter_mem ht sorry) this

  --sorry

  -- have := hf'.isInducing.nhds_eq_comap
  -- have : f x = (s.restrict f) ⟨x, mem_of_mem_nhds hs'⟩ := rfl
  -- rw [this]
  -- rw [hf'.isInducing.nhds_eq_comap]
  -- apply le_antisymm
  -- · exact Filter.map_le_iff_le_comap.mp hf
  -- · rw [le_nhds_iff]
  --   intro s' hxs' hs'
  --   rw [Filter.mem_comap]
  --   let ssmall : Set s := sorry -- s' as subset of s...
  --   have : IsOpen ssmall := sorry -- hopefully easy
  --   use (s.restrict f) '' ssmall--(s ∩ s')
  --   constructor
  --   · -- TODO: this move is too strong, but we don't need all of it!
  --     --apply IsOpen.mem_nhds
  --     --sorry--have : IsOpenMap (s.restrict f) := by apply?
  --     --apply mem_image_of_mem
  --     --refine (mem_image (s.restrict f) ssmall (f x)).mpr ?_
  --     sorry -- use x cast to s...
  --   rw [preimage_subset_iff]
  --   rintro x ⟨x', hx', hx'x⟩
  --   sorry

-- these seem superfluous now: [IsManifold J n N] [IsManifold J' n N']
lemma continuousAt_iff_comp_isImmersionAt
    {f : M → N} {φ : N → N'} (h : IsImmersionAt F J J' n φ (f x)) :
    ContinuousAt f x ↔ ContinuousAt (φ ∘ f) x := by
  choose t ht hxt htφ using h.exists_nbhd_restr_isEmbedding
  simp_rw [ContinuousAt, nhds_eq_comap h.continuousAt ht hxt htφ, Filter.tendsto_comap_iff,
    comp_apply]

-- TODO: add same lemma for immersions and continuity

lemma aux {f : M → N} {φ : N → N'} [IsManifold I n M] [IsManifold J' n N']
    (h : IsImmersionAt F J J' n φ (f x)) (h' : ContMDiffAt I J' n (φ ∘ f) x)
    {t : Set M} (ht : t ⊆ f ⁻¹' h.domChart.source) (hxt : x ∈ t) :
    ContDiffWithinAt 𝕜 n (↑(h.domChart.extend J) ∘ f ∘ ↑((chartAt H x).extend I).symm)
      (((chartAt H x).extend I).symm ⁻¹' t ∩ range I) (((chartAt H x).extend I) x) := by
  set f' := (h.domChart.extend J) ∘ f ∘ ↑((chartAt H x).extend I).symm
  set φ' := (h.codChart.extend J') ∘ φ ∘ (h.domChart.extend J).symm
  set x' := (((chartAt H x).extend I) x)
  set s := (extChartAt I x).symm ⁻¹' t ∩ range I
  have hx' : (((chartAt H x).extend I) x) ∈ s := by
    refine ⟨?_, mem_range_self _⟩
    rw [mem_preimage, ← (extChartAt I x).left_inv (mem_extChartAt_source x)]
    simpa
  -- old code, probably obsolete
  -- set s := ((chartAt H x).extend I).symm ⁻¹' (chartAt H x).source ∩ range I
  -- have hx' : x' ∈ s := by
  --   refine ⟨?_, mem_range_self _⟩
  --   refine mem_preimage.mpr ?_
  --   simp only [x']
  --   -- can or should this be a separate lemma? there is nothing going on here!
  --   rw [← PartialHomeomorph.extend_source (I := I)]
  --   refine PartialEquiv.map_target ((chartAt H x).extend I) ?_
  --   refine PartialEquiv.map_source ((chartAt H x).extend I) ?_
  --   rw [PartialHomeomorph.extend_source]
  --   exact ChartedSpace.mem_chart_source x
  --replace h' : ContMDiffWithinAt I J' n (φ ∘ f) (chartAt H x).source x := h'.contMDiffWithinAt
  replace h' : ContMDiffWithinAt I J' n (φ ∘ f) t x := h'.contMDiffWithinAt
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas x) h.codChart_mem_maximalAtlas (mem_chart_source H x)
    h.mem_codChart_source] at h'
  replace h' := h'.2
  have := h.writtenInCharts
  have h'' : ContDiffWithinAt 𝕜 n (φ' ∘ f') s x' := by
    apply h'.congr_of_mem (fun y hy ↦ ?_) hx'
    simp [φ', f']
    congr
    exact h.domChart.left_inv (ht hy.1)
  set f'' := ((h.equiv ∘ fun x ↦ (x, 0)) ∘ f')
  have h''' : ContDiffWithinAt 𝕜 n f'' s x' := by
    refine h''.congr_of_mem (fun y hy ↦ ?_) hx'
    simp only [f'', φ', f']
    nth_rw 2 [comp_apply]
    rw [h.writtenInCharts]
    congr
    rw [h.domChart.extend_target_eq_image_source]
    exact ⟨(f ∘ ((chartAt H x).extend I).symm) y, ht hy.1, by simp⟩
  -- Compose with a suitable projection to cancel the inclusion.
  have h'''' : ContDiffWithinAt 𝕜 n ((Prod.fst ∘ h.equiv.symm) ∘ f'') s x' := by
    refine ContDiffWithinAt.comp x' ?_ h''' (mapsTo_univ _ _)
    rw [contDiffWithinAt_univ]
    exact contDiffAt_fst.comp _ h.equiv.symm.contDiff.contDiffAt
  exact h''''.congr_of_mem (fun y hy ↦ by simp [f'']) hx'

lemma ContMDiffAt.iff_comp_isImmersionAt
    [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']
    {f : M → N} {φ : N → N'} (h : IsImmersionAt F J J' n φ (f x)) :
    ContMDiffAt I J n f x ↔ ContMDiffAt I J' n (φ ∘ f) x := by
  refine ⟨fun hf ↦ h.contMDiffAt.comp x hf, fun h' ↦ ?_⟩
  -- Since `f` is continuous at `x`, some neighbourhood `t` of `x` is mapped
  -- into `h.domChart.source` under `f`. By restriction, we may assume `t` is open.
  have hf₁ : ContinuousAt f x := ((continuousAt_iff_comp_isImmersionAt h).mpr h'.continuousAt)
  have : h.domChart.source ∈ 𝓝 (f x) := h.domChart.open_source.mem_nhds h.mem_domChart_source
  obtain ⟨t, ht, htopen, hxt⟩ := mem_nhds_iff.mp (hf₁ this)
  suffices ContMDiffWithinAt I J n f t x from this.contMDiffAt <| htopen.mem_nhds hxt
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
    h.domChart_mem_maximalAtlas (mem_chart_source H x) h.mem_domChart_source]
  refine ⟨hf₁.continuousWithinAt, ?_⟩
  exact aux h h' ht hxt

  /- old code, probably obsolete
  rw [contMDiffAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
    h.domChart_mem_maximalAtlas (mem_chart_source H x) h.mem_domChart_source]
  refine ⟨sorry, ?_⟩ -- think! continuity is the warm-up problem!
  let n'chart := h.codChart
  rw [contMDiffAt_iff_of_mem_maximalAtlas (e := chartAt H x) (e' := h.codChart)
    (IsManifold.chart_mem_maximalAtlas x) h.codChart_mem_maximalAtlas (mem_chart_source H x)
    h.mem_codChart_source] at h'
  replace h' := h'.2
  have := h.writtenInCharts
  set f' := (h.domChart.extend J) ∘ f ∘ ↑((chartAt H x).extend I).symm
  set φ' := (h.codChart.extend J') ∘ φ ∘ (h.domChart.extend J).symm
  set x' := (((chartAt H x).extend I) x)
  -- Current WIP code!
  have h'' : ContDiffWithinAt 𝕜 n (φ' ∘ f') (range I) x' := by
    apply h'.congr_of_mem (fun y hy ↦ ?_) (mem_range_self _)
    simp only [φ', f']
    simp
    congr
    refine PartialHomeomorph.left_inv h.domChart ?_
    sorry -- need to think!
  set f'' := ((h.equiv ∘ fun x ↦ (x, 0)) ∘ f')
  have h''' : ContDiffWithinAt 𝕜 n f'' (range I) x' := by
    apply h''.congr_of_mem (fun y hy ↦ ?_) (mem_range_self _)
    simp only [f'']
    nth_rw 2 [comp_apply]
    simp only [φ']
    rw [h.writtenInCharts]
    congr
    -- need to think, is y in the right set?
    simp only [f']
    sorry
  -- Compose with a suitable projection to cancel the inclusion.
  have h'''' : ContDiffWithinAt 𝕜 n (Prod.fst ∘ h.equiv.symm ∘ f'') (range I) x' := by
    sorry -- easy, just composition
  apply h''''.congr_of_mem ?_ (mem_range_self _)
  intro y hy
  simp [f''] -/

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
  fun x ↦ (h x).congr_of_eventuallyEq heq.eventuallyEq

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (h : IsImmersion F I J n f) (h' : IsImmersion F' I' J' n g) :
    IsImmersion (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun ⟨x, x'⟩ ↦ (h x).prodMap (h' x')

variable [IsManifold I n M] [IsManifold I' n M']
/-- A `C^k` immersion is `C^k`. -/
theorem contMDiff (h : IsImmersion F I I' n f) : ContMDiff I I' n f := fun x ↦ (h x).contMDiffAt

end IsImmersion

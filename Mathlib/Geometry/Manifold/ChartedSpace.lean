/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Geometry.Manifold.StructureGroupoid

/-!
# Charted spaces

A smooth manifold is a topological space `M` locally modelled on a Euclidean space (or a Euclidean
half-space for manifolds with boundaries, or an infinite-dimensional vector space for more general
notions of manifolds), i.e., the manifold is covered by open subsets on which there are local
homeomorphisms (the charts) going to a model space `H`, and the changes of charts should be smooth
maps.

In this file, we introduce a general framework describing these notions, where the model space is an
arbitrary topological space. We avoid the word *manifold*, which should be reserved for the
situation where the model space is a (subset of a) vector space, and use the terminology
*charted space* instead.

If the changes of charts satisfy some additional property (for instance if they are smooth), then
`M` inherits additional structure (it makes sense to talk about smooth manifolds). There are
therefore two different ingredients in a charted space:
* the set of charts, which is data
* the fact that changes of charts belong to some group (in fact groupoid), which is additional Prop.

We separate these two parts in the definition: the charted space structure is just the set of
charts, and then the different smoothness requirements (smooth manifold, orientable manifold,
contact manifold, and so on) are additional properties of these charts. These properties are
formalized through the notion of structure groupoid, i.e., a set of open partial homeomorphisms
stable under composition and inverse, to which the change of coordinates should belong.

## Main definitions

* `StructureGroupoid H` : a subset of open partial homeomorphisms of `H` stable under composition,
  inverse and restriction (ex: partial diffeomorphisms).
* `continuousGroupoid H` : the groupoid of all open partial homeomorphisms of `H`.
* `ChartedSpace H M` : charted space structure on `M` modelled on `H`, given by an atlas of
  open partial homeomorphisms from `M` to `H` whose sources cover `M`. This is a type class.
* `HasGroupoid M G` : when `G` is a structure groupoid on `H` and `M` is a charted space
  modelled on `H`, require that all coordinate changes belong to `G`. This is a type class.
* `atlas H M` : when `M` is a charted space modelled on `H`, the atlas of this charted
  space structure, i.e., the set of charts.
* `G.maximalAtlas M` : when `M` is a charted space modelled on `H` and admitting `G` as a
  structure groupoid, one can consider all the open partial homeomorphisms from `M` to `H` such that
  changing coordinate from any chart to them belongs to `G`. This is a larger atlas, called the
  maximal atlas (for the groupoid `G`).
* `Structomorph G M M'` : the type of diffeomorphisms between the charted spaces `M` and `M'` for
  the groupoid `G`. We avoid the word diffeomorphism, keeping it for the smooth category.

As a basic example, we give the instance
`instance chartedSpaceSelf (H : Type*) [TopologicalSpace H] : ChartedSpace H H`
saying that a topological space is a charted space over itself, with the identity as unique chart.
This charted space structure is compatible with any groupoid.

Additional useful definitions:

* `Pregroupoid H` : a subset of partial maps of `H` stable under composition and
  restriction, but not inverse (ex: smooth maps)
* `Pregroupoid.groupoid` : construct a groupoid from a pregroupoid, by requiring that a map and
  its inverse both belong to the pregroupoid (ex: construct diffeos from smooth maps)
* `chartAt H x` is a preferred chart at `x : M` when `M` has a charted space structure modelled on
  `H`.
* `G.compatible he he'` states that, for any two charts `e` and `e'` in the atlas, the composition
  of `e.symm` and `e'` belongs to the groupoid `G` when `M` admits `G` as a structure groupoid.
* `G.compatible_of_mem_maximalAtlas he he'` states that, for any two charts `e` and `e'` in the
  maximal atlas associated to the groupoid `G`, the composition of `e.symm` and `e'` belongs to the
  `G` if `M` admits `G` as a structure groupoid.
* `ChartedSpaceCore.toChartedSpace`: consider a space without a topology, but endowed with a set
  of charts (which are partial equivs) for which the changes of coordinates are partial homeos.
  Then one can construct a topology on the space for which the charts become partial homeos,
  defining a genuine charted space structure.

## Implementation notes

The atlas in a charted space is *not* a maximal atlas in general: the notion of maximality depends
on the groupoid one considers, and changing groupoids changes the maximal atlas. With the current
formalization, it makes sense first to choose the atlas, and then to ask whether this precise atlas
defines a smooth manifold, an orientable manifold, and so on. A consequence is that structomorphisms
between `M` and `M'` do *not* induce a bijection between the atlases of `M` and `M'`: the
definition is only that, read in charts, the structomorphism locally belongs to the groupoid under
consideration. (This is equivalent to inducing a bijection between elements of the maximal atlas).
A consequence is that the invariance under structomorphisms of properties defined in terms of the
atlas is not obvious in general, and could require some work in theory (amounting to the fact
that these properties only depend on the maximal atlas, for instance). In practice, this does not
create any real difficulty.

We use the letter `H` for the model space thinking of the case of manifolds with boundary, where the
model space is a half-space.

Manifolds are sometimes defined as topological spaces with an atlas of local diffeomorphisms, and
sometimes as spaces with an atlas from which a topology is deduced. We use the former approach:
otherwise, there would be an instance from manifolds to topological spaces, which means that any
instance search for topological spaces would try to find manifold structures involving a yet
unknown model space, leading to problems. However, we also introduce the latter approach,
through a structure `ChartedSpaceCore` making it possible to construct a topology out of a set of
partial equivs with compatibility conditions (but we do not register it as an instance).

In the definition of a charted space, the model space is written as an explicit parameter as there
can be several model spaces for a given topological space. For instance, a complex manifold
(modelled over `ℂ^n`) will also be seen sometimes as a real manifold modelled over `ℝ^(2n)`.

## Notation

In the scope `Manifold`, we denote the composition of open partial homeomorphisms with `≫ₕ`, and the
composition of partial equivs with `≫`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Topology

universe u

variable {H : Type u} {H' : Type*} {M : Type*} {M' : Type*} {M'' : Type*}

open Set OpenPartialHomeomorph Manifold

/-! ### Charted spaces -/

/-- A charted space is a topological space endowed with an atlas, i.e., a set of local
homeomorphisms taking values in a model space `H`, called charts, such that the domains of the
charts cover the whole space. We express the covering property by choosing for each `x` a member
`chartAt x` of the atlas containing `x` in its source: in the smooth case, this is convenient to
construct the tangent bundle in an efficient way.
The model space is written as an explicit parameter as there can be several model spaces for a
given topological space. For instance, a complex manifold (modelled over `ℂ^n`) will also be seen
sometimes as a real manifold over `ℝ^(2n)`.
-/
@[ext]
class ChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M] where
  /-- The atlas of charts in the `ChartedSpace`. -/
  protected atlas : Set (OpenPartialHomeomorph M H)
  /-- The preferred chart at each point in the charted space. -/
  protected chartAt : M → OpenPartialHomeomorph M H
  protected mem_chart_source : ∀ x, x ∈ (chartAt x).source
  protected chart_mem_atlas : ∀ x, chartAt x ∈ atlas

/-- The atlas of charts in a `ChartedSpace`. -/
abbrev atlas (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Set (OpenPartialHomeomorph M H) :=
  ChartedSpace.atlas

/-- The preferred chart at a point `x` in a charted space `M`. -/
abbrev chartAt (H : Type*) [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : OpenPartialHomeomorph M H :=
  ChartedSpace.chartAt x

@[simp, mfld_simps]
lemma mem_chart_source (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : x ∈ (chartAt H x).source :=
  ChartedSpace.mem_chart_source x

@[simp, mfld_simps]
lemma chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : chartAt H x ∈ atlas H M :=
  ChartedSpace.chart_mem_atlas x

lemma nonempty_of_chartedSpace {H : Type*} {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : Nonempty H :=
  ⟨chartAt H x x⟩

lemma isEmpty_of_chartedSpace (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [IsEmpty H] : IsEmpty M := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · exact hM
  · exact (IsEmpty.false (chartAt H x x)).elim

section ChartedSpace

section

variable (H) [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

theorem mem_chart_target (x : M) : chartAt H x x ∈ (chartAt H x).target :=
  (chartAt H x).map_source (mem_chart_source _ _)

theorem chart_source_mem_nhds (x : M) : (chartAt H x).source ∈ 𝓝 x :=
  (chartAt H x).open_source.mem_nhds <| mem_chart_source H x

theorem chart_target_mem_nhds (x : M) : (chartAt H x).target ∈ 𝓝 (chartAt H x x) :=
  (chartAt H x).open_target.mem_nhds <| mem_chart_target H x

variable (M) in
@[simp]
theorem iUnion_source_chartAt : (⋃ x : M, (chartAt H x).source) = (univ : Set M) :=
  eq_univ_iff_forall.mpr fun x ↦ mem_iUnion.mpr ⟨x, mem_chart_source H x⟩

theorem ChartedSpace.isOpen_iff (s : Set M) :
    IsOpen s ↔ ∀ x : M, IsOpen <| chartAt H x '' ((chartAt H x).source ∩ s) := by
  rw [isOpen_iff_of_cover (fun i ↦ (chartAt H i).open_source) (iUnion_source_chartAt H M)]
  simp only [(chartAt H _).isOpen_image_iff_of_subset_source inter_subset_left]

/-- `achart H x` is the chart at `x`, considered as an element of the atlas.
Especially useful for working with `BasicContMDiffVectorBundleCore`. -/
def achart (x : M) : atlas H M :=
  ⟨chartAt H x, chart_mem_atlas H x⟩

theorem achart_def (x : M) : achart H x = ⟨chartAt H x, chart_mem_atlas H x⟩ :=
  rfl

@[simp, mfld_simps]
theorem coe_achart (x : M) : (achart H x : OpenPartialHomeomorph M H) = chartAt H x :=
  rfl

@[simp, mfld_simps]
theorem achart_val (x : M) : (achart H x).1 = chartAt H x :=
  rfl

theorem mem_achart_source (x : M) : x ∈ (achart H x).1.source :=
  mem_chart_source H x

open TopologicalSpace

theorem ChartedSpace.secondCountable_of_countable_cover [SecondCountableTopology H] {s : Set M}
    (hs : ⋃ (x) (_ : x ∈ s), (chartAt H x).source = univ) (hsc : s.Countable) :
    SecondCountableTopology M := by
  haveI : ∀ x : M, SecondCountableTopology (chartAt H x).source :=
    fun x ↦ (chartAt (H := H) x).secondCountableTopology_source
  haveI := hsc.toEncodable
  rw [biUnion_eq_iUnion] at hs
  exact secondCountableTopology_of_countable_cover (fun x : s ↦ (chartAt H (x : M)).open_source) hs

variable (M)

theorem ChartedSpace.secondCountable_of_sigmaCompact [SecondCountableTopology H]
    [SigmaCompactSpace M] : SecondCountableTopology M := by
  obtain ⟨s, hsc, hsU⟩ : ∃ s, Set.Countable s ∧ ⋃ (x) (_ : x ∈ s), (chartAt H x).source = univ :=
    countable_cover_nhds_of_sigmaCompact fun x : M ↦ chart_source_mem_nhds H x
  exact ChartedSpace.secondCountable_of_countable_cover H hsU hsc

/-- If a topological space admits an atlas with locally compact charts, then the space itself
is locally compact. -/
theorem ChartedSpace.locallyCompactSpace [LocallyCompactSpace H] : LocallyCompactSpace M := by
  have : ∀ x : M, (𝓝 x).HasBasis
      (fun s ↦ s ∈ 𝓝 (chartAt H x x) ∧ IsCompact s ∧ s ⊆ (chartAt H x).target)
      fun s ↦ (chartAt H x).symm '' s := fun x ↦ by
    rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact ((compact_basis_nhds (chartAt H x x)).hasBasis_self_subset
      (chart_target_mem_nhds H x)).map _
  refine .of_hasBasis this ?_
  rintro x s ⟨_, h₂, h₃⟩
  exact h₂.image_of_continuousOn ((chartAt H x).continuousOn_symm.mono h₃)

/-- If a topological space admits an atlas with locally connected charts, then the space itself is
locally connected. -/
theorem ChartedSpace.locallyConnectedSpace [LocallyConnectedSpace H] : LocallyConnectedSpace M := by
  let e : M → OpenPartialHomeomorph M H := chartAt H
  refine locallyConnectedSpace_of_connected_bases (fun x s ↦ (e x).symm '' s)
      (fun x s ↦ (IsOpen s ∧ e x x ∈ s ∧ IsConnected s) ∧ s ⊆ (e x).target) ?_ ?_
  · intro x
    simpa only [e, OpenPartialHomeomorph.symm_map_nhds_eq, mem_chart_source] using
      ((LocallyConnectedSpace.open_connected_basis (e x x)).restrict_subset
        ((e x).open_target.mem_nhds (mem_chart_target H x))).map (e x).symm
  · rintro x s ⟨⟨-, -, hsconn⟩, hssubset⟩
    exact hsconn.isPreconnected.image _ ((e x).continuousOn_symm.mono hssubset)

/-- If a topological space `M` admits an atlas with locally path-connected charts,
then `M` itself is locally path-connected. -/
theorem ChartedSpace.locPathConnectedSpace [LocPathConnectedSpace H] : LocPathConnectedSpace M := by
  refine ⟨fun x ↦ ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨u, hu⟩ ↦ Filter.mem_of_superset hu.1.1 hu.2⟩⟩⟩
  let e := chartAt H x
  let t := s ∩ e.source
  have ht : t ∈ 𝓝 x := Filter.inter_mem hs (chart_source_mem_nhds _ _)
  refine ⟨e.symm '' pathComponentIn (e '' t) (e x), ⟨?_, ?_⟩, (?_ : _ ⊆ t).trans inter_subset_left⟩
  · nth_rewrite 1 [← e.left_inv (mem_chart_source _ _)]
    apply e.symm.image_mem_nhds (by simp [e])
    exact pathComponentIn_mem_nhds <| e.image_mem_nhds (mem_chart_source _ _) ht
  · refine (isPathConnected_pathComponentIn <| mem_image_of_mem e (mem_of_mem_nhds ht)).image' ?_
    refine e.continuousOn_symm.mono <| subset_trans ?_ e.map_source''
    exact (pathComponentIn_mono <| image_mono inter_subset_right).trans pathComponentIn_subset
  · exact (image_mono pathComponentIn_subset).trans
      (PartialEquiv.symm_image_image_of_subset_source _ inter_subset_right).subset

/-- If `M` is modelled on `H'` and `H'` is itself modelled on `H`, then we can consider `M` as being
modelled on `H`. -/
def ChartedSpace.comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
    (M : Type*) [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] :
    ChartedSpace H M where
  atlas := image2 OpenPartialHomeomorph.trans (atlas H' M) (atlas H H')
  chartAt p := (chartAt H' p).trans (chartAt H (chartAt H' p p))
  mem_chart_source p := by simp only [mfld_simps]
  chart_mem_atlas p := ⟨chartAt _ p, chart_mem_atlas _ p, chartAt _ _, chart_mem_atlas _ _, rfl⟩

theorem chartAt_comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] (x : M) :
    (letI := ChartedSpace.comp H H' M; chartAt H x) = chartAt H' x ≫ₕ chartAt H (chartAt H' x x) :=
  rfl

/-- A charted space over a T1 space is T1. Note that this is *not* true for T2 (for instance for
the real line with a double origin). -/
theorem ChartedSpace.t1Space [T1Space H] : T1Space M := by
  apply t1Space_iff_exists_open.2 (fun x y hxy ↦ ?_)
  by_cases hy : y ∈ (chartAt H x).source
  · refine ⟨(chartAt H x).source ∩ (chartAt H x)⁻¹' ({chartAt H x y}ᶜ), ?_, ?_, by simp⟩
    · exact OpenPartialHomeomorph.isOpen_inter_preimage _ isOpen_compl_singleton
    · simp only [preimage_compl, mem_inter_iff, mem_chart_source, mem_compl_iff, mem_preimage,
        mem_singleton_iff, true_and]
      exact (chartAt H x).injOn.ne (ChartedSpace.mem_chart_source x) hy hxy
  · exact ⟨(chartAt H x).source, (chartAt H x).open_source, ChartedSpace.mem_chart_source x, hy⟩

/-- A charted space over a discrete space is discrete. -/
theorem ChartedSpace.discreteTopology [DiscreteTopology H] : DiscreteTopology M := by
  apply discreteTopology_iff_isOpen_singleton.2 (fun x ↦ ?_)
  have : IsOpen ((chartAt H x).source ∩ (chartAt H x) ⁻¹' {chartAt H x x}) :=
    isOpen_inter_preimage _ (isOpen_discrete _)
  convert this
  refine Subset.antisymm (by simp) ?_
  simp only [subset_singleton_iff, mem_inter_iff, mem_preimage, mem_singleton_iff, and_imp]
  intro y hy h'y
  exact (chartAt H x).injOn hy (mem_chart_source _ x) h'y

end

section Constructions

/-- An empty type is a charted space over any topological space. -/
def ChartedSpace.empty (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [IsEmpty M] : ChartedSpace H M where
  atlas := ∅
  chartAt x := (IsEmpty.false x).elim
  mem_chart_source x := (IsEmpty.false x).elim
  chart_mem_atlas x := (IsEmpty.false x).elim

/-- Any space is a `ChartedSpace` modelled over itself, by just using the identity chart. -/
instance chartedSpaceSelf (H : Type*) [TopologicalSpace H] : ChartedSpace H H where
  atlas := {OpenPartialHomeomorph.refl H}
  chartAt _ := OpenPartialHomeomorph.refl H
  mem_chart_source x := mem_univ x
  chart_mem_atlas _ := mem_singleton _

/-- In the trivial `ChartedSpace` structure of a space modelled over itself through the identity,
the atlas members are just the identity. -/
@[simp, mfld_simps]
theorem chartedSpaceSelf_atlas {H : Type*} [TopologicalSpace H] {e : OpenPartialHomeomorph H H} :
    e ∈ atlas H H ↔ e = OpenPartialHomeomorph.refl H :=
  Iff.rfl

/-- In the model space, `chartAt` is always the identity. -/
theorem chartAt_self_eq {H : Type*} [TopologicalSpace H] {x : H} :
    chartAt H x = OpenPartialHomeomorph.refl H := rfl

/-- Any discrete space is a charted space over a singleton set.
We keep this as a definition (not an instance) to avoid instance search trying to search for
`DiscreteTopology` or `Unique` instances.
-/
def ChartedSpace.of_discreteTopology [TopologicalSpace M] [TopologicalSpace H]
    [DiscreteTopology M] [h : Unique H] : ChartedSpace H M where
  atlas :=
    letI f := fun x : M ↦ OpenPartialHomeomorph.const
      (isOpen_discrete {x}) (isOpen_discrete {h.default})
    Set.image f univ
  chartAt x := OpenPartialHomeomorph.const (isOpen_discrete {x}) (isOpen_discrete {h.default})
  mem_chart_source x := by simp
  chart_mem_atlas x := by simp

/-- A chart on the discrete space is the constant chart. -/
@[simp, mfld_simps]
lemma chartedSpace_of_discreteTopology_chartAt [TopologicalSpace M] [TopologicalSpace H]
    [DiscreteTopology M] [h : Unique H] {x : M} :
    haveI := ChartedSpace.of_discreteTopology (M := M) (H := H)
    chartAt H x = OpenPartialHomeomorph.const (isOpen_discrete {x}) (isOpen_discrete {h.default}) :=
  rfl

section Products

library_note «Manifold type tags» /-- For technical reasons we introduce two type tags:

* `ModelProd H H'` is the same as `H × H'`;
* `ModelPi H` is the same as `∀ i, H i`, where `H : ι → Type*` and `ι` is a finite type.

In both cases the reason is the same, so we explain it only in the case of the product. A charted
space `M` with model `H` is a set of charts from `M` to `H` covering the space. Every space is
registered as a charted space over itself, using the only chart `id`, in `chartedSpaceSelf`. You
can also define a product of charted space `M` and `M'` (with model space `H × H'`) by taking the
products of the charts. Now, on `H × H'`, there are two charted space structures with model space
`H × H'` itself, the one coming from `chartedSpaceSelf`, and the one coming from the product of
the two `chartedSpaceSelf` on each component. They are equal, but not defeq (because the product
of `id` and `id` is not defeq to `id`), which is bad as we know. This expedient of renaming `H × H'`
solves this problem. -/


/-- Same thing as `H × H'`. We introduce it for technical reasons,
see note [Manifold type tags]. -/
def ModelProd (H : Type*) (H' : Type*) :=
  H × H'

/-- Same thing as `∀ i, H i`. We introduce it for technical reasons,
see note [Manifold type tags]. -/
def ModelPi {ι : Type*} (H : ι → Type*) :=
  ∀ i, H i

section

instance modelProdInhabited [Inhabited H] [Inhabited H'] : Inhabited (ModelProd H H') :=
  instInhabitedProd

instance (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H'] :
    TopologicalSpace (ModelProd H H') :=
  instTopologicalSpaceProd

-- Next lemma shows up often when dealing with derivatives, so we register it as simp lemma.
@[simp, mfld_simps]
theorem modelProd_range_prod_id {H : Type*} {H' : Type*} {α : Type*} (f : H → α) :
    (range fun p : ModelProd H H' ↦ (f p.1, p.2)) = range f ×ˢ (univ : Set H') := by
  rw [prod_range_univ_eq]
  rfl

end

section

variable {ι : Type*} {Hi : ι → Type*}

instance modelPiInhabited [∀ i, Inhabited (Hi i)] : Inhabited (ModelPi Hi) :=
  Pi.instInhabited

instance [∀ i, TopologicalSpace (Hi i)] : TopologicalSpace (ModelPi Hi) :=
  Pi.topologicalSpace

end

/-- The product of two charted spaces is naturally a charted space, with the canonical
construction of the atlas of product maps. -/
instance prodChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (H' : Type*) [TopologicalSpace H'] (M' : Type*) [TopologicalSpace M']
    [ChartedSpace H' M'] : ChartedSpace (ModelProd H H') (M × M') where
  atlas := image2 OpenPartialHomeomorph.prod (atlas H M) (atlas H' M')
  chartAt x := (chartAt H x.1).prod (chartAt H' x.2)
  mem_chart_source x := ⟨mem_chart_source H x.1, mem_chart_source H' x.2⟩
  chart_mem_atlas x := mem_image2_of_mem (chart_mem_atlas H x.1) (chart_mem_atlas H' x.2)

section prodChartedSpace

@[ext]
theorem ModelProd.ext {x y : ModelProd H H'} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y :=
  Prod.ext h₁ h₂

variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {x : M × M'}

@[simp, mfld_simps]
theorem prodChartedSpace_chartAt :
    chartAt (ModelProd H H') x = (chartAt H x.fst).prod (chartAt H' x.snd) :=
  rfl

theorem chartedSpaceSelf_prod : prodChartedSpace H H H' H' = chartedSpaceSelf (H × H') := by
  ext1
  · simp [atlas, ChartedSpace.atlas]
  · ext1
    simp only [prodChartedSpace_chartAt, chartAt_self_eq, refl_prod_refl]
    rfl

end prodChartedSpace

/-- The product of a finite family of charted spaces is naturally a charted space, with the
canonical construction of the atlas of finite product maps. -/
instance piChartedSpace {ι : Type*} [Finite ι] (H : ι → Type*) [∀ i, TopologicalSpace (H i)]
    (M : ι → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)] :
    ChartedSpace (ModelPi H) (∀ i, M i) where
  atlas := OpenPartialHomeomorph.pi '' Set.pi univ fun _ ↦ atlas (H _) (M _)
  chartAt f := OpenPartialHomeomorph.pi fun i ↦ chartAt (H i) (f i)
  mem_chart_source f i _ := mem_chart_source (H i) (f i)
  chart_mem_atlas f := mem_image_of_mem _ fun i _ ↦ chart_mem_atlas (H i) (f i)

@[simp, mfld_simps]
theorem piChartedSpace_chartAt {ι : Type*} [Finite ι] (H : ι → Type*)
    [∀ i, TopologicalSpace (H i)] (M : ι → Type*) [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (H i) (M i)] (f : ∀ i, M i) :
    chartAt (H := ModelPi H) f = OpenPartialHomeomorph.pi fun i ↦ chartAt (H i) (f i) :=
  rfl

end Products

section sum

variable [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace M']
    [cm : ChartedSpace H M] [cm' : ChartedSpace H M']

/-- The disjoint union of two charted spaces modelled on a non-empty space `H`
is a charted space over `H`. -/
def ChartedSpace.sum_of_nonempty [Nonempty H] : ChartedSpace H (M ⊕ M') where
  atlas := ((fun e ↦ e.lift_openEmbedding IsOpenEmbedding.inl) '' cm.atlas) ∪
    ((fun e ↦ e.lift_openEmbedding IsOpenEmbedding.inr) '' cm'.atlas)
  -- At `x : M`, the chart is the chart in `M`; at `x' ∈ M'`, it is the chart in `M'`.
  chartAt := Sum.elim (fun x ↦ (cm.chartAt x).lift_openEmbedding IsOpenEmbedding.inl)
    (fun x ↦ (cm'.chartAt x).lift_openEmbedding IsOpenEmbedding.inr)
  mem_chart_source p := by
    cases p with
    | inl x =>
      rw [Sum.elim_inl, lift_openEmbedding_source,
        ← OpenPartialHomeomorph.lift_openEmbedding_source _ IsOpenEmbedding.inl]
      use x, cm.mem_chart_source x
    | inr x =>
      rw [Sum.elim_inr, lift_openEmbedding_source,
        ← OpenPartialHomeomorph.lift_openEmbedding_source _ IsOpenEmbedding.inr]
      use x, cm'.mem_chart_source x
  chart_mem_atlas p := by
    cases p with
    | inl x =>
      rw [Sum.elim_inl]
      left
      use ChartedSpace.chartAt x, cm.chart_mem_atlas x
    | inr x =>
      rw [Sum.elim_inr]
      right
      use ChartedSpace.chartAt x, cm'.chart_mem_atlas x

open scoped Classical in
instance ChartedSpace.sum : ChartedSpace H (M ⊕ M') := by
  by_cases! h : Nonempty H
  · exact ChartedSpace.sum_of_nonempty
  have : IsEmpty M := isEmpty_of_chartedSpace H
  have : IsEmpty M' := isEmpty_of_chartedSpace H
  exact empty H (M ⊕ M')

lemma ChartedSpace.sum_chartAt_inl (x : M) :
    haveI : Nonempty H := nonempty_of_chartedSpace x
    chartAt H (Sum.inl x)
      = (chartAt H x).lift_openEmbedding (X' := M ⊕ M') IsOpenEmbedding.inl := by
  simp only [chartAt, sum, nonempty_of_chartedSpace x, ↓reduceDIte]
  rfl

lemma ChartedSpace.sum_chartAt_inr (x' : M') :
    haveI : Nonempty H := nonempty_of_chartedSpace x'
    chartAt H (Sum.inr x')
      = (chartAt H x').lift_openEmbedding (X' := M ⊕ M') IsOpenEmbedding.inr := by
  simp only [chartAt, sum, nonempty_of_chartedSpace x', ↓reduceDIte]
  rfl

@[simp, mfld_simps] lemma sum_chartAt_inl_apply {x y : M} :
    (chartAt H (.inl x : M ⊕ M')) (Sum.inl y) = (chartAt H x) y := by
  haveI : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inl]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

@[simp, mfld_simps] lemma sum_chartAt_inr_apply {x y : M'} :
    (chartAt H (.inr x : M ⊕ M')) (Sum.inr y) = (chartAt H x) y := by
  haveI : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inr]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

lemma ChartedSpace.mem_atlas_sum [h : Nonempty H]
    {e : OpenPartialHomeomorph (M ⊕ M') H} (he : e ∈ atlas H (M ⊕ M')) :
    (∃ f : OpenPartialHomeomorph M H, f ∈ (atlas H M)
      ∧ e = (f.lift_openEmbedding IsOpenEmbedding.inl))
    ∨ (∃ f' : OpenPartialHomeomorph M' H, f' ∈ (atlas H M') ∧
      e = (f'.lift_openEmbedding IsOpenEmbedding.inr)) := by
  simp only [atlas, sum, h, ↓reduceDIte] at he
  obtain (⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩) := he
  · rw [← hxe]; left; use x
  · rw [← hxe]; right; use x

end sum

end Constructions

end ChartedSpace

/-! ### Constructing a topology from an atlas -/

/-- Sometimes, one may want to construct a charted space structure on a space which does not yet
have a topological structure, where the topology would come from the charts. For this, one needs
charts that are only partial equivalences, and continuity properties for their composition.
This is formalised in `ChartedSpaceCore`. -/
structure ChartedSpaceCore (H : Type*) [TopologicalSpace H] (M : Type*) where
  /-- An atlas of charts, which are only `PartialEquiv`s -/
  atlas : Set (PartialEquiv M H)
  /-- The preferred chart at each point -/
  chartAt : M → PartialEquiv M H
  mem_chart_source : ∀ x, x ∈ (chartAt x).source
  chart_mem_atlas : ∀ x, chartAt x ∈ atlas
  open_source : ∀ e e' : PartialEquiv M H, e ∈ atlas → e' ∈ atlas → IsOpen (e.symm.trans e').source
  continuousOn_toFun : ∀ e e' : PartialEquiv M H, e ∈ atlas → e' ∈ atlas →
    ContinuousOn (e.symm.trans e') (e.symm.trans e').source

namespace ChartedSpaceCore

variable [TopologicalSpace H] (c : ChartedSpaceCore H M) {e : PartialEquiv M H}

/-- Topology generated by a set of charts on a Type. -/
protected def toTopologicalSpace : TopologicalSpace M :=
  TopologicalSpace.generateFrom <|
    ⋃ (e : PartialEquiv M H) (_ : e ∈ c.atlas) (s : Set H) (_ : IsOpen s),
      {e ⁻¹' s ∩ e.source}

theorem open_source' (he : e ∈ c.atlas) : IsOpen[c.toTopologicalSpace] e.source := by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine ⟨e, he, univ, isOpen_univ, ?_⟩
  simp only [Set.univ_inter, Set.preimage_univ]

theorem open_target (he : e ∈ c.atlas) : IsOpen e.target := by
  have E : e.target ∩ e.symm ⁻¹' e.source = e.target :=
    Subset.antisymm inter_subset_left fun x hx ↦
      ⟨hx, PartialEquiv.target_subset_preimage_source _ hx⟩
  simpa [PartialEquiv.trans_source, E] using c.open_source e e he he

/-- An element of the atlas in a charted space without topology becomes an open partial
homeomorphism for the topology constructed from this atlas. The `OpenPartialHomeomorph` version is
given in this definition. -/
protected def openPartialHomeomorph (e : PartialEquiv M H) (he : e ∈ c.atlas) :
    @OpenPartialHomeomorph M H c.toTopologicalSpace _ :=
  { __ := c.toTopologicalSpace
    __ := e
    open_source := by convert c.open_source' he
    open_target := by convert c.open_target he
    continuousOn_toFun := by
      letI : TopologicalSpace M := c.toTopologicalSpace
      rw [continuousOn_open_iff (c.open_source' he)]
      intro s s_open
      rw [inter_comm]
      apply TopologicalSpace.GenerateOpen.basic
      simp only [exists_prop, mem_iUnion, mem_singleton_iff]
      exact ⟨e, he, ⟨s, s_open, rfl⟩⟩
    continuousOn_invFun := by
      letI : TopologicalSpace M := c.toTopologicalSpace
      apply continuousOn_isOpen_of_generateFrom
      intro t ht
      simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
      rcases ht with ⟨e', e'_atlas, s, s_open, ts⟩
      rw [ts]
      let f := e.symm.trans e'
      have : IsOpen (f ⁻¹' s ∩ f.source) := by
        simpa [f, inter_comm] using (continuousOn_open_iff (c.open_source e e' he e'_atlas)).1
          (c.continuousOn_toFun e e' he e'_atlas) s s_open
      have A : e' ∘ e.symm ⁻¹' s ∩ (e.target ∩ e.symm ⁻¹' e'.source) =
          e.target ∩ (e' ∘ e.symm ⁻¹' s ∩ e.symm ⁻¹' e'.source) := by
        rw [← inter_assoc, ← inter_assoc]
        congr 1
        exact inter_comm _ _
      simpa [f, PartialEquiv.trans_source, preimage_inter, preimage_comp.symm, A] using this }

@[deprecated (since := "2025-08-29")] alias
  partialHomeomorph := ChartedSpaceCore.openPartialHomeomorph

/-- Given a charted space without topology, endow it with a genuine charted space structure with
respect to the topology constructed from the atlas. -/
def toChartedSpace : @ChartedSpace H _ M c.toTopologicalSpace :=
  { __ := c.toTopologicalSpace
    atlas := ⋃ (e : PartialEquiv M H) (he : e ∈ c.atlas), {c.openPartialHomeomorph e he}
    chartAt := fun x ↦ c.openPartialHomeomorph (c.chartAt x) (c.chart_mem_atlas x)
    mem_chart_source := fun x ↦ c.mem_chart_source x
    chart_mem_atlas := fun x ↦ by
      simp only [mem_iUnion, mem_singleton_iff]
      exact ⟨c.chartAt x, c.chart_mem_atlas x, rfl⟩}

end ChartedSpaceCore

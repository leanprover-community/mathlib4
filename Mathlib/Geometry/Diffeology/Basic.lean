/-
Copyright (c) 2024 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Diffeological spaces

A diffeological space is a concrete sheaf on the site of cartesian spaces ℝⁿ and smooth maps
between them, or equivalently a type `X` with a well-behaved notion of smoothness for functions from
the spaces ℝⁿ to X - see https://ncatlab.org/nlab/show/diffeological+space. In this file we focus on
the latter viewpoint and define some of the basic notions of diffeology, like diffeological spaces
and smooth maps between them.

Concretely, this means that for our purposes a diffeological space is a type `X` together with a set
`plots n` of maps ℝⁿ → X for each n (called plots), such that the following three properties hold:
* Every constant map is a plot.
* For every plot p : ℝⁿ → X and smooth map f : ℝᵐ → ℝⁿ, p ∘ f is a plot.
* Every map p : ℝⁿ → X that is locally smooth is a plot, where by locally smooth we mean that ℝⁿ can
  be covered by open sets U such that p ∘ f is a plot for every smooth f : ℝᵐ → U.
Every normed space, smooth manifold etc. is then naturally a diffeological space by simply taking
the plots to be those maps ℝⁿ → X that are smooth in the traditional sense. A map `f : X → Y`
between diffeological spaces is furthermore called smooth if postcomposition with it sends plots of
`X` to plots of `Y`. This is equivalent to the usual definition of smoothness for maps between e.g.
manifolds, and equivalent to being a plot for maps p : ℝⁿ → X.

In addition to this notion of smoothness, every diffeological space `X` also comes equipped with a
natural diffeology, called the D-topology; it is the finest topology on `X` that makes all plots
continuous, and consists precisely of those sets whose preimages under plots are all open. This
recovers the standard topology of e.g. normed spaces and manifolds, and makes all smooth maps
continuous. We provide this as a definition but not as an instance, for reasons outlined in the
implementation details below.

## Main definitions / results

* `DiffeologicalSpace X`: the type of diffeologies on a type `X`.
* `IsPlot p`: predicate stating that a map p : ℝⁿ → X is a plot, i.e. belongs to the diffeology
  on `X`.
* `DSmooth f`: predicate stating that a map `f : X → Y` between diffeological spaces is smooth in
  the sense that it sends plots to plots. This is the correct notion of morphisms between
  diffeological spaces.
* `dTopology`: the D-topology on a diffeological space, consisting of all sets `U` whose preimage
  `p ⁻¹' u` is open for all plots `p`. This is a definition rather than an instance to avoid
  typeclass diamonds (see below), and meant for use with notation such as
  `Continuous[_, dTopology]`.
* `IsDTopologyCompatible X`: typeclass stating that `X` is equipped with a topology that is equal
  (but not necessarily defeq) to the D-topology.
* `NormedSpace.toDiffeology`: the standard diffeology on any finite-dimensional normed space `X`,
  consisting of all conventionally smooth maps ℝⁿ → X. This is again a definition rather than a
  instance for typeclass diamond reasons; however, we do put this as an instance on `ℝ` and
  `EuclideanSpace ℝ ι` for finite `ι`.
* `IsContDiffCompatible X`: typeclass stating that the diffeology on a normed space `X` is equal to
  the diffeology whose plots are precisely the smooth maps.
* `isPlot_iff_dSmooth`: a map ℝⁿ → X is a plot iff it is smooth.
* `dSmooth_iff_contDiff`: a map between finite-dimensional normed spaces is smooth in the sense of
  `DSmooth` iff it is smooth in the sense of `ContDiff ℝ ∞`.

## Implementation notes

### Choice of test spaces

Instead of defining diffeologies as collections of plots ℝⁿ → X whose domains are the spaces ℝⁿ, we
could have also defined them in terms of maps from some other collection of test spaces; for
example:
* all open balls in the spaces ℝⁿ
* all open subsets of the spaces ℝⁿ
* all finite-dimensional normed spaces, or open balls therein / open subsets thereof
* all finite-dimensional smooth manifolds.

All of these result in equivalent notions of diffeologies and smooth maps; the abstract way to see
this is that the corresponding sites are all dense subsites of the site of finite-dimensional smooth
manifolds, and hence give rise to equivalent sheaf topoi. Which of those sites / collections of test
spaces to use is hence mainly a matter of convenience; we have gone with the cartesian spaces ℝⁿ
mainly for two reasons:
* They are the simplest to work with for practical purposes: maps between subsets are more annoying
  to deal with formally than maps between types, and e.g. smooth manifolds are extremely annoying
  to quantify over, while the cartesian spaces ℝⁿ are indexed simply by the natural numbers ℕ.
* Working with e.g. all finite-dimensional normed spaces instead of this particular choice of
  representatives would lead to an unnecessary universe bump.

One downside of this choice compared to that of all open subsets of ℝⁿ is however that it makes the
sheaf condition / locality condition of diffeologies ("any map that is locally a plot is also
globally a plot") somewhat awkward to state and prove. To mitigate this, we provide
`DiffeologicalSpace.ofPlotsOn` as a way to construct a diffeology from plots whose domains are
subsets of ℝⁿ. See the definition of `NormedSpace.toDiffeology` for an example where this is used.

### D-Topology

While the D-topology is quite well-behaved in some regards, it does unfortunately not always commute
with e.g. products. This means that it can not be registered as an instance - otherwise, there would
be two `TopologicalSpace`-instances on binary products, the product topology of the D-topologies on
the factors and the D-topology of the product diffeology. For emphasis we repeat: in general these
topologies can be mathematically distinct not just non-defeq. We thus instead define a typeclass
`IsDTopologyCompatible X` to express when the topology on `X` does match the D-topology, and also
give the D-topology the short name `dTopology` to enable use of notations such as
`Continuous[_, dTopology]` for continuity with respect to the D-topology.

In order to make it easier to work with diffeological spaces whose natural diffeology does match
the D-topology, we also include the D-topology as part of the data of `DiffeologicalSpace X`.
This allows the diffeologies on e.g. ℝⁿ, manifolds and quotients of diffeological spaces to be
defined in such a way that the D-topology is defeq to the topology that the space already carries.

### Diffeologies on normed spaces

Every normed spaces carries a natural diffeology consisting of all smooth maps from ℝⁿ. While this
"normed space diffeology" does commute with arbitrary products, we can't register it as an instance
because it wouldn't be defeq to the product diffeology on products of normed spaces. We thus only
give it as a definition (`NormedSpace.toDiffeology`) instead of an instance, and instead provide a
typeclass `IsContDiffCompatible X` for talking about normed spaces equipped with the normed space
diffeology.

To make working with finite-dimensional spaces easier, `NormedSpace.toDiffeology` is defined in such
a way that its D-topology is defeq to the topology induced by the norm - however, this currently
comes at the cost of making the definition work only on finite-dimensional spaces. It should be
possible to extend this to all normed spaces though in the future.

## TODO

Much of the basic theory of diffeological spaces has already been formalised at
https://github.com/peabrainiac/lean-orbifolds and just needs to be upstreamed. However, some TODOs
that haven't been formalised at all yet and only depend on the material here are:
* Generalise `NormedSpace.toDiffeology` to infinite-dimensional normed spaces. The hard part of this
  is showing that the D-topology of any normed space is just its usual topology, as is needed to
  make that equality definitional. On paper, this is relatively straightforward:
  for a set U ⊆ X that is not open under the standard normed space topology, take a sequence x_i
  outside of U that converges to a point in U, a smooth map ℝ → X under which a convergent sequence
  in ℝ maps to this sequence (x_i), and use it to conclude that U is not D-open either. However,
  constructing the needed smooth map explicitly is probably a lot of work.
* Generalise `dSmooth_iff_contDiff` to infinite-dimensional normed spaces if possible. There should
  be some references at least for the case of Banach spaces in the literature.

## References

* [Patrick Iglesias-Zemmour, *Diffeology*][zemmour2013diffeology]
* <https://ncatlab.org/nlab/show/diffeological+space>

## Tags
diffeology, diffeological space, smoothness, smooth function
-/

@[expose] public section

noncomputable section

assert_not_exists ChartedSpace

local macro:max "𝔼" noWs n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

open Topology ContDiff

/-- A diffeology on `X`, given by the smooth functions (or "plots") from ℝⁿ to `X`. -/
class DiffeologicalSpace (X : Type*) where
  /-- The plots `EuclideanSpace ℝ (Fin n) → X` representing the smooth ways to map
  `EuclideanSpace ℝ (Fin n)` into `X`. This is the main
  piece of data underlying the diffeology. -/
  plots (n : ℕ) : Set (𝔼ⁿ → X)
  /-- Every constant map needs to be a plot. -/
  constant_plots {n : ℕ} (x : X) : (fun _ ↦ x) ∈ plots n
  /-- Smooth reparametrisations of plots need to be plots. -/
  plot_reparam {n m : ℕ} {p : 𝔼ᵐ → X} {f : 𝔼ⁿ → 𝔼ᵐ} (hp : p ∈ plots m) (hf : ContDiff ℝ ∞ f) :
    p ∘ f ∈ plots n
  /-- Every locally smooth map `EuclideanSpace ℝ (Fin n) → X` is a plot. -/
  locality {n : ℕ} {p : 𝔼ⁿ → X} (hp : ∀ x : 𝔼ⁿ, ∃ u : Set 𝔼ⁿ, IsOpen u ∧ x ∈ u ∧
    ∀ {m : ℕ} {f : 𝔼ᵐ → 𝔼ⁿ}, (∀ x, f x ∈ u) → ContDiff ℝ ∞ f → p ∘ f ∈ plots m) : p ∈ plots n
  /-- The D-topology of the diffeology. This is included as part of the data in order to give
  control over what the D-topology is defeq to. See also note [forgetful inheritance]. -/
  dTopology : TopologicalSpace X := {
    IsOpen u := ∀ ⦃n : ℕ⦄, ∀ p ∈ plots n, IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ _ ↦ isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp ↦
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp ↦
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu ↦ hs u hu p hp }
  /-- The D-topology consists of exactly those sets whose preimages under plots are all open. -/
  isOpen_iff_preimages_plots {u : Set X} :
    dTopology.IsOpen u ↔ ∀ {n : ℕ}, ∀ p ∈ plots n, IsOpen (p ⁻¹' u) := by rfl

namespace Diffeology

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

section Defs

alias dTopology := DiffeologicalSpace.dTopology

/-- A map `p : EuclideanSpace ℝ (Fin n) → X` is called a plot iff it is part of the diffeology on
`X`. This is equivalent to `p` being smooth with respect to the standard diffeology on
`EuclideanSpace ℝ (Fin n)`. -/
@[fun_prop]
def IsPlot {n : ℕ} (p : 𝔼ⁿ → X) : Prop := p ∈ DiffeologicalSpace.plots n

/-- A function between diffeological spaces is smooth iff composition with it preserves
smoothness of plots. -/
@[fun_prop]
def DSmooth (f : X → Y) : Prop := ∀ (n : ℕ) (p : 𝔼ⁿ → X), IsPlot p → IsPlot (f ∘ p)

end Defs

@[ext]
protected theorem _root_.DiffeologicalSpace.ext {X : Type*} {d₁ d₂ : DiffeologicalSpace X}
    (h : @IsPlot _ d₁ = @IsPlot _ d₂) : d₁ = d₂ := by
  obtain ⟨p₁, _, _, _, t₁, h₁⟩ := d₁
  obtain ⟨p₂, _, _, _, t₂, h₂⟩ := d₂
  congr 1; ext s
  exact ((show p₁ = p₂ from h) ▸ @h₁ s).trans (@h₂ s).symm

@[fun_prop]
lemma isPlot_const {n : ℕ} {x : X} : IsPlot (fun _ ↦ x : 𝔼ⁿ → X) :=
  DiffeologicalSpace.constant_plots x

lemma isPlot_reparam {n m : ℕ} {p : 𝔼ᵐ → X} {f : 𝔼ⁿ → 𝔼ᵐ} (hp : IsPlot p) (hf : ContDiff ℝ ∞ f) :
    IsPlot (p ∘ f) :=
  DiffeologicalSpace.plot_reparam hp hf

protected lemma IsPlot.dSmooth_comp {n : ℕ} {p : 𝔼ⁿ → X} {f : X → Y}
    (hp : IsPlot p) (hf : DSmooth f) : IsPlot (f ∘ p) :=
  hf n p hp

@[fun_prop]
protected lemma IsPlot.dSmooth_comp' {n : ℕ} {p : 𝔼ⁿ → X} {f : X → Y}
    (hp : IsPlot p) (hf : DSmooth f) : IsPlot fun x ↦ f (p x) :=
  hf n p hp

lemma isOpen_iff_preimages_plots {u : Set X} :
    IsOpen[dTopology] u ↔ ∀ (n : ℕ) (p : 𝔼ⁿ → X), IsPlot p → IsOpen (p ⁻¹' u) :=
  DiffeologicalSpace.isOpen_iff_preimages_plots

protected lemma IsPlot.continuous {n : ℕ} {p : 𝔼ⁿ → X} (hp : IsPlot p) :
    Continuous[_, dTopology] p :=
  continuous_def.2 fun _ hu ↦ isOpen_iff_preimages_plots.1 hu n p hp

protected theorem DSmooth.continuous {f : X → Y} (hf : DSmooth f) :
    Continuous[dTopology, dTopology] f := by
  simp_rw [continuous_def, isOpen_iff_preimages_plots (X := X), isOpen_iff_preimages_plots (X := Y)]
  exact fun u hu n p hp ↦ hu n (f ∘ p) (hf n p hp)

theorem dSmooth_iff {f : X → Y} :
    DSmooth f ↔ ∀ (n : ℕ) (p : 𝔼ⁿ → X), IsPlot p → IsPlot (f ∘ p) :=
  Iff.rfl

theorem dSmooth_id : DSmooth (@id X) := by simp [DSmooth]

@[fun_prop]
theorem dSmooth_id' : DSmooth fun x : X ↦ x := dSmooth_id

theorem DSmooth.comp {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (g ∘ f) :=
  fun _ _ hp ↦ hg _ _ (hf _ _ hp)

@[fun_prop]
theorem DSmooth.comp' {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (fun x ↦ g (f x)) := hg.comp hf

@[fun_prop]
theorem dSmooth_const {y : Y} : DSmooth fun _ : X ↦ y :=
  fun _ _ _ ↦ isPlot_const

end Diffeology

namespace DiffeologicalSpace

/-- Replaces the D-topology of a diffeology with another topology equal to it. Useful
to construct diffeologies with better definitional equalities. -/
def replaceDTopology {X : Type*} (d : DiffeologicalSpace X)
    (t : TopologicalSpace X) (h : @dTopology _ d = t) : DiffeologicalSpace X where
  dTopology := t
  isOpen_iff_preimages_plots := by intro _; rw [← d.isOpen_iff_preimages_plots, ← h]
  __ := d

lemma replaceDTopology_eq {X : Type*} {d : DiffeologicalSpace X}
    {t : TopologicalSpace X} {h : @dTopology _ d = t} : d.replaceDTopology t h = d := by
  ext; rfl

/-- A structure with plots specified on open subsets of ℝⁿ rather than ℝⁿ itself. Useful
for constructing diffeologies, as it often makes the locality condition easier to prove. -/
structure CorePlotsOn (X : Type*) where
  /-- The predicate determining which maps `u → X` with `u : Set (EuclideanSpace ℝ (Fin n))` open
  are plots. -/
  isPlotOn {n : ℕ} {u : Set 𝔼ⁿ} (hu : IsOpen u) : (𝔼ⁿ → X) → Prop
  isPlotOn_congr {n : ℕ} {u : Set 𝔼ⁿ} (hu : IsOpen u) {p q : 𝔼ⁿ → X} (h : Set.EqOn p q u) :
    isPlotOn hu p ↔ isPlotOn hu q
  /-- The predicate that the diffeology built from this structure will use. Can be overwritten
  to allow for better definitional equalities. -/
  isPlot {n : ℕ} : (𝔼ⁿ → X) → Prop := fun p ↦ isPlotOn isOpen_univ p
  isPlotOn_univ {n : ℕ} {p : 𝔼ⁿ → X} :
    isPlotOn isOpen_univ p ↔ isPlot p := by simp
  isPlot_const {n : ℕ} (x : X) : isPlot fun (_ : 𝔼ⁿ) ↦ x
  isPlotOn_reparam {n m : ℕ} {u : Set 𝔼ⁿ} {v : Set 𝔼ᵐ} {hu : IsOpen u} (hv : IsOpen v)
    {p : 𝔼ⁿ → X} {f : 𝔼ᵐ → 𝔼ⁿ} (h : Set.MapsTo f v u) (hp : isPlotOn hu p)
    (hf : ContDiffOn ℝ ∞ f v) : isPlotOn hv (p ∘ f)
  /-- The locality axiom of diffeologies, phrased in terms of `isPlotOn`. -/
  locality {n : ℕ} {u : Set 𝔼ⁿ} (hu : IsOpen u) {p : 𝔼ⁿ → X}
    (hp : ∀ x ∈ u, ∃ (v : Set _) (hv : IsOpen v), x ∈ v ∧ isPlotOn hv p) : isPlotOn hu p
  /-- The D-topology that the diffeology built from this structure will use. Can be overwritten
  to allow for better definitional equalities. -/
  dTopology : TopologicalSpace X := {
    IsOpen u := ∀ ⦃n : ℕ⦄, ∀ p : 𝔼ⁿ → X, isPlot p → IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ _ ↦ isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp ↦
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp ↦
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu ↦ hs u hu p hp }
  isOpen_iff_preimages_plots {u : Set X} : dTopology.IsOpen u ↔
    ∀ {n : ℕ}, ∀ p : 𝔼ⁿ → X, isPlot p → IsOpen (p ⁻¹' u) := by rfl

/-- Constructs a diffeology from plots defined on open subsets or ℝⁿ rather than ℝⁿ itself,
organised in the form of the auxiliary `CorePlotsOn` structure.
This is more involved in most regards, but also often makes it quite a lot easier to prove
the locality condition. -/
def ofCorePlotsOn {X : Type*} (d : DiffeologicalSpace.CorePlotsOn X) :
    DiffeologicalSpace X where
  plots _ := {p | d.isPlot p}
  constant_plots _ := d.isPlot_const _
  plot_reparam hp hf := d.isPlotOn_univ.mp <|
    d.isPlotOn_reparam _ (Set.mapsTo_univ _ _) (d.isPlotOn_univ.mpr hp) hf.contDiffOn
  locality {n p} h := by
    refine d.isPlotOn_univ.mp <| d.locality _ fun x _ ↦ ?_
    let ⟨u, hu, hxu, hu'⟩ := h x
    let ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp hu x hxu
    have h : d.isPlot (p ∘ OpenPartialHomeomorph.univBall x ε) := hu'
      (f := OpenPartialHomeomorph.univBall x ε)
      (fun x' ↦ by
        replace h := (OpenPartialHomeomorph.univBall x ε).map_source (x := x')
        rw [OpenPartialHomeomorph.univBall_target x hε] at h
        aesop)
      OpenPartialHomeomorph.contDiff_univBall
    have h' := d.isPlotOn_reparam (Metric.isOpen_ball) (Set.mapsTo_univ _ _)
      (d.isPlotOn_univ.mpr h) (OpenPartialHomeomorph.contDiffOn_univBall_symm (c := x) (r := ε))
    refine ⟨_, Metric.isOpen_ball, Metric.mem_ball_self hε, (d.isPlotOn_congr _ ?_).mp h'⟩
    rw [Function.comp_assoc, ← OpenPartialHomeomorph.coe_trans]
    apply Set.EqOn.comp_left
    convert (OpenPartialHomeomorph.symm_trans_self (OpenPartialHomeomorph.univBall x ε)).2
    simp [OpenPartialHomeomorph.univBall_target x hε]
  dTopology := d.dTopology
  isOpen_iff_preimages_plots := d.isOpen_iff_preimages_plots

end DiffeologicalSpace

namespace Diffeology

/-- Technical condition saying that the topology on a type agrees with the D-topology.
Necessary because the D-topologies on for example products and subspaces don't agree with
the product and subspace topologies. -/
class IsDTopologyCompatible (X : Type*) [t : TopologicalSpace X] [DiffeologicalSpace X] : Prop where
  dTop_eq (X) : dTopology = t

/-- A smooth function between spaces that are equipped with the D-topology is continuous. -/
protected theorem DSmooth.continuous' {X Y : Type*}
    [TopologicalSpace X] [DiffeologicalSpace X] [IsDTopologyCompatible X]
    [TopologicalSpace Y] [DiffeologicalSpace Y] [IsDTopologyCompatible Y]
    {f : X → Y} (hf : DSmooth f) : Continuous f := by
  convert hf.continuous
  · rw [IsDTopologyCompatible.dTop_eq X]
  · rw [IsDTopologyCompatible.dTop_eq Y]

/-- Technical condition saying that the diffeology on a space is the one coming from
smoothness in the sense of `ContDiff ℝ ∞`. Necessary as a hypothesis for some theorems
because some normed spaces carry a diffeology that is equal but not defeq to the normed space
diffeology (for example the product diffeology in the case of `Fin n → ℝ`), so the information
that these theorems still holds needs to be made available via this typeclass. -/
class IsContDiffCompatible (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [DiffeologicalSpace X] : Prop where
  isPlot_iff {n : ℕ} {p : 𝔼ⁿ → X} : IsPlot p ↔ ContDiff ℝ ∞ p

/-- Diffeology on a finite-dimensional normed space. We make this a definition instead of an
instance because we also want to have product diffeologies as an instance, and having both would
cause instance diamonds on spaces like `Fin n → ℝ`. -/
def _root_.NormedSpace.toDiffeology (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    DiffeologicalSpace X :=
  .ofCorePlotsOn {
    isPlotOn := fun {_ u} _ p ↦ ContDiffOn ℝ ∞ p u
    isPlotOn_congr := fun _ _ _ h ↦ contDiffOn_congr h
    isPlot := fun p ↦ ContDiff ℝ ∞ p
    isPlotOn_univ := contDiffOn_univ
    isPlot_const := fun _ ↦ contDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf ↦ hp.comp hf h.subset_preimage
    locality := fun _ _ h ↦ fun x hxu ↦ by
      let ⟨v, hv, hxv, hv'⟩ := h x hxu
      exact ((hv' x hxv).contDiffAt (hv.mem_nhds hxv)).contDiffWithinAt
    dTopology := inferInstance
    isOpen_iff_preimages_plots := fun {u} ↦ by
      refine ⟨fun hu _ _ hp ↦ IsOpen.preimage (hp.continuous) hu, fun h ↦ ?_⟩
      rw [← toEuclidean.preimage_symm_preimage u]
      exact toEuclidean.continuous.isOpen_preimage _ (h _ toEuclidean.symm.contDiff) }

attribute [local instance] NormedSpace.toDiffeology in
instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    IsContDiffCompatible X :=
  ⟨Iff.rfl⟩

lemma _root_.NormedSpace.isContDiffCompatible_iff_eq_toDiffeology {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [d : DiffeologicalSpace X] :
    IsContDiffCompatible X ↔ d = NormedSpace.toDiffeology X :=
  ⟨fun _ ↦ by ext n p; exact IsContDiffCompatible.isPlot_iff, fun h ↦ h ▸ inferInstance⟩

attribute [local instance] NormedSpace.toDiffeology in
instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    IsDTopologyCompatible X :=
  ⟨rfl⟩

instance : DiffeologicalSpace ℝ := NormedSpace.toDiffeology _

instance {ι : Type*} [Fintype ι] : DiffeologicalSpace (EuclideanSpace ℝ ι) :=
  NormedSpace.toDiffeology _

variable {X : Type*} [DiffeologicalSpace X] {n : ℕ}

@[fun_prop]
protected theorem IsPlot.dSmooth {p : 𝔼ⁿ → X} (hp : IsPlot p) : DSmooth p :=
  fun _ _ ↦ isPlot_reparam hp

@[fun_prop]
protected theorem DSmooth.isPlot {p : 𝔼ⁿ → X} (hp : DSmooth p) : IsPlot p :=
  hp n id <| contDiff_id (n := ∞)

theorem isPlot_iff_dSmooth {p : 𝔼ⁿ → X} : IsPlot p ↔ DSmooth p :=
  ⟨IsPlot.dSmooth, DSmooth.isPlot⟩

lemma isPlot_id : IsPlot (@id 𝔼ⁿ) := contDiff_id (n := ∞)

@[fun_prop]
lemma isPlot_id' : IsPlot fun x : 𝔼ⁿ ↦ x := isPlot_id

variable {Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [IsContDiffCompatible X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [DiffeologicalSpace Y] [IsContDiffCompatible Y]

theorem isPlot_iff_contDiff {p : 𝔼ⁿ → X} : IsPlot p ↔ ContDiff ℝ ∞ p :=
  IsContDiffCompatible.isPlot_iff

@[fun_prop]
protected theorem _root_.ContDiff.isPlot {p : 𝔼ⁿ → X} (hp : ContDiff ℝ ∞ p) : IsPlot p :=
  isPlot_iff_contDiff.2 hp

@[fun_prop]
protected theorem IsPlot.contDiff {p : 𝔼ⁿ → X} (hp : IsPlot p) : ContDiff ℝ ∞ p :=
  isPlot_iff_contDiff.1 hp

@[fun_prop]
protected theorem _root_.ContDiff.dSmooth {f : X → Y} (hf : ContDiff ℝ ∞ f) : DSmooth f :=
  fun _ _ hp ↦ (hf.comp hp.contDiff).isPlot

@[fun_prop]
protected theorem DSmooth.contDiff [FiniteDimensional ℝ X] {f : X → Y} (hf : DSmooth f) :
    ContDiff ℝ ∞ f := by
  let g := toEuclidean (E := X)
  rw [← Function.comp_id f, ← g.symm_comp_self]
  exact (hf _ _ g.symm.contDiff.isPlot).contDiff.comp g.contDiff

theorem dSmooth_iff_contDiff [FiniteDimensional ℝ X] {f : X → Y} : DSmooth f ↔ ContDiff ℝ ∞ f :=
  ⟨DSmooth.contDiff, ContDiff.dSmooth⟩

end Diffeology

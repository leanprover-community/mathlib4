/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Diffeological spaces

A diffeological space is a concrete sheaf on the site of cartesian spaces ℝⁿ and smooth maps
between them, or equivalently a set `X` with a well-behaved notion of smoothness for functions from
ℝⁿ to X - see https://ncatlab.org/nlab/show/diffeological+space.

In this file we define some of the basic notions of diffeology, in particular a typeclass
`DiffeologicalSpace X`, the notions `IsPlot p` and `DSmooth f` for maps ℝⁿ → X resp. X → Y, and the
D-topology, the finest topology on a diffeological space for which all plots are continuous.

## Implementation notes

Instead of defining diffeologies as collections of plots whose domains are the spaces ℝⁿ, we could
have also equivalently allowed the domains to be open subsets of ℝⁿ, or arbitrary smooth manifolds.
We chose to go with the first option because the latter two can both be somewhat inconvenient to
work with in Lean.

A downside of working only with the spaces ℝⁿ instead of also their subsets is that it makes the
sheaf condition / locality condition of diffeologies somewhat awkward to state and prove; to
mitigate this, we provide `DiffeologicalSpace.mkOfPlotsOn` as a way to construct a diffeology from
plots whose domains are subsets of ℝⁿ.

### D-Topology

Since the D-topology does not always commute with e.g. products, it can not be registered as an
instance - otherwise, there would be two `TopologicalSpace`-instances on binary products, the
product topology of the D-topologies on the factors and the D-topology of the product diffeology.
We thus instead define a typeclass `IsDTopCompatible X` to express when the topology on `X` does
match the D-topology, and also give the D-topology the short name `DTop` to enable use of notations
such as `Continuous[_, DTop]` for continuity with respect to the D-topology.

In order to make it easier to work with diffeological spaces whose natural diffeology does match
the D-topology, we also include the D-topology as part of the data of `DiffeologicalSpace X`.
This allows the diffeologies on e.g. ℝⁿ, manifolds and quotients of diffeological spaces to be
defined in such a way that the D-topology is defeq to the topology that the space already carries.

### Diffeologies on normed spaces
Every normed spaces carries a natural diffeology consisting of all smooth maps from ℝⁿ. While this
"normed space diffeology" does commute with arbitrary products, we can't register it as an instance
because it wouldn't be defeq to the product diffeology on products of normed spaces. We thus only
give it as a definition (`euclideanDiffeology`) instead of an instance, and instead provide a
typeclass `IsContDiffCompatible X` for talking about normed spaces equipped with the normed space
diffeology.

To make working with finite-dimensional spaces easier, `euclideanDiffeology` is defined in such a
way that its D-topology is defeq to the topology induced by the norm - however, this currently comes
at the cost of making the definition work only on finite-dimensional spaces. It should be possible
to extend this to all Banach or Fréchet spaces though in the future.

## References

* [Patrick Iglesias-Zemmour, *Diffeology*][zemmour2013diffeology]
* <https://ncatlab.org/nlab/show/diffeological+space>

## Tags
diffeology, diffeological space, smoothness, smooth function
-/

open Topology ContDiff

/-- The finite-dimensional normed spaces that diffeological spaces are modelled on. We introduce
an abbreviation here because we refer to them quite a lot. -/
abbrev Eucl (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A diffeology on `X`, given by the smooth functions (or "plots") from ℝⁿ to `X`. -/
class DiffeologicalSpace (X : Type*) where
  /-- The plots `Eucl n → X` representing the smooth ways to map `Eucl n` into `X`. This is the main
  piece of data underlying the diffeology. -/
  plots (n : ℕ) : Set (Eucl n → X)
  /-- Every constant map needs to be a plot. -/
  constant_plots {n : ℕ} (x : X) : (fun _ ↦ x) ∈ plots n
  /-- Smooth reparametrisations of plots need to be plots. -/
  plot_reparam {n m : ℕ} {p : Eucl m → X} {f : Eucl n → Eucl m} :
    p ∈ plots m → (ContDiff ℝ ∞ f) → (p ∘ f ∈ plots n)
  /-- Every locally smooth map `Eucl n → X` is a plot. -/
  locality {n : ℕ} {p : Eucl n → X} : (∀ x : Eucl n, ∃ u : Set (Eucl n), IsOpen u ∧ x ∈ u ∧
    ∀ {m : ℕ} {f : Eucl m → Eucl n}, (hfu : ∀ x, f x ∈ u) → ContDiff ℝ ∞ f → p ∘ f ∈ plots m) →
      p ∈ plots n
  /-- The D-topology of the diffeology. This is included as part of the data in order to give
  control over what the D-topology is defeq to. -/
  dTopology : TopologicalSpace X := {
    IsOpen u := ∀ ⦃n : ℕ⦄, ∀ p ∈ plots n, IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ _ ↦ isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp ↦
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp ↦
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu ↦ hs u hu p hp
  }
  /-- The D-topology consists of exactly those sets whose preimages under plots are all open. -/
  isOpen_iff_preimages_plots {u : Set X} : dTopology.IsOpen u ↔
      ∀ {n : ℕ}, ∀ p ∈ plots n, IsOpen (p ⁻¹' u) := by rfl

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

section Defs

/-- D-topology of a diffeological space. This is a definition rather than an instance
because the D-topology might not agree with already registered topologies like the one
on normed spaces. -/
def DTop : TopologicalSpace X := DiffeologicalSpace.dTopology

/-- A map `p : Eucl n → X` is called a plot iff it is part of the diffeology on `X`. This is
equivalent to `p` being smooth with respect to the standard diffeology on `Eucl n`. -/
def IsPlot {n : ℕ} (p : Eucl n → X) : Prop := p ∈ DiffeologicalSpace.plots n

/-- A function between diffeological spaces is smooth iff composition with it preserves
smoothness of plots. -/
@[fun_prop]
def DSmooth (f : X → Y) : Prop := ∀ (n : ℕ) (p : Eucl n → X), IsPlot p → IsPlot (f ∘ p)

/-- Notation for the D-topology of non-standard diffeologies. -/
notation (name := DTop_of) "DTop[" d "]" => @DTop _ d

/-- Notation for the plots of non-standard diffeologies. -/
notation (name := IsPlot_of) "IsPlot[" d "]" => @IsPlot _ d

/-- Notation for smoothness with respect to non-standard diffeologies. -/
notation (name := DSmooth_of) "DSmooth[" d₁ ", " d₂ "]" => @DSmooth _ _ d₁ d₂

end Defs

@[ext]
protected theorem DiffeologicalSpace.ext {X : Type*} {d₁ d₂ : DiffeologicalSpace X}
    (h : IsPlot[d₁] = IsPlot[d₂]) : d₁ = d₂ := by
  cases' d₁ with p₁ _ _ _ t₁ h₁; cases' d₂ with p₂ _ _ _ t₂ h₂
  congr 1; ext s
  exact ((show p₁ = p₂ by exact h) ▸ @h₁ s).trans (@h₂ s).symm

lemma isPlot_const {n : ℕ} {x : X} : IsPlot (fun _ ↦ x : Eucl n → X) :=
  DiffeologicalSpace.constant_plots x

lemma isPlot_reparam {n m : ℕ} {p : Eucl m → X} {f : Eucl n → Eucl m}
    (hp : IsPlot p) (hf : ContDiff ℝ ∞ f) : IsPlot (p ∘ f) :=
  DiffeologicalSpace.plot_reparam hp hf

lemma isOpen_iff_preimages_plots {u : Set X} :
    IsOpen[DTop] u ↔ ∀ (n : ℕ) (p : Eucl n → X), IsPlot p → IsOpen (p ⁻¹' u) :=
  DiffeologicalSpace.isOpen_iff_preimages_plots

protected lemma IsPlot.continuous {n : ℕ} {p : Eucl n → X} (hp : IsPlot p) :
    Continuous[_, DTop] p :=
  continuous_def.2 fun _ hu ↦ isOpen_iff_preimages_plots.1 hu n p hp

protected theorem DSmooth.continuous {f : X → Y} (hf : DSmooth f) : Continuous[DTop, DTop] f := by
  simp_rw [continuous_def, isOpen_iff_preimages_plots (X := X), isOpen_iff_preimages_plots (X := Y)]
  exact fun u hu n p hp ↦ hu n (f ∘ p) (hf n p hp)

theorem dsmooth_iff {f : X → Y} : DSmooth f ↔
    ∀ (n : ℕ) (p : Eucl n → X), IsPlot p → IsPlot (f ∘ p) := by rfl

theorem dsmooth_id : DSmooth (@id X) := by simp [DSmooth]

@[fun_prop]
theorem dsmooth_id' : DSmooth fun x : X ↦ x := dsmooth_id

theorem DSmooth.comp {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (g ∘ f) :=
  fun _ _ hp ↦ hg _ _ (hf _ _ hp)

@[fun_prop]
theorem DSmooth.comp' {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (fun x ↦ g (f x)) := hg.comp hf

@[fun_prop]
theorem dsmooth_const {y : Y} : DSmooth fun _ : X ↦ y :=
  fun _ _ _ ↦ isPlot_const

/-- Replaces the D-topology of a diffeology with another topology equal to it. Useful
to construct diffeologies with better definitional equalities. -/
def DiffeologicalSpace.withDTopology {X : Type*} (d : DiffeologicalSpace X)
    (t : TopologicalSpace X) (h : DTop[d] = t) : DiffeologicalSpace X where
  dTopology := t
  isOpen_iff_preimages_plots := by intro _; rw [← d.isOpen_iff_preimages_plots, ← h]
  __ := d

lemma DiffeologicalSpace.withDTopology_eq {X : Type*} {d : DiffeologicalSpace X}
    {t : TopologicalSpace X} {h : DTop[d] = t} : d.withDTopology t h = d := by
  ext; rfl

/-- A structure with plots specified on open subsets of ℝⁿ rather than ℝⁿ itself. Useful
for constructing diffeologies, as it often makes the locality condition easier to prove. -/
structure DiffeologicalSpace.CorePlotsOn (X : Type*) where
  /-- The predicate determining which maps `u → X` with `u : Set (Eucl n)` open are plots. -/
  isPlotOn {n : ℕ} {u : Set (Eucl n)} (hu : IsOpen u) : (Eucl n → X) → Prop
  isPlotOn_congr {n : ℕ} {u : Set (Eucl n)} (hu : IsOpen u) {p q : Eucl n → X}
    (h : Set.EqOn p q u) : isPlotOn hu p ↔ isPlotOn hu q
  /-- The predicate that the diffeology built from this structure will use. Can be overwritten
    to allow for better definitional equalities. -/
  isPlot {n : ℕ} : (Eucl n → X) → Prop := fun p ↦ isPlotOn isOpen_univ p
  isPlotOn_univ {n : ℕ} {p : Eucl n → X} : isPlotOn isOpen_univ p ↔ isPlot p := by simp
  isPlot_const {n : ℕ} (x : X) : isPlot fun (_ : Eucl n) ↦ x
  isPlotOn_reparam {n m : ℕ} {u : Set (Eucl n)} {v : Set (Eucl m)} {hu : IsOpen u}
    (hv : IsOpen v) {p : Eucl n → X} {f : Eucl m → Eucl n} (h : Set.MapsTo f v u) :
    isPlotOn hu p → ContDiffOn ℝ ∞ f v → isPlotOn hv (p ∘ f)
  /-- The locality axiom of diffeologies, phrased in terms of `isPlotOn`. -/
  locality {n : ℕ} {u : Set (Eucl n)} (hu : IsOpen u) {p : Eucl n → X} :
    (∀ x ∈ u, ∃ (v : Set (Eucl n)) (hv : IsOpen v), x ∈ v ∧ isPlotOn hv p) → isPlotOn hu p
  /-- The D-topology that the diffeology built from this structure will use. Can be overwritten
    to allow for better definitional equalities. -/
  dTopology : TopologicalSpace X := {
    IsOpen u := ∀ ⦃n : ℕ⦄, ∀ p : Eucl n → X, isPlot p → IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ _ ↦ isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp ↦
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp ↦
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu ↦ hs u hu p hp
  }
  isOpen_iff_preimages_plots {u : Set X} : dTopology.IsOpen u ↔
    ∀ {n : ℕ}, ∀ p : Eucl n → X, isPlot p → IsOpen (p ⁻¹' u) := by rfl

/-- Constructs a diffeology from plots defined on open subsets or ℝⁿ rather than ℝⁿ itself,
organised in the form of the auxiliary `CorePlotsOn` structure.
This is more involved in most regards, but also often makes it quite a lot easier to prove
the locality condition. -/
def DiffeologicalSpace.mkOfPlotsOn {X : Type*} (d : CorePlotsOn X) : DiffeologicalSpace X where
  plots _ := {p | d.isPlot p}
  constant_plots _ := d.isPlot_const _
  plot_reparam hp hf := d.isPlotOn_univ.mp <|
    d.isPlotOn_reparam _ (Set.mapsTo_univ _ _) (d.isPlotOn_univ.mpr hp) hf.contDiffOn
  locality {n p} h := by
    dsimp at h
    refine d.isPlotOn_univ.mp <| d.locality _ fun x _ ↦ ?_
    let ⟨u, hu, hxu, hu'⟩ := h x
    let ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp hu x hxu
    have h := hu' (f := PartialHomeomorph.univBall x ε) (fun x' ↦ by
      have h := (PartialHomeomorph.univBall x ε).map_source (x := x')
      rw [PartialHomeomorph.univBall_source, PartialHomeomorph.univBall_target x hε] at h
      exact hε' (h (Set.mem_univ _))) PartialHomeomorph.contDiff_univBall
    have h' := d.isPlotOn_reparam (Metric.isOpen_ball) (Set.mapsTo_univ _ _)
      (d.isPlotOn_univ.mpr h) (PartialHomeomorph.contDiffOn_univBall_symm (c := x) (r := ε))
    refine ⟨_, Metric.isOpen_ball, Metric.mem_ball_self hε, (d.isPlotOn_congr _ ?_).mp h'⟩
    rw [Function.comp_assoc, ← PartialHomeomorph.coe_trans]; apply Set.EqOn.comp_left
    convert (PartialHomeomorph.symm_trans_self (PartialHomeomorph.univBall x ε)).2
    simp [(PartialHomeomorph.univBall_target x hε)]
  dTopology := d.dTopology
  isOpen_iff_preimages_plots := d.isOpen_iff_preimages_plots

section FiniteDimensionalNormedSpace

/-- Diffeology on a finite-dimensional normed space. We make this a definition instead of an
instance because we also want to have product diffeologies as an instance, and having both would
cause instance diamonds on spaces like `Fin n → ℝ`. -/
def euclideanDiffeology {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] : DiffeologicalSpace X :=
  DiffeologicalSpace.mkOfPlotsOn {
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

/-- Technical condition saying that the diffeology on a space is the one coming from
smoothness in the sense of `ContDiff ℝ ∞`. Necessary as a hypothesis for some theorems
because some normed spaces carry a diffeology that is equal but not defeq to the normed space
diffeology (for example the product diffeology in the case of `Fin n → ℝ`), so the information
that these theorems still holds needs to be made available via this typeclass. -/
class IsContDiffCompatible (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [DiffeologicalSpace X] : Prop where
  isPlot_iff {n : ℕ} {p : Eucl n → X} : IsPlot p ↔ ContDiff ℝ ∞ p

/-- Technical condition saying that the topology on a type agrees with the D-topology.
Necessary because the D-topologies on for example products and subspaces don't agree with
the product and subspace topologies. -/
class IsDTopCompatible (X : Type*) [t : TopologicalSpace X] [DiffeologicalSpace X] : Prop where
  dTop_eq : DTop = t

theorem dTop_eq (X : Type*) [t : TopologicalSpace X] [DiffeologicalSpace X] [IsDTopCompatible X] :
    DTop = t := IsDTopCompatible.dTop_eq

/-- A smooth function between spaces that are equipped with the D-topology is continuous. -/
protected theorem DSmooth.continuous' {X Y : Type*} [TopologicalSpace X] [DiffeologicalSpace X]
    [IsDTopCompatible X] [TopologicalSpace Y] [DiffeologicalSpace Y]
    [IsDTopCompatible Y] {f : X → Y} (hf : DSmooth f) : Continuous f :=
  dTop_eq X ▸ dTop_eq Y ▸ hf.continuous

instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] : @IsContDiffCompatible X _ _ euclideanDiffeology :=
  let _ := euclideanDiffeology (X := X); ⟨Iff.rfl⟩

lemma contDiffCompatible_iff_eq_euclideanDiffeology {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [d : DiffeologicalSpace X] :
    IsContDiffCompatible X ↔ d = euclideanDiffeology :=
  ⟨fun _ ↦ by ext n p; exact IsContDiffCompatible.isPlot_iff, fun h ↦ h ▸ inferInstance⟩

instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] : @IsDTopCompatible X _ euclideanDiffeology :=
  let _ := euclideanDiffeology (X := X); ⟨rfl⟩

instance : DiffeologicalSpace ℝ := euclideanDiffeology

example : IsContDiffCompatible ℝ := inferInstance

example : IsDTopCompatible ℝ := inferInstance

noncomputable instance {ι : Type*} [Fintype ι] : DiffeologicalSpace (EuclideanSpace ℝ ι) :=
  euclideanDiffeology

example {ι : Type*} [Fintype ι] : IsContDiffCompatible (EuclideanSpace ℝ ι) := inferInstance

example {ι : Type*} [Fintype ι] : IsDTopCompatible (EuclideanSpace ℝ ι) := inferInstance

protected theorem IsPlot.dsmooth {n : ℕ} {p : Eucl n → X} (hp : IsPlot p) : DSmooth p :=
  fun _ _ ↦ isPlot_reparam hp

protected theorem DSmooth.isPlot {n : ℕ} {p : Eucl n → X} (hp : DSmooth p) : IsPlot p :=
  hp n id <| @contDiff_id ℝ _ (Eucl n) _ _ ∞

theorem isPlot_iff_dsmooth {n : ℕ} {p : Eucl n → X} : IsPlot p ↔ DSmooth p :=
  ⟨IsPlot.dsmooth, DSmooth.isPlot⟩

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [DiffeologicalSpace X]
  [IsContDiffCompatible X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [DiffeologicalSpace Y]
  [IsContDiffCompatible Y]

theorem isPlot_iff_contDiff {n : ℕ} {p : Eucl n → X} : IsPlot p ↔ ContDiff ℝ ∞ p :=
  IsContDiffCompatible.isPlot_iff

protected theorem ContDiff.dsmooth {f : X → Y} (hf: ContDiff ℝ ∞ f) : DSmooth f :=
  fun _ _ hp ↦ isPlot_iff_contDiff.2 (hf.comp (isPlot_iff_contDiff.1 hp))

protected theorem DSmooth.contDiff [FiniteDimensional ℝ X] {f : X → Y} (hf : DSmooth f) :
    ContDiff ℝ ∞ f := by
  let g := toEuclidean (E := X)
  rw [← Function.comp_id f, ← g.symm_comp_self]
  exact (isPlot_iff_contDiff.1 <| hf _ _ (g.symm.contDiff.dsmooth.isPlot)).comp g.contDiff

theorem dsmooth_iff_contDiff [FiniteDimensional ℝ X] {f : X → Y} : DSmooth f ↔ ContDiff ℝ ∞ f :=
  ⟨DSmooth.contDiff, ContDiff.dsmooth⟩

end FiniteDimensionalNormedSpace

/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Equicontinuity of a family of functions

Let `X` be a topological space and `α` a `UniformSpace`. A family of functions `F : ι → X → α`
is said to be *equicontinuous at a point `x₀ : X`* when, for any entourage `U` in `α`, there is a
neighborhood `V` of `x₀` such that, for all `x ∈ V`, and *for all `i`*, `F i x` is `U`-close to
`F i x₀`. In other words, one has `∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x, ∀ i, dist x₀ x < δ → dist (F i x₀) (F i x) < ε`.

`F` is said to be *equicontinuous* if it is equicontinuous at each point.

A closely related concept is that of ***uniform*** *equicontinuity* of a family of functions
`F : ι → β → α` between uniform spaces, which means that, for any entourage `U` in `α`, there is an
entourage `V` in `β` such that, if `x` and `y` are `V`-close, then *for all `i`*, `F i x` and
`F i y` are `U`-close. In other words, one has
`∀ U ∈ 𝓤 α, ∀ᶠ xy in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x y, ∀ i, dist x y < δ → dist (F i x₀) (F i x) < ε`.

## Main definitions

* `EquicontinuousAt`: equicontinuity of a family of functions at a point
* `Equicontinuous`: equicontinuity of a family of functions on the whole domain
* `UniformEquicontinuous`: uniform equicontinuity of a family of functions on the whole domain

We also introduce relative versions, namely `EquicontinuousWithinAt`, `EquicontinuousOn` and
`UniformEquicontinuousOn`, akin to `ContinuousWithinAt`, `ContinuousOn` and `UniformContinuousOn`
respectively.

## Main statements

* `equicontinuous_iff_continuous`: equicontinuity can be expressed as a simple continuity
  condition between well-chosen function spaces. This is really useful for building up the theory.
* `Equicontinuous.closure`: if a set of functions is equicontinuous, its closure
  *for the topology of pointwise convergence* is also equicontinuous.

## Notations

Throughout this file, we use :
- `ι`, `κ` for indexing types
- `X`, `Y`, `Z` for topological spaces
- `α`, `β`, `γ` for uniform spaces

## Implementation details

We choose to express equicontinuity as a properties of indexed families of functions rather
than sets of functions for the following reasons:
- it is really easy to express equicontinuity of `H : Set (X → α)` using our setup: it is just
  equicontinuity of the family `(↑) : ↥H → (X → α)`. On the other hand, going the other way around
  would require working with the range of the family, which is always annoying because it
  introduces useless existentials.
- in most applications, one doesn't work with bare functions but with a more specific hom type
  `hom`. Equicontinuity of a set `H : Set hom` would then have to be expressed as equicontinuity
  of `coe_fn '' H`, which is super annoying to work with. This is much simpler with families,
  because equicontinuity of a family `𝓕 : ι → hom` would simply be expressed as equicontinuity
  of `coe_fn ∘ 𝓕`, which doesn't introduce any nasty existentials.

To simplify statements, we do provide abbreviations `Set.EquicontinuousAt`, `Set.Equicontinuous`
and `Set.UniformEquicontinuous` asserting the corresponding fact about the family
`(↑) : ↥H → (X → α)` where `H : Set (X → α)`. Note however that these won't work for sets of hom
types, and in that case one should go back to the family definition rather than using `Set.image`.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]

## Tags

equicontinuity, uniform convergence, ascoli
-/


section

open UniformSpace Filter Set Uniformity Topology UniformConvergence Function

variable {ι κ X X' Y α α' β β' γ : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
  [uα : UniformSpace α] [uβ : UniformSpace β] [uγ : UniformSpace γ]

/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous at `x₀ : X`* if, for all entourages `U ∈ 𝓤 α`, there is a neighborhood `V` of `x₀`
such that, for all `x ∈ V` and for all `i : ι`, `F i x` is `U`-close to `F i x₀`. -/
def EquicontinuousAt (F : ι → X → α) (x₀ : X) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U

/-- We say that a set `H : Set (X → α)` of functions is equicontinuous at a point if the family
`(↑) : ↥H → (X → α)` is equicontinuous at that point. -/
protected abbrev Set.EquicontinuousAt (H : Set <| X → α) (x₀ : X) : Prop :=
  EquicontinuousAt ((↑) : H → X → α) x₀

/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous at `x₀ : X` within `S : Set X`* if, for all entourages `U ∈ 𝓤 α`, there is a
neighborhood `V` of `x₀` within `S` such that, for all `x ∈ V` and for all `i : ι`, `F i x` is
`U`-close to `F i x₀`. -/
def EquicontinuousWithinAt (F : ι → X → α) (S : Set X) (x₀ : X) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝[S] x₀, ∀ i, (F i x₀, F i x) ∈ U

/-- We say that a set `H : Set (X → α)` of functions is equicontinuous at a point within a subset
if the family `(↑) : ↥H → (X → α)` is equicontinuous at that point within that same subset. -/
protected abbrev Set.EquicontinuousWithinAt (H : Set <| X → α) (S : Set X) (x₀ : X) : Prop :=
  EquicontinuousWithinAt ((↑) : H → X → α) S x₀

/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous* on all of `X` if it is equicontinuous at each point of `X`. -/
def Equicontinuous (F : ι → X → α) : Prop :=
  ∀ x₀, EquicontinuousAt F x₀

/-- We say that a set `H : Set (X → α)` of functions is equicontinuous if the family
`(↑) : ↥H → (X → α)` is equicontinuous. -/
protected abbrev Set.Equicontinuous (H : Set <| X → α) : Prop :=
  Equicontinuous ((↑) : H → X → α)

/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous on `S : Set X`* if it is equicontinuous *within `S`* at each point of `S`. -/
def EquicontinuousOn (F : ι → X → α) (S : Set X) : Prop :=
  ∀ x₀ ∈ S, EquicontinuousWithinAt F S x₀

/-- We say that a set `H : Set (X → α)` of functions is equicontinuous on a subset if the family
`(↑) : ↥H → (X → α)` is equicontinuous on that subset. -/
protected abbrev Set.EquicontinuousOn (H : Set <| X → α) (S : Set X) : Prop :=
  EquicontinuousOn ((↑) : H → X → α) S

/-- A family `F : ι → β → α` of functions between uniform spaces is *uniformly equicontinuous* if,
for all entourages `U ∈ 𝓤 α`, there is an entourage `V ∈ 𝓤 β` such that, whenever `x` and `y` are
`V`-close, we have that, *for all `i : ι`*, `F i x` is `U`-close to `F i y`. -/
def UniformEquicontinuous (F : ι → β → α) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ xy : β × β in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U

/-- We say that a set `H : Set (X → α)` of functions is uniformly equicontinuous if the family
`(↑) : ↥H → (X → α)` is uniformly equicontinuous. -/
protected abbrev Set.UniformEquicontinuous (H : Set <| β → α) : Prop :=
  UniformEquicontinuous ((↑) : H → β → α)

/-- A family `F : ι → β → α` of functions between uniform spaces is
*uniformly equicontinuous on `S : Set β`* if, for all entourages `U ∈ 𝓤 α`, there is a relative
entourage `V ∈ 𝓤 β ⊓ 𝓟 (S ×ˢ S)` such that, whenever `x` and `y` are `V`-close, we have that,
*for all `i : ι`*, `F i x` is `U`-close to `F i y`. -/
def UniformEquicontinuousOn (F : ι → β → α) (S : Set β) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ xy : β × β in 𝓤 β ⊓ 𝓟 (S ×ˢ S), ∀ i, (F i xy.1, F i xy.2) ∈ U

/-- We say that a set `H : Set (X → α)` of functions is uniformly equicontinuous on a subset if the
family `(↑) : ↥H → (X → α)` is uniformly equicontinuous on that subset. -/
protected abbrev Set.UniformEquicontinuousOn (H : Set <| β → α) (S : Set β) : Prop :=
  UniformEquicontinuousOn ((↑) : H → β → α) S

lemma EquicontinuousAt.equicontinuousWithinAt {F : ι → X → α} {x₀ : X} (H : EquicontinuousAt F x₀)
    (S : Set X) : EquicontinuousWithinAt F S x₀ :=
  fun U hU ↦ (H U hU).filter_mono inf_le_left

lemma EquicontinuousWithinAt.mono {F : ι → X → α} {x₀ : X} {S T : Set X}
    (H : EquicontinuousWithinAt F T x₀) (hST : S ⊆ T) : EquicontinuousWithinAt F S x₀ :=
  fun U hU ↦ (H U hU).filter_mono <| nhdsWithin_mono x₀ hST

@[simp] lemma equicontinuousWithinAt_univ (F : ι → X → α) (x₀ : X) :
    EquicontinuousWithinAt F univ x₀ ↔ EquicontinuousAt F x₀ := by
  rw [EquicontinuousWithinAt, EquicontinuousAt, nhdsWithin_univ]

lemma equicontinuousAt_restrict_iff (F : ι → X → α) {S : Set X} (x₀ : S) :
    EquicontinuousAt (S.restrict ∘ F) x₀ ↔ EquicontinuousWithinAt F S x₀ := by
  simp [EquicontinuousWithinAt, EquicontinuousAt,
    ← eventually_nhds_subtype_iff]

lemma Equicontinuous.equicontinuousOn {F : ι → X → α} (H : Equicontinuous F)
    (S : Set X) : EquicontinuousOn F S :=
  fun x _ ↦ (H x).equicontinuousWithinAt S

lemma EquicontinuousOn.mono {F : ι → X → α} {S T : Set X}
    (H : EquicontinuousOn F T) (hST : S ⊆ T) : EquicontinuousOn F S :=
  fun x hx ↦ (H x (hST hx)).mono hST

lemma equicontinuousOn_univ (F : ι → X → α) :
    EquicontinuousOn F univ ↔ Equicontinuous F := by
  simp [EquicontinuousOn, Equicontinuous]

lemma equicontinuous_restrict_iff (F : ι → X → α) {S : Set X} :
    Equicontinuous (S.restrict ∘ F) ↔ EquicontinuousOn F S := by
  simp [Equicontinuous, EquicontinuousOn, equicontinuousAt_restrict_iff]

lemma UniformEquicontinuous.uniformEquicontinuousOn {F : ι → β → α} (H : UniformEquicontinuous F)
    (S : Set β) : UniformEquicontinuousOn F S :=
  fun U hU ↦ (H U hU).filter_mono inf_le_left

lemma UniformEquicontinuousOn.mono {F : ι → β → α} {S T : Set β}
    (H : UniformEquicontinuousOn F T) (hST : S ⊆ T) : UniformEquicontinuousOn F S :=
  fun U hU ↦ (H U hU).filter_mono <| by gcongr

lemma uniformEquicontinuousOn_univ (F : ι → β → α) :
    UniformEquicontinuousOn F univ ↔ UniformEquicontinuous F := by
  simp [UniformEquicontinuousOn, UniformEquicontinuous]

lemma uniformEquicontinuous_restrict_iff (F : ι → β → α) {S : Set β} :
    UniformEquicontinuous (S.restrict ∘ F) ↔ UniformEquicontinuousOn F S := by
  rw [UniformEquicontinuous, UniformEquicontinuousOn]
  conv in _ ⊓ _ => rw [← Subtype.range_val (s := S), ← range_prodMap, ← map_comap]
  rfl

/-!
### Empty index type
-/

@[simp]
lemma equicontinuousAt_empty [h : IsEmpty ι] (F : ι → X → α) (x₀ : X) :
    EquicontinuousAt F x₀ :=
  fun _ _ ↦ Eventually.of_forall (fun _ ↦ h.elim)

@[simp]
lemma equicontinuousWithinAt_empty [h : IsEmpty ι] (F : ι → X → α) (S : Set X) (x₀ : X) :
    EquicontinuousWithinAt F S x₀ :=
  fun _ _ ↦ Eventually.of_forall (fun _ ↦ h.elim)

@[simp]
lemma equicontinuous_empty [IsEmpty ι] (F : ι → X → α) :
    Equicontinuous F :=
  equicontinuousAt_empty F

@[simp]
lemma equicontinuousOn_empty [IsEmpty ι] (F : ι → X → α) (S : Set X) :
    EquicontinuousOn F S :=
  fun x₀ _ ↦ equicontinuousWithinAt_empty F S x₀

@[simp]
lemma uniformEquicontinuous_empty [h : IsEmpty ι] (F : ι → β → α) :
    UniformEquicontinuous F :=
  fun _ _ ↦ Eventually.of_forall (fun _ ↦ h.elim)

@[simp]
lemma uniformEquicontinuousOn_empty [h : IsEmpty ι] (F : ι → β → α) (S : Set β) :
    UniformEquicontinuousOn F S :=
  fun _ _ ↦ Eventually.of_forall (fun _ ↦ h.elim)

/-!
### Finite index type
-/

theorem equicontinuousAt_finite [Finite ι] {F : ι → X → α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔ ∀ i, ContinuousAt (F i) x₀ := by
  simp [EquicontinuousAt, ContinuousAt, (nhds_basis_uniformity' (𝓤 α).basis_sets).tendsto_right_iff,
    UniformSpace.ball, @forall_swap _ ι]

theorem equicontinuousWithinAt_finite [Finite ι] {F : ι → X → α} {S : Set X} {x₀ : X} :
    EquicontinuousWithinAt F S x₀ ↔ ∀ i, ContinuousWithinAt (F i) S x₀ := by
  simp [EquicontinuousWithinAt, ContinuousWithinAt,
    (nhds_basis_uniformity' (𝓤 α).basis_sets).tendsto_right_iff, UniformSpace.ball,
    @forall_swap _ ι]

theorem equicontinuous_finite [Finite ι] {F : ι → X → α} :
    Equicontinuous F ↔ ∀ i, Continuous (F i) := by
  simp only [Equicontinuous, equicontinuousAt_finite, continuous_iff_continuousAt, @forall_swap ι]

theorem equicontinuousOn_finite [Finite ι] {F : ι → X → α} {S : Set X} :
    EquicontinuousOn F S ↔ ∀ i, ContinuousOn (F i) S := by
  simp only [EquicontinuousOn, equicontinuousWithinAt_finite, ContinuousOn, @forall_swap ι]

theorem uniformEquicontinuous_finite [Finite ι] {F : ι → β → α} :
    UniformEquicontinuous F ↔ ∀ i, UniformContinuous (F i) := by
  simp only [UniformEquicontinuous, eventually_all, @forall_swap _ ι]; rfl

theorem uniformEquicontinuousOn_finite [Finite ι] {F : ι → β → α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ ∀ i, UniformContinuousOn (F i) S := by
  simp only [UniformEquicontinuousOn, eventually_all, @forall_swap _ ι]; rfl

/-!
### Index type with a unique element
-/

theorem equicontinuousAt_unique [Unique ι] {F : ι → X → α} {x : X} :
    EquicontinuousAt F x ↔ ContinuousAt (F default) x :=
  equicontinuousAt_finite.trans Unique.forall_iff

theorem equicontinuousWithinAt_unique [Unique ι] {F : ι → X → α} {S : Set X} {x : X} :
    EquicontinuousWithinAt F S x ↔ ContinuousWithinAt (F default) S x :=
  equicontinuousWithinAt_finite.trans Unique.forall_iff

theorem equicontinuous_unique [Unique ι] {F : ι → X → α} :
    Equicontinuous F ↔ Continuous (F default) :=
  equicontinuous_finite.trans Unique.forall_iff

theorem equicontinuousOn_unique [Unique ι] {F : ι → X → α} {S : Set X} :
    EquicontinuousOn F S ↔ ContinuousOn (F default) S :=
  equicontinuousOn_finite.trans Unique.forall_iff

theorem uniformEquicontinuous_unique [Unique ι] {F : ι → β → α} :
    UniformEquicontinuous F ↔ UniformContinuous (F default) :=
  uniformEquicontinuous_finite.trans Unique.forall_iff

theorem uniformEquicontinuousOn_unique [Unique ι] {F : ι → β → α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ UniformContinuousOn (F default) S :=
  uniformEquicontinuousOn_finite.trans Unique.forall_iff

/-- Reformulation of equicontinuity at `x₀` within a set `S`, comparing two variables near `x₀`
instead of comparing only one with `x₀`. -/
theorem equicontinuousWithinAt_iff_pair {F : ι → X → α} {S : Set X} {x₀ : X} (hx₀ : x₀ ∈ S) :
    EquicontinuousWithinAt F S x₀ ↔
      ∀ U ∈ 𝓤 α, ∃ V ∈ 𝓝[S] x₀, ∀ x ∈ V, ∀ y ∈ V, ∀ i, (F i x, F i y) ∈ U := by
  constructor <;> intro H U hU
  · rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
    refine ⟨_, H V hV, fun x hx y hy i ↦ hVU (prodMk_mem_compRel ?_ (hy i))⟩
    exact hVsymm.mk_mem_comm.mp (hx i)
  · rcases H U hU with ⟨V, hV, hVU⟩
    filter_upwards [hV] using fun x hx i ↦ hVU x₀ (mem_of_mem_nhdsWithin hx₀ hV) x hx i

/-- Reformulation of equicontinuity at `x₀` comparing two variables near `x₀` instead of comparing
only one with `x₀`. -/
theorem equicontinuousAt_iff_pair {F : ι → X → α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔
      ∀ U ∈ 𝓤 α, ∃ V ∈ 𝓝 x₀, ∀ x ∈ V, ∀ y ∈ V, ∀ i, (F i x, F i y) ∈ U := by
  simp_rw [← equicontinuousWithinAt_univ, equicontinuousWithinAt_iff_pair (mem_univ x₀),
    nhdsWithin_univ]

/-- Uniform equicontinuity implies equicontinuity. -/
theorem UniformEquicontinuous.equicontinuous {F : ι → β → α} (h : UniformEquicontinuous F) :
    Equicontinuous F := fun x₀ U hU ↦
  mem_of_superset (ball_mem_nhds x₀ (h U hU)) fun _ hx i ↦ hx i

/-- Uniform equicontinuity on a subset implies equicontinuity on that subset. -/
theorem UniformEquicontinuousOn.equicontinuousOn {F : ι → β → α} {S : Set β}
    (h : UniformEquicontinuousOn F S) :
    EquicontinuousOn F S := fun _ hx₀ U hU ↦
  mem_of_superset (ball_mem_nhdsWithin hx₀ (h U hU)) fun _ hx i ↦ hx i

/-- Each function of a family equicontinuous at `x₀` is continuous at `x₀`. -/
theorem EquicontinuousAt.continuousAt {F : ι → X → α} {x₀ : X} (h : EquicontinuousAt F x₀) (i : ι) :
    ContinuousAt (F i) x₀ :=
  (UniformSpace.hasBasis_nhds _).tendsto_right_iff.2 fun U ⟨hU, _⟩ ↦ (h U hU).mono fun _x hx ↦ hx i

/-- Each function of a family equicontinuous at `x₀` within `S` is continuous at `x₀` within `S`. -/
theorem EquicontinuousWithinAt.continuousWithinAt {F : ι → X → α} {S : Set X} {x₀ : X}
    (h : EquicontinuousWithinAt F S x₀) (i : ι) :
    ContinuousWithinAt (F i) S x₀ :=
  (UniformSpace.hasBasis_nhds _).tendsto_right_iff.2 fun U ⟨hU, _⟩ ↦ (h U hU).mono fun _x hx ↦ hx i

protected theorem Set.EquicontinuousAt.continuousAt_of_mem {H : Set <| X → α} {x₀ : X}
    (h : H.EquicontinuousAt x₀) {f : X → α} (hf : f ∈ H) : ContinuousAt f x₀ :=
  h.continuousAt ⟨f, hf⟩

protected theorem Set.EquicontinuousWithinAt.continuousWithinAt_of_mem {H : Set <| X → α}
    {S : Set X} {x₀ : X} (h : H.EquicontinuousWithinAt S x₀) {f : X → α} (hf : f ∈ H) :
    ContinuousWithinAt f S x₀ :=
  h.continuousWithinAt ⟨f, hf⟩

/-- Each function of an equicontinuous family is continuous. -/
theorem Equicontinuous.continuous {F : ι → X → α} (h : Equicontinuous F) (i : ι) :
    Continuous (F i) :=
  continuous_iff_continuousAt.mpr fun x ↦ (h x).continuousAt i

/-- Each function of a family equicontinuous on `S` is continuous on `S`. -/
theorem EquicontinuousOn.continuousOn {F : ι → X → α} {S : Set X} (h : EquicontinuousOn F S)
    (i : ι) : ContinuousOn (F i) S :=
  fun x hx ↦ (h x hx).continuousWithinAt i

protected theorem Set.Equicontinuous.continuous_of_mem {H : Set <| X → α} (h : H.Equicontinuous)
    {f : X → α} (hf : f ∈ H) : Continuous f :=
  h.continuous ⟨f, hf⟩

protected theorem Set.EquicontinuousOn.continuousOn_of_mem {H : Set <| X → α} {S : Set X}
    (h : H.EquicontinuousOn S) {f : X → α} (hf : f ∈ H) : ContinuousOn f S :=
  h.continuousOn ⟨f, hf⟩

/-- Each function of a uniformly equicontinuous family is uniformly continuous. -/
theorem UniformEquicontinuous.uniformContinuous {F : ι → β → α} (h : UniformEquicontinuous F)
    (i : ι) : UniformContinuous (F i) := fun U hU ↦
  mem_map.mpr (mem_of_superset (h U hU) fun _ hxy ↦ hxy i)

/-- Each function of a family uniformly equicontinuous on `S` is uniformly continuous on `S`. -/
theorem UniformEquicontinuousOn.uniformContinuousOn {F : ι → β → α} {S : Set β}
    (h : UniformEquicontinuousOn F S) (i : ι) :
    UniformContinuousOn (F i) S := fun U hU ↦
  mem_map.mpr (mem_of_superset (h U hU) fun _ hxy ↦ hxy i)

protected theorem Set.UniformEquicontinuous.uniformContinuous_of_mem {H : Set <| β → α}
    (h : H.UniformEquicontinuous) {f : β → α} (hf : f ∈ H) : UniformContinuous f :=
  h.uniformContinuous ⟨f, hf⟩

protected theorem Set.UniformEquicontinuousOn.uniformContinuousOn_of_mem {H : Set <| β → α}
    {S : Set β} (h : H.UniformEquicontinuousOn S) {f : β → α} (hf : f ∈ H) :
    UniformContinuousOn f S :=
  h.uniformContinuousOn ⟨f, hf⟩

/-- Taking sub-families preserves equicontinuity at a point. -/
theorem EquicontinuousAt.comp {F : ι → X → α} {x₀ : X} (h : EquicontinuousAt F x₀) (u : κ → ι) :
    EquicontinuousAt (F ∘ u) x₀ := fun U hU ↦ (h U hU).mono fun _ H k ↦ H (u k)

/-- Taking sub-families preserves equicontinuity at a point within a subset. -/
theorem EquicontinuousWithinAt.comp {F : ι → X → α} {S : Set X} {x₀ : X}
    (h : EquicontinuousWithinAt F S x₀) (u : κ → ι) :
    EquicontinuousWithinAt (F ∘ u) S x₀ :=
  fun U hU ↦ (h U hU).mono fun _ H k ↦ H (u k)

protected theorem Set.EquicontinuousAt.mono {H H' : Set <| X → α} {x₀ : X}
    (h : H.EquicontinuousAt x₀) (hH : H' ⊆ H) : H'.EquicontinuousAt x₀ :=
  h.comp (inclusion hH)

protected theorem Set.EquicontinuousWithinAt.mono {H H' : Set <| X → α} {S : Set X} {x₀ : X}
    (h : H.EquicontinuousWithinAt S x₀) (hH : H' ⊆ H) : H'.EquicontinuousWithinAt S x₀ :=
  h.comp (inclusion hH)

/-- Taking sub-families preserves equicontinuity. -/
theorem Equicontinuous.comp {F : ι → X → α} (h : Equicontinuous F) (u : κ → ι) :
    Equicontinuous (F ∘ u) := fun x ↦ (h x).comp u

/-- Taking sub-families preserves equicontinuity on a subset. -/
theorem EquicontinuousOn.comp {F : ι → X → α} {S : Set X} (h : EquicontinuousOn F S) (u : κ → ι) :
    EquicontinuousOn (F ∘ u) S := fun x hx ↦ (h x hx).comp u

protected theorem Set.Equicontinuous.mono {H H' : Set <| X → α} (h : H.Equicontinuous)
    (hH : H' ⊆ H) : H'.Equicontinuous :=
  h.comp (inclusion hH)

protected theorem Set.EquicontinuousOn.mono {H H' : Set <| X → α} {S : Set X}
    (h : H.EquicontinuousOn S) (hH : H' ⊆ H) : H'.EquicontinuousOn S :=
  h.comp (inclusion hH)

/-- Taking sub-families preserves uniform equicontinuity. -/
theorem UniformEquicontinuous.comp {F : ι → β → α} (h : UniformEquicontinuous F) (u : κ → ι) :
    UniformEquicontinuous (F ∘ u) := fun U hU ↦ (h U hU).mono fun _ H k ↦ H (u k)

/-- Taking sub-families preserves uniform equicontinuity on a subset. -/
theorem UniformEquicontinuousOn.comp {F : ι → β → α} {S : Set β} (h : UniformEquicontinuousOn F S)
    (u : κ → ι) : UniformEquicontinuousOn (F ∘ u) S :=
  fun U hU ↦ (h U hU).mono fun _ H k ↦ H (u k)

protected theorem Set.UniformEquicontinuous.mono {H H' : Set <| β → α} (h : H.UniformEquicontinuous)
    (hH : H' ⊆ H) : H'.UniformEquicontinuous :=
  h.comp (inclusion hH)

protected theorem Set.UniformEquicontinuousOn.mono {H H' : Set <| β → α} {S : Set β}
    (h : H.UniformEquicontinuousOn S) (hH : H' ⊆ H) : H'.UniformEquicontinuousOn S :=
  h.comp (inclusion hH)

/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` iff `range 𝓕` is equicontinuous at `x₀`,
i.e the family `(↑) : range F → X → α` is equicontinuous at `x₀`. -/
theorem equicontinuousAt_iff_range {F : ι → X → α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔ EquicontinuousAt ((↑) : range F → X → α) x₀ := by
  simp only [EquicontinuousAt, forall_subtype_range_iff]

/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` within `S` iff `range 𝓕` is equicontinuous
at `x₀` within `S`, i.e the family `(↑) : range F → X → α` is equicontinuous at `x₀` within `S`. -/
theorem equicontinuousWithinAt_iff_range {F : ι → X → α} {S : Set X} {x₀ : X} :
    EquicontinuousWithinAt F S x₀ ↔ EquicontinuousWithinAt ((↑) : range F → X → α) S x₀ := by
  simp only [EquicontinuousWithinAt, forall_subtype_range_iff]

/-- A family `𝓕 : ι → X → α` is equicontinuous iff `range 𝓕` is equicontinuous,
i.e the family `(↑) : range F → X → α` is equicontinuous. -/
theorem equicontinuous_iff_range {F : ι → X → α} :
    Equicontinuous F ↔ Equicontinuous ((↑) : range F → X → α) :=
  forall_congr' fun _ ↦ equicontinuousAt_iff_range

/-- A family `𝓕 : ι → X → α` is equicontinuous on `S` iff `range 𝓕` is equicontinuous on `S`,
i.e the family `(↑) : range F → X → α` is equicontinuous on `S`. -/
theorem equicontinuousOn_iff_range {F : ι → X → α} {S : Set X} :
    EquicontinuousOn F S ↔ EquicontinuousOn ((↑) : range F → X → α) S :=
  forall_congr' fun _ ↦ forall_congr' fun _ ↦ equicontinuousWithinAt_iff_range

/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous iff `range 𝓕` is uniformly equicontinuous,
i.e the family `(↑) : range F → β → α` is uniformly equicontinuous. -/
theorem uniformEquicontinuous_iff_range {F : ι → β → α} :
    UniformEquicontinuous F ↔ UniformEquicontinuous ((↑) : range F → β → α) :=
  ⟨fun h ↦ by rw [← comp_rangeSplitting F]; exact h.comp _, fun h ↦
    h.comp (rangeFactorization F)⟩

/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous on `S` iff `range 𝓕` is uniformly
equicontinuous on `S`, i.e the family `(↑) : range F → β → α` is uniformly equicontinuous on `S`. -/
theorem uniformEquicontinuousOn_iff_range {F : ι → β → α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ UniformEquicontinuousOn ((↑) : range F → β → α) S :=
  ⟨fun h ↦ by rw [← comp_rangeSplitting F]; exact h.comp _, fun h ↦
    h.comp (rangeFactorization F)⟩

section

open UniformFun

/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` iff the function `swap 𝓕 : X → ι → α` is
continuous at `x₀` *when `ι → α` is equipped with the topology of uniform convergence*. This is
very useful for developing the equicontinuity API, but it should not be used directly for other
purposes. -/
theorem equicontinuousAt_iff_continuousAt {F : ι → X → α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔ ContinuousAt (ofFun ∘ Function.swap F : X → ι →ᵤ α) x₀ := by
  rw [ContinuousAt, (UniformFun.hasBasis_nhds ι α _).tendsto_right_iff]
  rfl

/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` within `S` iff the function
`swap 𝓕 : X → ι → α` is continuous at `x₀` within `S`
*when `ι → α` is equipped with the topology of uniform convergence*. This is very useful for
developing the equicontinuity API, but it should not be used directly for other purposes. -/
theorem equicontinuousWithinAt_iff_continuousWithinAt {F : ι → X → α} {S : Set X} {x₀ : X} :
    EquicontinuousWithinAt F S x₀ ↔
    ContinuousWithinAt (ofFun ∘ Function.swap F : X → ι →ᵤ α) S x₀ := by
  rw [ContinuousWithinAt, (UniformFun.hasBasis_nhds ι α _).tendsto_right_iff]
  rfl

/-- A family `𝓕 : ι → X → α` is equicontinuous iff the function `swap 𝓕 : X → ι → α` is
continuous *when `ι → α` is equipped with the topology of uniform convergence*. This is
very useful for developing the equicontinuity API, but it should not be used directly for other
purposes. -/
theorem equicontinuous_iff_continuous {F : ι → X → α} :
    Equicontinuous F ↔ Continuous (ofFun ∘ Function.swap F : X → ι →ᵤ α) := by
  simp_rw [Equicontinuous, continuous_iff_continuousAt, equicontinuousAt_iff_continuousAt]

/-- A family `𝓕 : ι → X → α` is equicontinuous on `S` iff the function `swap 𝓕 : X → ι → α` is
continuous on `S` *when `ι → α` is equipped with the topology of uniform convergence*. This is
very useful for developing the equicontinuity API, but it should not be used directly for other
purposes. -/
theorem equicontinuousOn_iff_continuousOn {F : ι → X → α} {S : Set X} :
    EquicontinuousOn F S ↔ ContinuousOn (ofFun ∘ Function.swap F : X → ι →ᵤ α) S := by
  simp_rw [EquicontinuousOn, ContinuousOn, equicontinuousWithinAt_iff_continuousWithinAt]

/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous iff the function `swap 𝓕 : β → ι → α` is
uniformly continuous *when `ι → α` is equipped with the uniform structure of uniform convergence*.
This is very useful for developing the equicontinuity API, but it should not be used directly
for other purposes. -/
theorem uniformEquicontinuous_iff_uniformContinuous {F : ι → β → α} :
    UniformEquicontinuous F ↔ UniformContinuous (ofFun ∘ Function.swap F : β → ι →ᵤ α) := by
  rw [UniformContinuous, (UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl

/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous on `S` iff the function
`swap 𝓕 : β → ι → α` is uniformly continuous on `S`
*when `ι → α` is equipped with the uniform structure of uniform convergence*. This is very useful
for developing the equicontinuity API, but it should not be used directly for other purposes. -/
theorem uniformEquicontinuousOn_iff_uniformContinuousOn {F : ι → β → α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ UniformContinuousOn (ofFun ∘ Function.swap F : β → ι →ᵤ α) S := by
  rw [UniformContinuousOn, (UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl

theorem equicontinuousWithinAt_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'}
    {S : Set X} {x₀ : X} : EquicontinuousWithinAt (uα :=  ⨅ k, u k) F S x₀ ↔
      ∀ k, EquicontinuousWithinAt (uα :=  u k) F S x₀ := by
  simp only [equicontinuousWithinAt_iff_continuousWithinAt (uα := _), topologicalSpace]
  unfold ContinuousWithinAt
  rw [UniformFun.iInf_eq, toTopologicalSpace_iInf, nhds_iInf, tendsto_iInf]

theorem equicontinuousAt_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'}
    {x₀ : X} :
    EquicontinuousAt (uα := ⨅ k, u k) F x₀ ↔ ∀ k, EquicontinuousAt (uα := u k) F x₀ := by
  simp only [← equicontinuousWithinAt_univ (uα := _), equicontinuousWithinAt_iInf_rng]

theorem equicontinuous_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'} :
    Equicontinuous (uα := ⨅ k, u k) F ↔ ∀ k, Equicontinuous (uα := u k) F := by
  simp_rw [equicontinuous_iff_continuous (uα := _), UniformFun.topologicalSpace]
  rw [UniformFun.iInf_eq, toTopologicalSpace_iInf, continuous_iInf_rng]

theorem equicontinuousOn_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'}
    {S : Set X} :
    EquicontinuousOn (uα := ⨅ k, u k) F S ↔ ∀ k, EquicontinuousOn (uα := u k) F S := by
  simp_rw [EquicontinuousOn, equicontinuousWithinAt_iInf_rng, @forall_swap _ κ]

theorem uniformEquicontinuous_iInf_rng {u : κ → UniformSpace α'} {F : ι → β → α'} :
    UniformEquicontinuous (uα := ⨅ k, u k) F ↔ ∀ k, UniformEquicontinuous (uα := u k) F := by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uα := _)]
  rw [UniformFun.iInf_eq, uniformContinuous_iInf_rng]

theorem uniformEquicontinuousOn_iInf_rng {u : κ → UniformSpace α'} {F : ι → β → α'}
    {S : Set β} : UniformEquicontinuousOn (uα := ⨅ k, u k) F S ↔
      ∀ k, UniformEquicontinuousOn (uα := u k) F S := by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uα := _)]
  unfold UniformContinuousOn
  rw [UniformFun.iInf_eq, iInf_uniformity, tendsto_iInf]

theorem equicontinuousWithinAt_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {S : Set X'} {x₀ : X'} {k : κ} (hk : EquicontinuousWithinAt (tX := t k) F S x₀) :
    EquicontinuousWithinAt (tX := ⨅ k, t k) F S x₀ := by
  simp only [equicontinuousWithinAt_iff_continuousWithinAt (tX := _)] at hk ⊢
  unfold ContinuousWithinAt nhdsWithin at hk ⊢
  rw [nhds_iInf]
  exact hk.mono_left <| inf_le_inf_right _ <| iInf_le _ k

theorem equicontinuousAt_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {x₀ : X'} {k : κ} (hk : EquicontinuousAt (tX := t k) F x₀) :
    EquicontinuousAt (tX := ⨅ k, t k) F x₀ := by
  rw [← equicontinuousWithinAt_univ (tX := _)] at hk ⊢
  exact equicontinuousWithinAt_iInf_dom hk

theorem equicontinuous_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {k : κ} (hk : Equicontinuous (tX := t k) F) :
    Equicontinuous (tX := ⨅ k, t k) F :=
  fun x ↦ equicontinuousAt_iInf_dom (hk x)

theorem equicontinuousOn_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {S : Set X'} {k : κ} (hk : EquicontinuousOn (tX := t k) F S) :
    EquicontinuousOn (tX := ⨅ k, t k) F S :=
  fun x hx ↦ equicontinuousWithinAt_iInf_dom (hk x hx)

theorem uniformEquicontinuous_iInf_dom {u : κ → UniformSpace β'} {F : ι → β' → α}
    {k : κ} (hk : UniformEquicontinuous (uβ := u k) F) :
    UniformEquicontinuous (uβ := ⨅ k, u k) F := by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uβ := _)] at hk ⊢
  exact uniformContinuous_iInf_dom hk

theorem uniformEquicontinuousOn_iInf_dom {u : κ → UniformSpace β'} {F : ι → β' → α}
    {S : Set β'} {k : κ} (hk : UniformEquicontinuousOn (uβ := u k) F S) :
    UniformEquicontinuousOn (uβ := ⨅ k, u k) F S := by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uβ := _)] at hk ⊢
  unfold UniformContinuousOn
  rw [iInf_uniformity]
  exact hk.mono_left <| inf_le_inf_right _ <| iInf_le _ k

theorem Filter.HasBasis.equicontinuousAt_iff_left {p : κ → Prop} {s : κ → Set X}
    {F : ι → X → α} {x₀ : X} (hX : (𝓝 x₀).HasBasis p s) :
    EquicontinuousAt F x₀ ↔ ∀ U ∈ 𝓤 α, ∃ k, p k ∧ ∀ x ∈ s k, ∀ i, (F i x₀, F i x) ∈ U := by
  rw [equicontinuousAt_iff_continuousAt, ContinuousAt,
    hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl

theorem Filter.HasBasis.equicontinuousWithinAt_iff_left {p : κ → Prop} {s : κ → Set X}
    {F : ι → X → α} {S : Set X} {x₀ : X} (hX : (𝓝[S] x₀).HasBasis p s) :
    EquicontinuousWithinAt F S x₀ ↔ ∀ U ∈ 𝓤 α, ∃ k, p k ∧ ∀ x ∈ s k, ∀ i, (F i x₀, F i x) ∈ U := by
  rw [equicontinuousWithinAt_iff_continuousWithinAt, ContinuousWithinAt,
    hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl

theorem Filter.HasBasis.equicontinuousAt_iff_right {p : κ → Prop} {s : κ → Set (α × α)}
    {F : ι → X → α} {x₀ : X} (hα : (𝓤 α).HasBasis p s) :
    EquicontinuousAt F x₀ ↔ ∀ k, p k → ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ s k := by
  rw [equicontinuousAt_iff_continuousAt, ContinuousAt,
    (UniformFun.hasBasis_nhds_of_basis ι α _ hα).tendsto_right_iff]
  rfl

theorem Filter.HasBasis.equicontinuousWithinAt_iff_right {p : κ → Prop}
    {s : κ → Set (α × α)} {F : ι → X → α} {S : Set X} {x₀ : X} (hα : (𝓤 α).HasBasis p s) :
    EquicontinuousWithinAt F S x₀ ↔ ∀ k, p k → ∀ᶠ x in 𝓝[S] x₀, ∀ i, (F i x₀, F i x) ∈ s k := by
  rw [equicontinuousWithinAt_iff_continuousWithinAt, ContinuousWithinAt,
    (UniformFun.hasBasis_nhds_of_basis ι α _ hα).tendsto_right_iff]
  rfl

theorem Filter.HasBasis.equicontinuousAt_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop} {s₁ : κ₁ → Set X}
    {p₂ : κ₂ → Prop} {s₂ : κ₂ → Set (α × α)} {F : ι → X → α} {x₀ : X} (hX : (𝓝 x₀).HasBasis p₁ s₁)
    (hα : (𝓤 α).HasBasis p₂ s₂) :
    EquicontinuousAt F x₀ ↔
      ∀ k₂, p₂ k₂ → ∃ k₁, p₁ k₁ ∧ ∀ x ∈ s₁ k₁, ∀ i, (F i x₀, F i x) ∈ s₂ k₂ := by
  rw [equicontinuousAt_iff_continuousAt, ContinuousAt,
    hX.tendsto_iff (UniformFun.hasBasis_nhds_of_basis ι α _ hα)]
  rfl

theorem Filter.HasBasis.equicontinuousWithinAt_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop}
    {s₁ : κ₁ → Set X} {p₂ : κ₂ → Prop} {s₂ : κ₂ → Set (α × α)} {F : ι → X → α} {S : Set X} {x₀ : X}
    (hX : (𝓝[S] x₀).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) :
    EquicontinuousWithinAt F S x₀ ↔
      ∀ k₂, p₂ k₂ → ∃ k₁, p₁ k₁ ∧ ∀ x ∈ s₁ k₁, ∀ i, (F i x₀, F i x) ∈ s₂ k₂ := by
  rw [equicontinuousWithinAt_iff_continuousWithinAt, ContinuousWithinAt,
    hX.tendsto_iff (UniformFun.hasBasis_nhds_of_basis ι α _ hα)]
  rfl

theorem Filter.HasBasis.uniformEquicontinuous_iff_left {p : κ → Prop}
    {s : κ → Set (β × β)} {F : ι → β → α} (hβ : (𝓤 β).HasBasis p s) :
    UniformEquicontinuous F ↔
      ∀ U ∈ 𝓤 α, ∃ k, p k ∧ ∀ x y, (x, y) ∈ s k → ∀ i, (F i x, F i y) ∈ U := by
  rw [uniformEquicontinuous_iff_uniformContinuous, UniformContinuous,
    hβ.tendsto_iff (UniformFun.hasBasis_uniformity ι α)]
  simp only [Prod.forall]
  rfl

theorem Filter.HasBasis.uniformEquicontinuousOn_iff_left {p : κ → Prop}
    {s : κ → Set (β × β)} {F : ι → β → α} {S : Set β} (hβ : (𝓤 β ⊓ 𝓟 (S ×ˢ S)).HasBasis p s) :
    UniformEquicontinuousOn F S ↔
      ∀ U ∈ 𝓤 α, ∃ k, p k ∧ ∀ x y, (x, y) ∈ s k → ∀ i, (F i x, F i y) ∈ U := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn, UniformContinuousOn,
    hβ.tendsto_iff (UniformFun.hasBasis_uniformity ι α)]
  simp only [Prod.forall]
  rfl

theorem Filter.HasBasis.uniformEquicontinuous_iff_right {p : κ → Prop}
    {s : κ → Set (α × α)} {F : ι → β → α} (hα : (𝓤 α).HasBasis p s) :
    UniformEquicontinuous F ↔ ∀ k, p k → ∀ᶠ xy : β × β in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ s k := by
  rw [uniformEquicontinuous_iff_uniformContinuous, UniformContinuous,
    (UniformFun.hasBasis_uniformity_of_basis ι α hα).tendsto_right_iff]
  rfl

theorem Filter.HasBasis.uniformEquicontinuousOn_iff_right {p : κ → Prop}
    {s : κ → Set (α × α)} {F : ι → β → α} {S : Set β} (hα : (𝓤 α).HasBasis p s) :
    UniformEquicontinuousOn F S ↔
      ∀ k, p k → ∀ᶠ xy : β × β in 𝓤 β ⊓ 𝓟 (S ×ˢ S), ∀ i, (F i xy.1, F i xy.2) ∈ s k := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn, UniformContinuousOn,
    (UniformFun.hasBasis_uniformity_of_basis ι α hα).tendsto_right_iff]
  rfl

theorem Filter.HasBasis.uniformEquicontinuous_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop}
    {s₁ : κ₁ → Set (β × β)} {p₂ : κ₂ → Prop} {s₂ : κ₂ → Set (α × α)} {F : ι → β → α}
    (hβ : (𝓤 β).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) :
    UniformEquicontinuous F ↔
      ∀ k₂, p₂ k₂ → ∃ k₁, p₁ k₁ ∧ ∀ x y, (x, y) ∈ s₁ k₁ → ∀ i, (F i x, F i y) ∈ s₂ k₂ := by
  rw [uniformEquicontinuous_iff_uniformContinuous, UniformContinuous,
    hβ.tendsto_iff (UniformFun.hasBasis_uniformity_of_basis ι α hα)]
  simp only [Prod.forall]
  rfl

theorem Filter.HasBasis.uniformEquicontinuousOn_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop}
    {s₁ : κ₁ → Set (β × β)} {p₂ : κ₂ → Prop} {s₂ : κ₂ → Set (α × α)} {F : ι → β → α}
    {S : Set β} (hβ : (𝓤 β ⊓ 𝓟 (S ×ˢ S)).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) :
    UniformEquicontinuousOn F S ↔
      ∀ k₂, p₂ k₂ → ∃ k₁, p₁ k₁ ∧ ∀ x y, (x, y) ∈ s₁ k₁ → ∀ i, (F i x, F i y) ∈ s₂ k₂ := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn, UniformContinuousOn,
    hβ.tendsto_iff (UniformFun.hasBasis_uniformity_of_basis ι α hα)]
  simp only [Prod.forall]
  rfl

/-- Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontinuous at a point
`x₀ : X` iff the family `𝓕'`, obtained by composing each function of `𝓕` by `u`, is
equicontinuous at `x₀`. -/
theorem IsUniformInducing.equicontinuousAt_iff {F : ι → X → α} {x₀ : X} {u : α → β}
    (hu : IsUniformInducing u) : EquicontinuousAt F x₀ ↔ EquicontinuousAt ((u ∘ ·) ∘ F) x₀ := by
  have := (UniformFun.postcomp_isUniformInducing (α := ι) hu).isInducing
  rw [equicontinuousAt_iff_continuousAt, equicontinuousAt_iff_continuousAt, this.continuousAt_iff]
  rfl

/-- Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontinuous at a point
`x₀ : X` within a subset `S : Set X` iff the family `𝓕'`, obtained by composing each function
of `𝓕` by `u`, is equicontinuous at `x₀` within `S`. -/
lemma IsUniformInducing.equicontinuousWithinAt_iff {F : ι → X → α} {S : Set X} {x₀ : X} {u : α → β}
    (hu : IsUniformInducing u) : EquicontinuousWithinAt F S x₀ ↔
      EquicontinuousWithinAt ((u ∘ ·) ∘ F) S x₀ := by
  have := (UniformFun.postcomp_isUniformInducing (α := ι) hu).isInducing
  simp only [equicontinuousWithinAt_iff_continuousWithinAt, this.continuousWithinAt_iff]
  rfl

/-- Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontinuous iff the
family `𝓕'`, obtained by composing each function of `𝓕` by `u`, is equicontinuous. -/
lemma IsUniformInducing.equicontinuous_iff {F : ι → X → α} {u : α → β} (hu : IsUniformInducing u) :
    Equicontinuous F ↔ Equicontinuous ((u ∘ ·) ∘ F) := by
  congrm ∀ x, ?_
  rw [hu.equicontinuousAt_iff]

/-- Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontinuous on a
subset `S : Set X` iff the family `𝓕'`, obtained by composing each function of `𝓕` by `u`, is
equicontinuous on `S`. -/
theorem IsUniformInducing.equicontinuousOn_iff {F : ι → X → α} {S : Set X} {u : α → β}
    (hu : IsUniformInducing u) : EquicontinuousOn F S ↔ EquicontinuousOn ((u ∘ ·) ∘ F) S := by
  congrm ∀ x ∈ S, ?_
  rw [hu.equicontinuousWithinAt_iff]

/-- Given `u : α → γ` a uniform inducing map, a family `𝓕 : ι → β → α` is uniformly equicontinuous
iff the family `𝓕'`, obtained by composing each function of `𝓕` by `u`, is uniformly
equicontinuous. -/
theorem IsUniformInducing.uniformEquicontinuous_iff {F : ι → β → α} {u : α → γ}
    (hu : IsUniformInducing u) : UniformEquicontinuous F ↔ UniformEquicontinuous ((u ∘ ·) ∘ F) := by
  have := UniformFun.postcomp_isUniformInducing (α := ι) hu
  simp only [uniformEquicontinuous_iff_uniformContinuous, this.uniformContinuous_iff]
  rfl

/-- Given `u : α → γ` a uniform inducing map, a family `𝓕 : ι → β → α` is uniformly equicontinuous
on a subset `S : Set β` iff the family `𝓕'`, obtained by composing each function of `𝓕` by `u`,
is uniformly equicontinuous on `S`. -/
theorem IsUniformInducing.uniformEquicontinuousOn_iff {F : ι → β → α} {S : Set β} {u : α → γ}
    (hu : IsUniformInducing u) :
    UniformEquicontinuousOn F S ↔ UniformEquicontinuousOn ((u ∘ ·) ∘ F) S := by
  have := UniformFun.postcomp_isUniformInducing (α := ι) hu
  simp only [uniformEquicontinuousOn_iff_uniformContinuousOn, this.uniformContinuousOn_iff]
  rfl

/-- If a set of functions is equicontinuous at some `x₀` within a set `S`, the same is true for its
closure in *any* topology for which evaluation at any `x ∈ S ∪ {x₀}` is continuous. Since
this will be applied to `DFunLike` types, we state it for any topological space with a map
to `X → α` satisfying the right continuity conditions. See also `Set.EquicontinuousWithinAt.closure`
for a more familiar (but weaker) statement.

Note: This could *technically* be called `EquicontinuousWithinAt.closure` without name clashes
with `Set.EquicontinuousWithinAt.closure`, but we don't do it because, even with a `protected`
marker, it would introduce ambiguities while working in namespace `Set` (e.g, in the proof of
any theorem called `Set.something`). -/
theorem EquicontinuousWithinAt.closure' {A : Set Y} {u : Y → X → α} {S : Set X} {x₀ : X}
    (hA : EquicontinuousWithinAt (u ∘ (↑) : A → X → α) S x₀) (hu₁ : Continuous (S.restrict ∘ u))
    (hu₂ : Continuous (eval x₀ ∘ u)) :
    EquicontinuousWithinAt (u ∘ (↑) : closure A → X → α) S x₀ := by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV, eventually_mem_nhdsWithin] with x hx hxS
  rw [SetCoe.forall] at *
  change A ⊆ (fun f ↦ (u f x₀, u f x)) ⁻¹' V at hx
  refine (closure_minimal hx <| hVclosed.preimage <| hu₂.prodMk ?_).trans (preimage_mono hVU)
  exact (continuous_apply ⟨x, hxS⟩).comp hu₁

/-- If a set of functions is equicontinuous at some `x₀`, the same is true for its closure in *any*
topology for which evaluation at any point is continuous. Since this will be applied to
`DFunLike` types, we state it for any topological space with a map to `X → α` satisfying the right
continuity conditions. See also `Set.EquicontinuousAt.closure` for a more familiar statement. -/
theorem EquicontinuousAt.closure' {A : Set Y} {u : Y → X → α} {x₀ : X}
    (hA : EquicontinuousAt (u ∘ (↑) : A → X → α) x₀) (hu : Continuous u) :
    EquicontinuousAt (u ∘ (↑) : closure A → X → α) x₀ := by
  rw [← equicontinuousWithinAt_univ] at hA ⊢
  exact hA.closure' (Pi.continuous_restrict _ |>.comp hu) (continuous_apply x₀ |>.comp hu)

/-- If a set of functions is equicontinuous at some `x₀`, its closure for the product topology is
also equicontinuous at `x₀`. -/
protected theorem Set.EquicontinuousAt.closure {A : Set (X → α)} {x₀ : X}
    (hA : A.EquicontinuousAt x₀) : (closure A).EquicontinuousAt x₀ :=
  hA.closure' (u := id) continuous_id

/-- If a set of functions is equicontinuous at some `x₀` within a set `S`, its closure for the
product topology is also equicontinuous at `x₀` within `S`. This would also be true for the coarser
topology of pointwise convergence on `S ∪ {x₀}`, see `Set.EquicontinuousWithinAt.closure'`. -/
protected theorem Set.EquicontinuousWithinAt.closure {A : Set (X → α)} {S : Set X} {x₀ : X}
    (hA : A.EquicontinuousWithinAt S x₀) :
    (closure A).EquicontinuousWithinAt S x₀ :=
  hA.closure' (u := id) (Pi.continuous_restrict _) (continuous_apply _)

/-- If a set of functions is equicontinuous, the same is true for its closure in *any*
topology for which evaluation at any point is continuous. Since this will be applied to
`DFunLike` types, we state it for any topological space with a map to `X → α` satisfying the right
continuity conditions. See also `Set.Equicontinuous.closure` for a more familiar statement. -/
theorem Equicontinuous.closure' {A : Set Y} {u : Y → X → α}
    (hA : Equicontinuous (u ∘ (↑) : A → X → α)) (hu : Continuous u) :
    Equicontinuous (u ∘ (↑) : closure A → X → α) := fun x ↦ (hA x).closure' hu

/-- If a set of functions is equicontinuous on a set `S`, the same is true for its closure in *any*
topology for which evaluation at any `x ∈ S` is continuous. Since this will be applied to
`DFunLike` types, we state it for any topological space with a map to `X → α` satisfying the right
continuity conditions. See also `Set.EquicontinuousOn.closure` for a more familiar
(but weaker) statement. -/
theorem EquicontinuousOn.closure' {A : Set Y} {u : Y → X → α} {S : Set X}
    (hA : EquicontinuousOn (u ∘ (↑) : A → X → α) S) (hu : Continuous (S.restrict ∘ u)) :
    EquicontinuousOn (u ∘ (↑) : closure A → X → α) S :=
  fun x hx ↦ (hA x hx).closure' hu <| by exact continuous_apply ⟨x, hx⟩ |>.comp hu

/-- If a set of functions is equicontinuous, its closure for the product topology is also
equicontinuous. -/
protected theorem Set.Equicontinuous.closure {A : Set <| X → α} (hA : A.Equicontinuous) :
    (closure A).Equicontinuous := fun x ↦ Set.EquicontinuousAt.closure (hA x)

/-- If a set of functions is equicontinuous, its closure for the product topology is also
equicontinuous. This would also be true for the coarser topology of pointwise convergence on `S`,
see `EquicontinuousOn.closure'`. -/
protected theorem Set.EquicontinuousOn.closure {A : Set <| X → α} {S : Set X}
    (hA : A.EquicontinuousOn S) : (closure A).EquicontinuousOn S :=
  fun x hx ↦ Set.EquicontinuousWithinAt.closure (hA x hx)

/-- If a set of functions is uniformly equicontinuous on a set `S`, the same is true for its
closure in *any* topology for which evaluation at any `x ∈ S` i continuous. Since this will be
applied to `DFunLike` types, we state it for any topological space with a map to `β → α` satisfying
the right continuity conditions. See also `Set.UniformEquicontinuousOn.closure` for a more familiar
(but weaker) statement. -/
theorem UniformEquicontinuousOn.closure' {A : Set Y} {u : Y → β → α} {S : Set β}
    (hA : UniformEquicontinuousOn (u ∘ (↑) : A → β → α) S) (hu : Continuous (S.restrict ∘ u)) :
    UniformEquicontinuousOn (u ∘ (↑) : closure A → β → α) S := by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV, mem_inf_of_right (mem_principal_self _)]
  rintro ⟨x, y⟩ hxy ⟨hxS, hyS⟩
  rw [SetCoe.forall] at *
  change A ⊆ (fun f ↦ (u f x, u f y)) ⁻¹' V at hxy
  refine (closure_minimal hxy <| hVclosed.preimage <| .prodMk ?_ ?_).trans (preimage_mono hVU)
  · exact (continuous_apply ⟨x, hxS⟩).comp hu
  · exact (continuous_apply ⟨y, hyS⟩).comp hu

/-- If a set of functions is uniformly equicontinuous, the same is true for its closure in *any*
topology for which evaluation at any point is continuous. Since this will be applied to
`DFunLike` types, we state it for any topological space with a map to `β → α` satisfying the right
continuity conditions. See also `Set.UniformEquicontinuous.closure` for a more familiar statement.
-/
theorem UniformEquicontinuous.closure' {A : Set Y} {u : Y → β → α}
    (hA : UniformEquicontinuous (u ∘ (↑) : A → β → α)) (hu : Continuous u) :
    UniformEquicontinuous (u ∘ (↑) : closure A → β → α) := by
  rw [← uniformEquicontinuousOn_univ] at hA ⊢
  exact hA.closure' (Pi.continuous_restrict _ |>.comp hu)

/-- If a set of functions is uniformly equicontinuous, its closure for the product topology is also
uniformly equicontinuous. -/
protected theorem Set.UniformEquicontinuous.closure {A : Set <| β → α}
    (hA : A.UniformEquicontinuous) : (closure A).UniformEquicontinuous :=
  UniformEquicontinuous.closure' (u := id) hA continuous_id

/-- If a set of functions is uniformly equicontinuous on a set `S`, its closure for the product
topology is also uniformly equicontinuous. This would also be true for the coarser topology of
pointwise convergence on `S`, see `UniformEquicontinuousOn.closure'`. -/
protected theorem Set.UniformEquicontinuousOn.closure {A : Set <| β → α} {S : Set β}
    (hA : A.UniformEquicontinuousOn S) : (closure A).UniformEquicontinuousOn S :=
  UniformEquicontinuousOn.closure' (u := id) hA (Pi.continuous_restrict _)

/-
Implementation note: The following lemma (as well as all the following variations) could
theoretically be deduced from the "closure" statements above. For example, we could do:
```lean
theorem Filter.Tendsto.continuousAt_of_equicontinuousAt {l : Filter ι} [l.NeBot] {F : ι → X → α}
    {f : X → α} {x₀ : X} (h₁ : Tendsto F l (𝓝 f)) (h₂ : EquicontinuousAt F x₀) :
    ContinuousAt f x₀ :=
  (equicontinuousAt_iff_range.mp h₂).closure.continuousAt
    ⟨f, mem_closure_of_tendsto h₁ <| Eventually.of_forall mem_range_self⟩

theorem Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous {l : Filter ι} [l.NeBot]
    {F : ι → β → α} {f : β → α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : UniformEquicontinuous F) :
    UniformContinuous f :=
  (uniformEquicontinuous_iff_range.mp h₂).closure.uniformContinuous
    ⟨f, mem_closure_of_tendsto h₁ <| Eventually.of_forall mem_range_self⟩
```

Unfortunately, the proofs get painful when dealing with the relative case as one needs to change
the ambient topology. So it turns out to be easier to re-do the proof by hand.
-/

/-- If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise on `S ∪ {x₀} : Set X`* along some nontrivial
filter, and if the family `𝓕` is equicontinuous at `x₀ : X` within `S`, then the limit is
continuous at `x₀` within `S`. -/
theorem Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt {l : Filter ι} [l.NeBot]
    {F : ι → X → α} {f : X → α} {S : Set X} {x₀ : X} (h₁ : ∀ x ∈ S, Tendsto (F · x) l (𝓝 (f x)))
    (h₂ : Tendsto (F · x₀) l (𝓝 (f x₀))) (h₃ : EquicontinuousWithinAt F S x₀) :
    ContinuousWithinAt f S x₀ := by
  intro U hU; rw [mem_map]
  rcases UniformSpace.mem_nhds_iff.mp hU with ⟨V, hV, hVU⟩
  rcases mem_uniformity_isClosed hV with ⟨W, hW, hWclosed, hWV⟩
  filter_upwards [h₃ W hW, eventually_mem_nhdsWithin] with x hx hxS using
    hVU <| ball_mono hWV (f x₀) <| hWclosed.mem_of_tendsto (h₂.prodMk_nhds (h₁ x hxS)) <|
    Eventually.of_forall hx

/-- If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise* along some nontrivial filter, and if the
family `𝓕` is equicontinuous at some `x₀ : X`, then the limit is continuous at `x₀`. -/
theorem Filter.Tendsto.continuousAt_of_equicontinuousAt {l : Filter ι} [l.NeBot] {F : ι → X → α}
    {f : X → α} {x₀ : X} (h₁ : Tendsto F l (𝓝 f)) (h₂ : EquicontinuousAt F x₀) :
    ContinuousAt f x₀ := by
  rw [← continuousWithinAt_univ, ← equicontinuousWithinAt_univ, tendsto_pi_nhds] at *
  exact continuousWithinAt_of_equicontinuousWithinAt (fun x _ ↦ h₁ x) (h₁ x₀) h₂

/-- If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise* along some nontrivial filter, and if the
family `𝓕` is equicontinuous, then the limit is continuous. -/
theorem Filter.Tendsto.continuous_of_equicontinuous {l : Filter ι} [l.NeBot] {F : ι → X → α}
    {f : X → α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : Equicontinuous F) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x ↦ h₁.continuousAt_of_equicontinuousAt (h₂ x)

/-- If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise on `S : Set X`* along some nontrivial
filter, and if the family `𝓕` is equicontinuous, then the limit is continuous on `S`. -/
theorem Filter.Tendsto.continuousOn_of_equicontinuousOn {l : Filter ι} [l.NeBot] {F : ι → X → α}
    {f : X → α} {S : Set X} (h₁ : ∀ x ∈ S, Tendsto (F · x) l (𝓝 (f x)))
    (h₂ : EquicontinuousOn F S) : ContinuousOn f S :=
  fun x hx ↦ Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt h₁ (h₁ x hx) (h₂ x hx)

/-- If `𝓕 : ι → β → α` tends to `f : β → α` *pointwise on `S : Set β`* along some nontrivial
filter, and if the family `𝓕` is uniformly equicontinuous on `S`, then the limit is uniformly
continuous on `S`. -/
theorem Filter.Tendsto.uniformContinuousOn_of_uniformEquicontinuousOn {l : Filter ι} [l.NeBot]
    {F : ι → β → α} {f : β → α} {S : Set β} (h₁ : ∀ x ∈ S, Tendsto (F · x) l (𝓝 (f x)))
    (h₂ : UniformEquicontinuousOn F S) :
    UniformContinuousOn f S := by
  intro U hU; rw [mem_map]
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [h₂ V hV, mem_inf_of_right (mem_principal_self _)]
  rintro ⟨x, y⟩ hxy ⟨hxS, hyS⟩
  exact hVU <| hVclosed.mem_of_tendsto ((h₁ x hxS).prodMk_nhds (h₁ y hyS)) <|
    Eventually.of_forall hxy

/-- If `𝓕 : ι → β → α` tends to `f : β → α` *pointwise* along some nontrivial filter, and if the
family `𝓕` is uniformly equicontinuous, then the limit is uniformly continuous. -/
theorem Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous {l : Filter ι} [l.NeBot]
    {F : ι → β → α} {f : β → α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : UniformEquicontinuous F) :
    UniformContinuous f := by
  rw [← uniformContinuousOn_univ, ← uniformEquicontinuousOn_univ, tendsto_pi_nhds] at *
  exact uniformContinuousOn_of_uniformEquicontinuousOn (fun x _ ↦ h₁ x) h₂

/-- If `F : ι → X → α` is a family of functions equicontinuous at `x`,
it tends to `f y` along a filter `l` for any `y ∈ s`,
the limit function `f` tends to `z` along `𝓝[s] x`, and `x ∈ closure s`,
then `(F · x)` tends to `z` along `l`.

In some sense, this is a converse of `EquicontinuousAt.closure`. -/
theorem EquicontinuousAt.tendsto_of_mem_closure {l : Filter ι} {F : ι → X → α} {f : X → α}
    {s : Set X} {x : X} {z : α} (hF : EquicontinuousAt F x) (hf : Tendsto f (𝓝[s] x) (𝓝 z))
    (hs : ∀ y ∈ s, Tendsto (F · y) l (𝓝 (f y))) (hx : x ∈ closure s) :
    Tendsto (F · x) l (𝓝 z) := by
  rw [(nhds_basis_uniformity (𝓤 α).basis_sets).tendsto_right_iff] at hf ⊢
  intro U hU
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVs, hVU⟩
  rw [mem_closure_iff_nhdsWithin_neBot] at hx
  have : ∀ᶠ y in 𝓝[s] x, y ∈ s ∧ (∀ i, (F i x, F i y) ∈ V) ∧ (f y, z) ∈ V :=
    eventually_mem_nhdsWithin.and <| ((hF V hV).filter_mono nhdsWithin_le_nhds).and (hf V hV)
  rcases this.exists with ⟨y, hys, hFy, hfy⟩
  filter_upwards [hs y hys (ball_mem_nhds _ hV)] with i hi
  exact hVU ⟨_, ⟨_, hFy i, (mem_ball_symmetry hVs).2 hi⟩, hfy⟩

/-- If `F : ι → X → α` is an equicontinuous family of functions,
`f : X → α` is a continuous function, and `l` is a filter on `ι`,
then `{x | Filter.Tendsto (F · x) l (𝓝 (f x))}` is a closed set. -/
theorem Equicontinuous.isClosed_setOf_tendsto {l : Filter ι} {F : ι → X → α} {f : X → α}
    (hF : Equicontinuous F) (hf : Continuous f) :
    IsClosed {x | Tendsto (F · x) l (𝓝 (f x))} :=
  closure_subset_iff_isClosed.mp fun x hx ↦
    (hF x).tendsto_of_mem_closure (hf.continuousAt.mono_left inf_le_left) (fun _ ↦ id) hx

end

end

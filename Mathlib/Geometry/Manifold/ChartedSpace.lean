/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Init.Align
import Mathlib.Topology.LocalHomeomorph

#align_import geometry.manifold.charted_space from "leanprover-community/mathlib"@"431589bce478b2229eba14b14a283250428217db"

/-!
# Charted spaces

A smooth manifold is a topological space `M` locally modelled on a euclidean space (or a euclidean
half-space for manifolds with boundaries, or an infinite dimensional vector space for more general
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
formalized through the notion of structure groupoid, i.e., a set of local homeomorphisms stable
under composition and inverse, to which the change of coordinates should belong.

## Main definitions

* `StructureGroupoid H` : a subset of local homeomorphisms of `H` stable under composition,
  inverse and restriction (ex: local diffeos).
* `continuousGroupoid H` : the groupoid of all local homeomorphisms of `H`.
* `ChartedSpace H M` : charted space structure on `M` modelled on `H`, given by an atlas of
  local homeomorphisms from `M` to `H` whose sources cover `M`. This is a type class.
* `HasGroupoid M G` : when `G` is a structure groupoid on `H` and `M` is a charted space
  modelled on `H`, require that all coordinate changes belong to `G`. This is a type class.
* `atlas H M` : when `M` is a charted space modelled on `H`, the atlas of this charted
  space structure, i.e., the set of charts.
* `G.maximalAtlas M` : when `M` is a charted space modelled on `H` and admitting `G` as a
  structure groupoid, one can consider all the local homeomorphisms from `M` to `H` such that
  changing coordinate from any chart to them belongs to `G`. This is a larger atlas, called the
  maximal atlas (for the groupoid `G`).
* `Structomorph G M M'` : the type of diffeomorphisms between the charted spaces `M` and `M'` for
  the groupoid `G`. We avoid the word diffeomorphism, keeping it for the smooth category.

As a basic example, we give the instance
`instance chartedSpaceSelf (H : Type*) [TopologicalSpace H] : ChartedSpace H H`
saying that a topological space is a charted space over itself, with the identity as unique chart.
This charted space structure is compatible with any groupoid.

Additional useful definitions:

* `Pregroupoid H` : a subset of local maps of `H` stable under composition and
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
  of charts (which are local equivs) for which the change of coordinates are local homeos. Then
  one can construct a topology on the space for which the charts become local homeos, defining
  a genuine charted space structure.

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
model space is a half space.

Manifolds are sometimes defined as topological spaces with an atlas of local diffeomorphisms, and
sometimes as spaces with an atlas from which a topology is deduced. We use the former approach:
otherwise, there would be an instance from manifolds to topological spaces, which means that any
instance search for topological spaces would try to find manifold structures involving a yet
unknown model space, leading to problems. However, we also introduce the latter approach,
through a structure `ChartedSpaceCore` making it possible to construct a topology out of a set of
local equivs with compatibility conditions (but we do not register it as an instance).

In the definition of a charted space, the model space is written as an explicit parameter as there
can be several model spaces for a given topological space. For instance, a complex manifold
(modelled over `ℂ^n`) will also be seen sometimes as a real manifold modelled over `ℝ^(2n)`.

## Notations

In the locale `Manifold`, we denote the composition of local homeomorphisms with `≫ₕ`, and the
composition of local equivs with `≫`.
-/

set_option autoImplicit true


noncomputable section

open Classical Topology Filter

universe u

variable {H : Type u} {H' : Type*} {M : Type*} {M' : Type*} {M'' : Type*}

/- Notational shortcut for the composition of local homeomorphisms and local equivs, i.e.,
`LocalHomeomorph.trans` and `LocalEquiv.trans`.
Note that, as is usual for equivs, the composition is from left to right, hence the direction of
the arrow. -/
scoped[Manifold] infixr:100 " ≫ₕ " => LocalHomeomorph.trans

scoped[Manifold] infixr:100 " ≫ " => LocalEquiv.trans

open Set LocalHomeomorph Manifold  -- Porting note: Added `Manifold`

/-! ### Structure groupoids -/


section Groupoid

/-! One could add to the definition of a structure groupoid the fact that the restriction of an
element of the groupoid to any open set still belongs to the groupoid.
(This is in Kobayashi-Nomizu.)
I am not sure I want this, for instance on `H × E` where `E` is a vector space, and the groupoid is
made of functions respecting the fibers and linear in the fibers (so that a charted space over this
groupoid is naturally a vector bundle) I prefer that the members of the groupoid are always
defined on sets of the form `s × E`. There is a typeclass `ClosedUnderRestriction` for groupoids
which have the restriction property.

The only nontrivial requirement is locality: if a local homeomorphism belongs to the groupoid
around each point in its domain of definition, then it belongs to the groupoid. Without this
requirement, the composition of structomorphisms does not have to be a structomorphism. Note that
this implies that a local homeomorphism with empty source belongs to any structure groupoid, as
it trivially satisfies this condition.

There is also a technical point, related to the fact that a local homeomorphism is by definition a
global map which is a homeomorphism when restricted to its source subset (and its values outside
of the source are not relevant). Therefore, we also require that being a member of the groupoid only
depends on the values on the source.

We use primes in the structure names as we will reformulate them below (without primes) using a
`Membership` instance, writing `e ∈ G` instead of `e ∈ G.members`.
-/


/-- A structure groupoid is a set of local homeomorphisms of a topological space stable under
composition and inverse. They appear in the definition of the smoothness class of a manifold. -/
structure StructureGroupoid (H : Type u) [TopologicalSpace H] where
  members : Set (LocalHomeomorph H H)
  trans' : ∀ e e' : LocalHomeomorph H H, e ∈ members → e' ∈ members → e ≫ₕ e' ∈ members
  symm' : ∀ e : LocalHomeomorph H H, e ∈ members → e.symm ∈ members
  id_mem' : LocalHomeomorph.refl H ∈ members
  locality' : ∀ e : LocalHomeomorph H H,
    (∀ x ∈ e.source, ∃ s, IsOpen s ∧ x ∈ s ∧ e.restr s ∈ members) → e ∈ members
  eq_on_source' : ∀ e e' : LocalHomeomorph H H, e ∈ members → e' ≈ e → e' ∈ members
#align structure_groupoid StructureGroupoid

variable [TopologicalSpace H]

instance : Membership (LocalHomeomorph H H) (StructureGroupoid H) :=
  ⟨fun (e : LocalHomeomorph H H) (G : StructureGroupoid H) ↦ e ∈ G.members⟩

theorem StructureGroupoid.trans (G : StructureGroupoid H) {e e' : LocalHomeomorph H H} (he : e ∈ G)
    (he' : e' ∈ G) : e ≫ₕ e' ∈ G :=
  G.trans' e e' he he'
#align structure_groupoid.trans StructureGroupoid.trans

theorem StructureGroupoid.symm (G : StructureGroupoid H) {e : LocalHomeomorph H H} (he : e ∈ G) :
    e.symm ∈ G :=
  G.symm' e he
#align structure_groupoid.symm StructureGroupoid.symm

theorem StructureGroupoid.id_mem (G : StructureGroupoid H) : LocalHomeomorph.refl H ∈ G :=
  G.id_mem'
#align structure_groupoid.id_mem StructureGroupoid.id_mem

theorem StructureGroupoid.locality (G : StructureGroupoid H) {e : LocalHomeomorph H H}
    (h : ∀ x ∈ e.source, ∃ s, IsOpen s ∧ x ∈ s ∧ e.restr s ∈ G) : e ∈ G :=
  G.locality' e h
#align structure_groupoid.locality StructureGroupoid.locality

theorem StructureGroupoid.eq_on_source (G : StructureGroupoid H) {e e' : LocalHomeomorph H H}
    (he : e ∈ G) (h : e' ≈ e) : e' ∈ G :=
  G.eq_on_source' e e' he h
#align structure_groupoid.eq_on_source StructureGroupoid.eq_on_source

/-- Partial order on the set of groupoids, given by inclusion of the members of the groupoid. -/
instance StructureGroupoid.partialOrder : PartialOrder (StructureGroupoid H) :=
  PartialOrder.lift StructureGroupoid.members fun a b h ↦ by
    cases a
    cases b
    dsimp at h
    induction h
    rfl
#align structure_groupoid.partial_order StructureGroupoid.partialOrder

theorem StructureGroupoid.le_iff {G₁ G₂ : StructureGroupoid H} : G₁ ≤ G₂ ↔ ∀ e, e ∈ G₁ → e ∈ G₂ :=
  Iff.rfl
#align structure_groupoid.le_iff StructureGroupoid.le_iff

/-- The trivial groupoid, containing only the identity (and maps with empty source, as this is
necessary from the definition). -/
def idGroupoid (H : Type u) [TopologicalSpace H] : StructureGroupoid H where
  members := {LocalHomeomorph.refl H} ∪ { e : LocalHomeomorph H H | e.source = ∅ }
  trans' e e' he he' := by
    cases' he with he he
    · simpa only [mem_singleton_iff.1 he, refl_trans]
    · have : (e ≫ₕ e').source ⊆ e.source := sep_subset _ _
      rw [he] at this
      have : e ≫ₕ e' ∈ { e : LocalHomeomorph H H | e.source = ∅ } := eq_bot_iff.2 this
      exact (mem_union _ _ _).2 (Or.inr this)
  symm' e he := by
    cases' (mem_union _ _ _).1 he with E E
    · simp [mem_singleton_iff.mp E]
    · right
      simpa only [e.toLocalEquiv.image_source_eq_target.symm, mfld_simps] using E
  id_mem' := mem_union_left _ rfl
  locality' e he := by
    cases' e.source.eq_empty_or_nonempty with h h
    · right
      exact h
    · left
      rcases h with ⟨x, hx⟩
      rcases he x hx with ⟨s, open_s, xs, hs⟩
      have x's : x ∈ (e.restr s).source := by
        rw [restr_source, open_s.interior_eq]
        exact ⟨hx, xs⟩
      cases' hs with hs hs
      · replace hs : LocalHomeomorph.restr e s = LocalHomeomorph.refl H
        · simpa only using hs
        have : (e.restr s).source = univ := by
          rw [hs]
          simp
        have : e.toLocalEquiv.source ∩ interior s = univ := this
        have : univ ⊆ interior s := by
          rw [← this]
          exact inter_subset_right _ _
        have : s = univ := by rwa [open_s.interior_eq, univ_subset_iff] at this
        simpa only [this, restr_univ] using hs
      · exfalso
        rw [mem_setOf_eq] at hs
        rwa [hs] at x's
  eq_on_source' e e' he he'e := by
    cases' he with he he
    · left
      have : e = e' := by
        refine' eq_of_eq_on_source_univ (Setoid.symm he'e) _ _ <;>
          rw [Set.mem_singleton_iff.1 he] <;> rfl
      rwa [← this]
    · right
      have he : e.toLocalEquiv.source = ∅ := he
      rwa [Set.mem_setOf_eq, EqOnSource.source_eq he'e]
#align id_groupoid idGroupoid

/-- Every structure groupoid contains the identity groupoid. -/
instance : OrderBot (StructureGroupoid H) where
  bot := idGroupoid H
  bot_le := by
    intro u f hf
    have hf : f ∈ {LocalHomeomorph.refl H} ∪ { e : LocalHomeomorph H H | e.source = ∅ } := hf
    simp only [singleton_union, mem_setOf_eq, mem_insert_iff] at hf
    cases' hf with hf hf
    · rw [hf]
      apply u.id_mem
    · apply u.locality
      intro x hx
      rw [hf, mem_empty_iff_false] at hx
      exact hx.elim

instance (H : Type u) [TopologicalSpace H] : Inhabited (StructureGroupoid H) :=
  ⟨idGroupoid H⟩

/-- To construct a groupoid, one may consider classes of local homeos such that both the function
and its inverse have some property. If this property is stable under composition,
one gets a groupoid. `Pregroupoid` bundles the properties needed for this construction, with the
groupoid of smooth functions with smooth inverses as an application. -/
structure Pregroupoid (H : Type*) [TopologicalSpace H] where
  property : (H → H) → Set H → Prop
  comp : ∀ {f g u v}, property f u → property g v →
    IsOpen u → IsOpen v → IsOpen (u ∩ f ⁻¹' v) → property (g ∘ f) (u ∩ f ⁻¹' v)
  id_mem : property id univ
  locality :
    ∀ {f u}, IsOpen u → (∀ x ∈ u, ∃ v, IsOpen v ∧ x ∈ v ∧ property f (u ∩ v)) → property f u
  congr : ∀ {f g : H → H} {u}, IsOpen u → (∀ x ∈ u, g x = f x) → property f u → property g u
#align pregroupoid Pregroupoid

/-- Construct a groupoid of local homeos for which the map and its inverse have some property,
from a pregroupoid asserting that this property is stable under composition. -/
def Pregroupoid.groupoid (PG : Pregroupoid H) : StructureGroupoid H where
  members := { e : LocalHomeomorph H H | PG.property e e.source ∧ PG.property e.symm e.target }
  trans' e e' he he' := by
    constructor
    · apply PG.comp he.1 he'.1 e.open_source e'.open_source
      apply e.continuous_toFun.preimage_open_of_open e.open_source e'.open_source
    · apply PG.comp he'.2 he.2 e'.open_target e.open_target
      apply e'.continuous_invFun.preimage_open_of_open e'.open_target e.open_target
  symm' e he := ⟨he.2, he.1⟩
  id_mem' := ⟨PG.id_mem, PG.id_mem⟩
  locality' e he := by
    constructor
    · refine' PG.locality e.open_source fun x xu ↦ _
      rcases he x xu with ⟨s, s_open, xs, hs⟩
      refine' ⟨s, s_open, xs, _⟩
      convert hs.1 using 1
      dsimp [LocalHomeomorph.restr]
      rw [s_open.interior_eq]
    · refine' PG.locality e.open_target fun x xu ↦ _
      rcases he (e.symm x) (e.map_target xu) with ⟨s, s_open, xs, hs⟩
      refine' ⟨e.target ∩ e.symm ⁻¹' s, _, ⟨xu, xs⟩, _⟩
      · exact ContinuousOn.preimage_open_of_open e.continuous_invFun e.open_target s_open
      · rw [← inter_assoc, inter_self]
        convert hs.2 using 1
        dsimp [LocalHomeomorph.restr]
        rw [s_open.interior_eq]
  eq_on_source' e e' he ee' := by
    constructor
    · apply PG.congr e'.open_source ee'.2
      simp only [ee'.1, he.1]
    · have A := EqOnSource.symm' ee'
      apply PG.congr e'.symm.open_source A.2
      -- Porting note: was
      -- convert he.2
      -- rw [A.1]
      -- rfl
      rw [A.1, symm_toLocalEquiv, LocalEquiv.symm_source]
      exact he.2
#align pregroupoid.groupoid Pregroupoid.groupoid

theorem mem_groupoid_of_pregroupoid {PG : Pregroupoid H} {e : LocalHomeomorph H H} :
    e ∈ PG.groupoid ↔ PG.property e e.source ∧ PG.property e.symm e.target :=
  Iff.rfl
#align mem_groupoid_of_pregroupoid mem_groupoid_of_pregroupoid

theorem groupoid_of_pregroupoid_le (PG₁ PG₂ : Pregroupoid H)
    (h : ∀ f s, PG₁.property f s → PG₂.property f s) : PG₁.groupoid ≤ PG₂.groupoid := by
  refine' StructureGroupoid.le_iff.2 fun e he ↦ _
  rw [mem_groupoid_of_pregroupoid] at he ⊢
  exact ⟨h _ _ he.1, h _ _ he.2⟩
#align groupoid_of_pregroupoid_le groupoid_of_pregroupoid_le

theorem mem_pregroupoid_of_eq_on_source (PG : Pregroupoid H) {e e' : LocalHomeomorph H H}
    (he' : e ≈ e') (he : PG.property e e.source) : PG.property e' e'.source := by
  rw [← he'.1]
  exact PG.congr e.open_source he'.eqOn.symm he
#align mem_pregroupoid_of_eq_on_source mem_pregroupoid_of_eq_on_source

/-- The pregroupoid of all local maps on a topological space `H`. -/
@[reducible]
def continuousPregroupoid (H : Type*) [TopologicalSpace H] : Pregroupoid H where
  property _ _ := True
  comp _ _ _ _ _ := trivial
  id_mem := trivial
  locality _ _ := trivial
  congr _ _ _ := trivial
#align continuous_pregroupoid continuousPregroupoid

instance (H : Type*) [TopologicalSpace H] : Inhabited (Pregroupoid H) :=
  ⟨continuousPregroupoid H⟩

/-- The groupoid of all local homeomorphisms on a topological space `H`. -/
def continuousGroupoid (H : Type*) [TopologicalSpace H] : StructureGroupoid H :=
  Pregroupoid.groupoid (continuousPregroupoid H)
#align continuous_groupoid continuousGroupoid

/-- Every structure groupoid is contained in the groupoid of all local homeomorphisms. -/
instance : OrderTop (StructureGroupoid H) where
  top := continuousGroupoid H
  le_top _ _ _ := ⟨trivial, trivial⟩

/-- A groupoid is closed under restriction if it contains all restrictions of its element local
homeomorphisms to open subsets of the source. -/
class ClosedUnderRestriction (G : StructureGroupoid H) : Prop where
  closedUnderRestriction :
    ∀ {e : LocalHomeomorph H H}, e ∈ G → ∀ s : Set H, IsOpen s → e.restr s ∈ G
#align closed_under_restriction ClosedUnderRestriction

theorem closedUnderRestriction' {G : StructureGroupoid H} [ClosedUnderRestriction G]
    {e : LocalHomeomorph H H} (he : e ∈ G) {s : Set H} (hs : IsOpen s) : e.restr s ∈ G :=
  ClosedUnderRestriction.closedUnderRestriction he s hs
#align closed_under_restriction' closedUnderRestriction'

/-- The trivial restriction-closed groupoid, containing only local homeomorphisms equivalent to the
restriction of the identity to the various open subsets. -/
def idRestrGroupoid : StructureGroupoid H where
  members := { e | ∃ (s : Set H) (h : IsOpen s), e ≈ LocalHomeomorph.ofSet s h }
  trans' := by
    rintro e e' ⟨s, hs, hse⟩ ⟨s', hs', hse'⟩
    refine' ⟨s ∩ s', IsOpen.inter hs hs', _⟩
    have := LocalHomeomorph.EqOnSource.trans' hse hse'
    rwa [LocalHomeomorph.ofSet_trans_ofSet] at this
  symm' := by
    rintro e ⟨s, hs, hse⟩
    refine' ⟨s, hs, _⟩
    rw [← ofSet_symm]
    exact LocalHomeomorph.EqOnSource.symm' hse
  id_mem' := ⟨univ, isOpen_univ, by simp only [mfld_simps, refl]⟩
  locality' := by
    intro e h
    refine' ⟨e.source, e.open_source, by simp only [mfld_simps], _⟩
    intro x hx
    rcases h x hx with ⟨s, hs, hxs, s', hs', hes'⟩
    have hes : x ∈ (e.restr s).source := by
      rw [e.restr_source]
      refine' ⟨hx, _⟩
      rw [hs.interior_eq]
      exact hxs
    simpa only [mfld_simps] using LocalHomeomorph.EqOnSource.eqOn hes' hes
  eq_on_source' := by
    rintro e e' ⟨s, hs, hse⟩ hee'
    exact ⟨s, hs, Setoid.trans hee' hse⟩
#align id_restr_groupoid idRestrGroupoid

theorem idRestrGroupoid_mem {s : Set H} (hs : IsOpen s) : ofSet s hs ∈ @idRestrGroupoid H _ :=
  ⟨s, hs, refl _⟩
#align id_restr_groupoid_mem idRestrGroupoid_mem

/-- The trivial restriction-closed groupoid is indeed `ClosedUnderRestriction`. -/
instance closedUnderRestriction_idRestrGroupoid : ClosedUnderRestriction (@idRestrGroupoid H _) :=
  ⟨by
    rintro e ⟨s', hs', he⟩ s hs
    use s' ∩ s, IsOpen.inter hs' hs
    refine' Setoid.trans (LocalHomeomorph.EqOnSource.restr he s) _
    exact ⟨by simp only [hs.interior_eq, mfld_simps], by simp only [mfld_simps, eqOn_refl]⟩⟩
#align closed_under_restriction_id_restr_groupoid closedUnderRestriction_idRestrGroupoid

/-- A groupoid is closed under restriction if and only if it contains the trivial restriction-closed
groupoid. -/
theorem closedUnderRestriction_iff_id_le (G : StructureGroupoid H) :
    ClosedUnderRestriction G ↔ idRestrGroupoid ≤ G := by
  constructor
  · intro _i
    apply StructureGroupoid.le_iff.mpr
    rintro e ⟨s, hs, hes⟩
    refine' G.eq_on_source _ hes
    convert closedUnderRestriction' G.id_mem hs
    -- Porting note: was
    -- change s = _ ∩ _
    -- rw [hs.interior_eq]
    -- simp only [mfld_simps]
    ext
    · rw [LocalHomeomorph.restr_apply, LocalHomeomorph.refl_apply, id, ofSet_apply, id_eq]
    · simp [hs]
    · simp [hs.interior_eq]
  · intro h
    constructor
    intro e he s hs
    rw [← ofSet_trans (e : LocalHomeomorph H H) hs]
    refine' G.trans _ he
    apply StructureGroupoid.le_iff.mp h
    exact idRestrGroupoid_mem hs
#align closed_under_restriction_iff_id_le closedUnderRestriction_iff_id_le

/-- The groupoid of all local homeomorphisms on a topological space `H` is closed under restriction.
-/
instance : ClosedUnderRestriction (continuousGroupoid H) :=
  (closedUnderRestriction_iff_id_le _).mpr le_top

end Groupoid

/-! ### Charted spaces -/


/-- A charted space is a topological space endowed with an atlas, i.e., a set of local
homeomorphisms taking value in a model space `H`, called charts, such that the domains of the charts
cover the whole space. We express the covering property by choosing for each `x` a member
`chartAt x` of the atlas containing `x` in its source: in the smooth case, this is convenient to
construct the tangent bundle in an efficient way.
The model space is written as an explicit parameter as there can be several model spaces for a
given topological space. For instance, a complex manifold (modelled over `ℂ^n`) will also be seen
sometimes as a real manifold over `ℝ^(2n)`.
-/
@[ext]
class ChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M] where
  protected atlas : Set (LocalHomeomorph M H)
  protected chartAt : M → LocalHomeomorph M H
  protected mem_chart_source : ∀ x, x ∈ (chartAt x).source
  protected chart_mem_atlas : ∀ x, chartAt x ∈ atlas
#align charted_space ChartedSpace

abbrev atlas (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Set (LocalHomeomorph M H) :=
  ChartedSpace.atlas

abbrev chartAt (H : Type*) [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : LocalHomeomorph M H :=
  ChartedSpace.chartAt x

@[simp, mfld_simps]
lemma mem_chart_source (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : x ∈ (chartAt H x).source :=
  ChartedSpace.mem_chart_source x

@[simp, mfld_simps]
lemma chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (x : M) : chartAt H x ∈ atlas H M :=
  ChartedSpace.chart_mem_atlas x

section ChartedSpace

/-- Any space is a `ChartedSpace` modelled over itself, by just using the identity chart. -/
instance chartedSpaceSelf (H : Type*) [TopologicalSpace H] : ChartedSpace H H where
  atlas := {LocalHomeomorph.refl H}
  chartAt _ := LocalHomeomorph.refl H
  mem_chart_source x := mem_univ x
  chart_mem_atlas _ := mem_singleton _
#align charted_space_self chartedSpaceSelf

/-- In the trivial `ChartedSpace` structure of a space modelled over itself through the identity,
the atlas members are just the identity. -/
@[simp, mfld_simps]
theorem chartedSpaceSelf_atlas {H : Type*} [TopologicalSpace H] {e : LocalHomeomorph H H} :
    e ∈ atlas H H ↔ e = LocalHomeomorph.refl H :=
  Iff.rfl
#align charted_space_self_atlas chartedSpaceSelf_atlas

/-- In the model space, `chartAt` is always the identity. -/
theorem chartAt_self_eq {H : Type*} [TopologicalSpace H] {x : H} :
    chartAt H x = LocalHomeomorph.refl H := rfl
#align chart_at_self_eq chartAt_self_eq

section

variable (H) [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

-- Porting note: Added `(H := H)` to avoid typeclass instance problem.
theorem mem_chart_target (x : M) : chartAt H x x ∈ (chartAt H x).target :=
  (chartAt H x).map_source (mem_chart_source _ _)
#align mem_chart_target mem_chart_target

theorem chart_source_mem_nhds (x : M) : (chartAt H x).source ∈ 𝓝 x :=
  (chartAt H x).open_source.mem_nhds <| mem_chart_source H x
#align chart_source_mem_nhds chart_source_mem_nhds

theorem chart_target_mem_nhds (x : M) : (chartAt H x).target ∈ 𝓝 (chartAt H x x) :=
  (chartAt H x).open_target.mem_nhds <| mem_chart_target H x
#align chart_target_mem_nhds chart_target_mem_nhds

/-- `achart H x` is the chart at `x`, considered as an element of the atlas.
Especially useful for working with `BasicSmoothVectorBundleCore`. -/
def achart (x : M) : atlas H M :=
  ⟨chartAt H x, chart_mem_atlas H x⟩
#align achart achart

theorem achart_def (x : M) : achart H x = ⟨chartAt H x, chart_mem_atlas H x⟩ :=
  rfl
#align achart_def achart_def

@[simp, mfld_simps]
theorem coe_achart (x : M) : (achart H x : LocalHomeomorph M H) = chartAt H x :=
  rfl
#align coe_achart coe_achart

@[simp, mfld_simps]
theorem achart_val (x : M) : (achart H x).1 = chartAt H x :=
  rfl
#align achart_val achart_val

theorem mem_achart_source (x : M) : x ∈ (achart H x).1.source :=
  mem_chart_source H x
#align mem_achart_source mem_achart_source

open TopologicalSpace

theorem ChartedSpace.secondCountable_of_countable_cover [SecondCountableTopology H] {s : Set M}
    (hs : ⋃ (x) (_ : x ∈ s), (chartAt H x).source = univ) (hsc : s.Countable) :
    SecondCountableTopology M := by
  haveI : ∀ x : M, SecondCountableTopology (chartAt H x).source :=
    fun x ↦ (chartAt (H := H) x).secondCountableTopology_source
  haveI := hsc.toEncodable
  rw [biUnion_eq_iUnion] at hs
  exact secondCountableTopology_of_countable_cover (fun x : s ↦ (chartAt H (x : M)).open_source) hs
#align charted_space.second_countable_of_countable_cover ChartedSpace.secondCountable_of_countable_cover

variable (M)

theorem ChartedSpace.secondCountable_of_sigma_compact [SecondCountableTopology H]
    [SigmaCompactSpace M] : SecondCountableTopology M := by
  obtain ⟨s, hsc, hsU⟩ : ∃ s, Set.Countable s ∧ ⋃ (x) (_ : x ∈ s), (chartAt H x).source = univ :=
    countable_cover_nhds_of_sigma_compact fun x : M ↦ chart_source_mem_nhds H x
  exact ChartedSpace.secondCountable_of_countable_cover H hsU hsc
#align charted_space.second_countable_of_sigma_compact ChartedSpace.secondCountable_of_sigma_compact

/-- If a topological space admits an atlas with locally compact charts, then the space itself
is locally compact. -/
theorem ChartedSpace.locallyCompactSpace [LocallyCompactSpace H] : LocallyCompactSpace M := by
  have : ∀ x : M, (𝓝 x).HasBasis
      (fun s ↦ s ∈ 𝓝 (chartAt H x x) ∧ IsCompact s ∧ s ⊆ (chartAt H x).target)
      fun s ↦ (chartAt H x).symm '' s := fun x ↦ by
    rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact ((compact_basis_nhds (chartAt H x x)).hasBasis_self_subset
      (chart_target_mem_nhds H x)).map _
  refine locallyCompactSpace_of_hasBasis this ?_
  rintro x s ⟨_, h₂, h₃⟩
  exact h₂.image_of_continuousOn ((chartAt H x).continuousOn_symm.mono h₃)
#align charted_space.locally_compact ChartedSpace.locallyCompactSpace

/-- If a topological space admits an atlas with locally connected charts, then the space itself is
locally connected. -/
theorem ChartedSpace.locallyConnectedSpace [LocallyConnectedSpace H] : LocallyConnectedSpace M := by
  let e : M → LocalHomeomorph M H := chartAt H
  refine' locallyConnectedSpace_of_connected_bases (fun x s ↦ (e x).symm '' s)
      (fun x s ↦ (IsOpen s ∧ e x x ∈ s ∧ IsConnected s) ∧ s ⊆ (e x).target) _ _
  · intro x
    simpa only [LocalHomeomorph.symm_map_nhds_eq, mem_chart_source] using
      ((LocallyConnectedSpace.open_connected_basis (e x x)).restrict_subset
        ((e x).open_target.mem_nhds (mem_chart_target H x))).map (e x).symm
  · rintro x s ⟨⟨-, -, hsconn⟩, hssubset⟩
    exact hsconn.isPreconnected.image _ ((e x).continuousOn_symm.mono hssubset)
#align charted_space.locally_connected_space ChartedSpace.locallyConnectedSpace

/-- If `M` is modelled on `H'` and `H'` is itself modelled on `H`, then we can consider `M` as being
modelled on `H`. -/
def ChartedSpace.comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
    (M : Type*) [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] :
    ChartedSpace H M where
  atlas := image2 LocalHomeomorph.trans (atlas H' M) (atlas H H')
  chartAt p := (chartAt H' p).trans (chartAt H (chartAt H' p p))
  mem_chart_source p := by simp only [mfld_simps]
  chart_mem_atlas p := ⟨chartAt _ p, chartAt _ _, chart_mem_atlas _ p, chart_mem_atlas _ _, rfl⟩
#align charted_space.comp ChartedSpace.comp

theorem chartAt_comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H H'] [ChartedSpace H' M] (x : M) :
    (letI := ChartedSpace.comp H H' M; chartAt H x) = chartAt H' x ≫ₕ chartAt H (chartAt H' x x) :=
  rfl

end

library_note "Manifold type tags" /-- For technical reasons we introduce two type tags:

* `ModelProd H H'` is the same as `H × H'`;
* `ModelPi H` is the same as `∀ i, H i`, where `H : ι → Type*` and `ι` is a finite type.

In both cases the reason is the same, so we explain it only in the case of the product. A charted
space `M` with model `H` is a set of local charts from `M` to `H` covering the space. Every space is
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
#align model_prod ModelProd

/-- Same thing as `∀ i, H i`. We introduce it for technical reasons,
see note [Manifold type tags]. -/
def ModelPi {ι : Type*} (H : ι → Type*) :=
  ∀ i, H i
#align model_pi ModelPi

section

-- attribute [local reducible] ModelProd -- Porting note: not available in Lean4

instance modelProdInhabited [Inhabited H] [Inhabited H'] : Inhabited (ModelProd H H') :=
  instInhabitedProd
#align model_prod_inhabited modelProdInhabited

instance (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H'] :
    TopologicalSpace (ModelProd H H') :=
  instTopologicalSpaceProd

-- Porting note: simpNF false positive
-- Next lemma shows up often when dealing with derivatives, register it as simp.
@[simp, mfld_simps, nolint simpNF]
theorem modelProd_range_prod_id {H : Type*} {H' : Type*} {α : Type*} (f : H → α) :
    (range fun p : ModelProd H H' ↦ (f p.1, p.2)) = range f ×ˢ (univ : Set H') := by
  rw [prod_range_univ_eq]
  rfl
#align model_prod_range_prod_id modelProd_range_prod_id

end

section

variable {ι : Type*} {Hi : ι → Type*}

-- Porting note: Old proof was `Pi.inhabited _`.
instance modelPiInhabited [∀ i, Inhabited (Hi i)] : Inhabited (ModelPi Hi) :=
  ⟨fun _ ↦ default⟩
#align model_pi_inhabited modelPiInhabited

instance [∀ i, TopologicalSpace (Hi i)] : TopologicalSpace (ModelPi Hi) :=
  Pi.topologicalSpace

end

/-- The product of two charted spaces is naturally a charted space, with the canonical
construction of the atlas of product maps. -/
instance prodChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (H' : Type*) [TopologicalSpace H'] (M' : Type*) [TopologicalSpace M']
    [ChartedSpace H' M'] : ChartedSpace (ModelProd H H') (M × M') where
  atlas := image2 LocalHomeomorph.prod (atlas H M) (atlas H' M')
  chartAt x := (chartAt H x.1).prod (chartAt H' x.2)
  mem_chart_source x := ⟨mem_chart_source H x.1, mem_chart_source H' x.2⟩
  chart_mem_atlas x := mem_image2_of_mem (chart_mem_atlas H x.1) (chart_mem_atlas H' x.2)
#align prod_charted_space prodChartedSpace

section prodChartedSpace

@[ext]
theorem ModelProd.ext {x y : ModelProd α β} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y :=
  Prod.ext h₁ h₂

variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {x : M × M'}

@[simp, mfld_simps]
theorem prodChartedSpace_chartAt :
    chartAt (ModelProd H H') x = (chartAt H x.fst).prod (chartAt H' x.snd) :=
  rfl
#align prod_charted_space_chart_at prodChartedSpace_chartAt

theorem chartedSpaceSelf_prod : prodChartedSpace H H H' H' = chartedSpaceSelf (H × H') := by
  ext1
  · simp [prodChartedSpace, atlas, ChartedSpace.atlas]
  · ext1
    simp only [prodChartedSpace_chartAt, chartAt_self_eq, refl_prod_refl]
    rfl
#align charted_space_self_prod chartedSpaceSelf_prod

end prodChartedSpace

/-- The product of a finite family of charted spaces is naturally a charted space, with the
canonical construction of the atlas of finite product maps. -/
instance piChartedSpace {ι : Type*} [Fintype ι] (H : ι → Type*) [∀ i, TopologicalSpace (H i)]
    (M : ι → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)] :
    ChartedSpace (ModelPi H) (∀ i, M i) where
  atlas := LocalHomeomorph.pi '' Set.pi univ fun _ ↦ atlas (H _) (M _)
  chartAt f := LocalHomeomorph.pi fun i ↦ chartAt (H i) (f i)
  mem_chart_source f i _ := mem_chart_source (H i) (f i)
  chart_mem_atlas f := mem_image_of_mem _ fun i _ ↦ chart_mem_atlas (H i) (f i)
#align pi_charted_space piChartedSpace

@[simp, mfld_simps]
theorem piChartedSpace_chartAt {ι : Type*} [Fintype ι] (H : ι → Type*)
    [∀ i, TopologicalSpace (H i)] (M : ι → Type*) [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (H i) (M i)] (f : ∀ i, M i) :
    chartAt (H := ModelPi H) f = LocalHomeomorph.pi fun i ↦ chartAt (H i) (f i) :=
  rfl
#align pi_charted_space_chart_at piChartedSpace_chartAt

end ChartedSpace

/-! ### Constructing a topology from an atlas -/


/-- Sometimes, one may want to construct a charted space structure on a space which does not yet
have a topological structure, where the topology would come from the charts. For this, one needs
charts that are only local equivs, and continuity properties for their composition.
This is formalised in `ChartedSpaceCore`. -/
-- @[nolint has_nonempty_instance]  -- Porting note: commented out
structure ChartedSpaceCore (H : Type*) [TopologicalSpace H] (M : Type*) where
  atlas : Set (LocalEquiv M H)
  chartAt : M → LocalEquiv M H
  mem_chart_source : ∀ x, x ∈ (chartAt x).source
  chart_mem_atlas : ∀ x, chartAt x ∈ atlas
  open_source : ∀ e e' : LocalEquiv M H, e ∈ atlas → e' ∈ atlas → IsOpen (e.symm.trans e').source
  continuous_toFun : ∀ e e' : LocalEquiv M H, e ∈ atlas → e' ∈ atlas →
    ContinuousOn (e.symm.trans e') (e.symm.trans e').source
#align charted_space_core ChartedSpaceCore

namespace ChartedSpaceCore

variable [TopologicalSpace H] (c : ChartedSpaceCore H M) {e : LocalEquiv M H}

/-- Topology generated by a set of charts on a Type. -/
protected def toTopologicalSpace : TopologicalSpace M :=
  TopologicalSpace.generateFrom <|
    ⋃ (e : LocalEquiv M H) (_ : e ∈ c.atlas) (s : Set H) (_ : IsOpen s),
      {e ⁻¹' s ∩ e.source}
#align charted_space_core.to_topological_space ChartedSpaceCore.toTopologicalSpace

theorem open_source' (he : e ∈ c.atlas) : IsOpen[c.toTopologicalSpace] e.source := by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_iUnion, mem_singleton_iff]
  refine' ⟨e, he, univ, isOpen_univ, _⟩
  simp only [Set.univ_inter, Set.preimage_univ]
#align charted_space_core.open_source' ChartedSpaceCore.open_source'

theorem open_target (he : e ∈ c.atlas) : IsOpen e.target := by
  have E : e.target ∩ e.symm ⁻¹' e.source = e.target :=
    Subset.antisymm (inter_subset_left _ _) fun x hx ↦
      ⟨hx, LocalEquiv.target_subset_preimage_source _ hx⟩
  simpa [LocalEquiv.trans_source, E] using c.open_source e e he he
#align charted_space_core.open_target ChartedSpaceCore.open_target

/-- An element of the atlas in a charted space without topology becomes a local homeomorphism
for the topology constructed from this atlas. The `localHomeomorph` version is given in this
definition. -/
protected def localHomeomorph (e : LocalEquiv M H) (he : e ∈ c.atlas) :
    @LocalHomeomorph M H c.toTopologicalSpace _ :=
  { c.toTopologicalSpace, e with
    open_source := by convert c.open_source' he
    open_target := by convert c.open_target he
    continuous_toFun := by
      letI : TopologicalSpace M := c.toTopologicalSpace
      rw [continuousOn_open_iff (c.open_source' he)]
      intro s s_open
      rw [inter_comm]
      apply TopologicalSpace.GenerateOpen.basic
      simp only [exists_prop, mem_iUnion, mem_singleton_iff]
      exact ⟨e, he, ⟨s, s_open, rfl⟩⟩
    continuous_invFun := by
      letI : TopologicalSpace M := c.toTopologicalSpace
      apply continuousOn_open_of_generateFrom
      intro t ht
      simp only [exists_prop, mem_iUnion, mem_singleton_iff] at ht
      rcases ht with ⟨e', e'_atlas, s, s_open, ts⟩
      rw [ts]
      let f := e.symm.trans e'
      have : IsOpen (f ⁻¹' s ∩ f.source) := by
        simpa [inter_comm] using (continuousOn_open_iff (c.open_source e e' he e'_atlas)).1
          (c.continuous_toFun e e' he e'_atlas) s s_open
      have A : e' ∘ e.symm ⁻¹' s ∩ (e.target ∩ e.symm ⁻¹' e'.source) =
          e.target ∩ (e' ∘ e.symm ⁻¹' s ∩ e.symm ⁻¹' e'.source) := by
        rw [← inter_assoc, ← inter_assoc]
        congr 1
        exact inter_comm _ _
      simpa [LocalEquiv.trans_source, preimage_inter, preimage_comp.symm, A] using this }
#align charted_space_core.local_homeomorph ChartedSpaceCore.localHomeomorph

/-- Given a charted space without topology, endow it with a genuine charted space structure with
respect to the topology constructed from the atlas. -/
def toChartedSpace : @ChartedSpace H _ M c.toTopologicalSpace :=
  { c.toTopologicalSpace with
    atlas := ⋃ (e : LocalEquiv M H) (he : e ∈ c.atlas), {c.localHomeomorph e he}
    chartAt := fun x ↦ c.localHomeomorph (c.chartAt x) (c.chart_mem_atlas x)
    mem_chart_source := fun x ↦ c.mem_chart_source x
    chart_mem_atlas := fun x ↦ by
      simp only [mem_iUnion, mem_singleton_iff]
      exact ⟨c.chartAt x, c.chart_mem_atlas x, rfl⟩}
#align charted_space_core.to_charted_space ChartedSpaceCore.toChartedSpace

end ChartedSpaceCore

/-! ### Charted space with a given structure groupoid -/


section HasGroupoid

variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/-- A charted space has an atlas in a groupoid `G` if the change of coordinates belong to the
groupoid. -/
class HasGroupoid {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (G : StructureGroupoid H) : Prop where
  compatible : ∀ {e e' : LocalHomeomorph M H}, e ∈ atlas H M → e' ∈ atlas H M → e.symm ≫ₕ e' ∈ G
#align has_groupoid HasGroupoid

/-- Reformulate in the `StructureGroupoid` namespace the compatibility condition of charts in a
charted space admitting a structure groupoid, to make it more easily accessible with dot
notation. -/
theorem StructureGroupoid.compatible {H : Type*} [TopologicalSpace H] (G : StructureGroupoid H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G]
    {e e' : LocalHomeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) : e.symm ≫ₕ e' ∈ G :=
  HasGroupoid.compatible he he'
#align structure_groupoid.compatible StructureGroupoid.compatible

theorem hasGroupoid_of_le {G₁ G₂ : StructureGroupoid H} (h : HasGroupoid M G₁) (hle : G₁ ≤ G₂) :
    HasGroupoid M G₂ :=
  ⟨fun he he' ↦ hle (h.compatible he he')⟩
#align has_groupoid_of_le hasGroupoid_of_le

theorem hasGroupoid_of_pregroupoid (PG : Pregroupoid H) (h : ∀ {e e' : LocalHomeomorph M H},
      e ∈ atlas H M → e' ∈ atlas H M → PG.property (e.symm ≫ₕ e') (e.symm ≫ₕ e').source) :
    HasGroupoid M PG.groupoid :=
  ⟨fun he he' ↦ mem_groupoid_of_pregroupoid.mpr ⟨h he he', h he' he⟩⟩
#align has_groupoid_of_pregroupoid hasGroupoid_of_pregroupoid

/-- The trivial charted space structure on the model space is compatible with any groupoid. -/
instance hasGroupoid_model_space (H : Type*) [TopologicalSpace H] (G : StructureGroupoid H) :
    HasGroupoid H G where
  compatible {e e'} he he' := by
    rw [chartedSpaceSelf_atlas] at he he'
    simp [he, he', StructureGroupoid.id_mem]
#align has_groupoid_model_space hasGroupoid_model_space

/-- Any charted space structure is compatible with the groupoid of all local homeomorphisms. -/
instance hasGroupoid_continuousGroupoid : HasGroupoid M (continuousGroupoid H) := by
  refine' ⟨fun _ _ ↦ _⟩
  rw [continuousGroupoid, mem_groupoid_of_pregroupoid]
  simp only [and_self_iff]
#align has_groupoid_continuous_groupoid hasGroupoid_continuousGroupoid

section MaximalAtlas

variable (M) (G : StructureGroupoid H)

/-- Given a charted space admitting a structure groupoid, the maximal atlas associated to this
structure groupoid is the set of all local charts that are compatible with the atlas, i.e., such
that changing coordinates with an atlas member gives an element of the groupoid. -/
def StructureGroupoid.maximalAtlas : Set (LocalHomeomorph M H) :=
  { e | ∀ e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G }
#align structure_groupoid.maximal_atlas StructureGroupoid.maximalAtlas

variable {M}

/-- The elements of the atlas belong to the maximal atlas for any structure groupoid. -/
theorem StructureGroupoid.subset_maximalAtlas [HasGroupoid M G] : atlas H M ⊆ G.maximalAtlas M :=
  fun _ he _ he' ↦ ⟨G.compatible he he', G.compatible he' he⟩
#align structure_groupoid.subset_maximal_atlas StructureGroupoid.subset_maximalAtlas

theorem StructureGroupoid.chart_mem_maximalAtlas [HasGroupoid M G] (x : M) :
    chartAt H x ∈ G.maximalAtlas M :=
  G.subset_maximalAtlas (chart_mem_atlas H x)
#align structure_groupoid.chart_mem_maximal_atlas StructureGroupoid.chart_mem_maximalAtlas

variable {G}

theorem mem_maximalAtlas_iff {e : LocalHomeomorph M H} :
    e ∈ G.maximalAtlas M ↔ ∀ e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G :=
  Iff.rfl
#align mem_maximal_atlas_iff mem_maximalAtlas_iff

/-- Changing coordinates between two elements of the maximal atlas gives rise to an element
of the structure groupoid. -/
theorem StructureGroupoid.compatible_of_mem_maximalAtlas {e e' : LocalHomeomorph M H}
    (he : e ∈ G.maximalAtlas M) (he' : e' ∈ G.maximalAtlas M) : e.symm ≫ₕ e' ∈ G := by
  refine' G.locality fun x hx ↦ _
  set f := chartAt (H := H) (e.symm x)
  let s := e.target ∩ e.symm ⁻¹' f.source
  have hs : IsOpen s := by
    apply e.symm.continuous_toFun.preimage_open_of_open <;> apply open_source
  have xs : x ∈ s := by
    simp only [mem_inter_iff, mem_preimage, mem_chart_source, and_true]
    exact ((mem_inter_iff _ _ _).1 hx).1
  refine' ⟨s, hs, xs, _⟩
  have A : e.symm ≫ₕ f ∈ G := (mem_maximalAtlas_iff.1 he f (chart_mem_atlas _ _)).1
  have B : f.symm ≫ₕ e' ∈ G := (mem_maximalAtlas_iff.1 he' f (chart_mem_atlas _ _)).2
  have C : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ∈ G := G.trans A B
  have D : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ≈ (e.symm ≫ₕ e').restr s := calc
    (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' = e.symm ≫ₕ (f ≫ₕ f.symm) ≫ₕ e' := by simp only [trans_assoc]
    _ ≈ e.symm ≫ₕ ofSet f.source f.open_source ≫ₕ e' :=
      EqOnSource.trans' (refl _) (EqOnSource.trans' (trans_self_symm _) (refl _))
    _ ≈ (e.symm ≫ₕ ofSet f.source f.open_source) ≫ₕ e' := by rw [trans_assoc]
    _ ≈ e.symm.restr s ≫ₕ e' := by rw [trans_of_set']; apply refl
    _ ≈ (e.symm ≫ₕ e').restr s := by rw [restr_trans]
  exact G.eq_on_source C (Setoid.symm D)
#align structure_groupoid.compatible_of_mem_maximal_atlas StructureGroupoid.compatible_of_mem_maximalAtlas

variable (G)

/-- In the model space, the identity is in any maximal atlas. -/
theorem StructureGroupoid.id_mem_maximalAtlas : LocalHomeomorph.refl H ∈ G.maximalAtlas H :=
  G.subset_maximalAtlas <| by simp
#align structure_groupoid.id_mem_maximal_atlas StructureGroupoid.id_mem_maximalAtlas

/-- In the model space, any element of the groupoid is in the maximal atlas. -/
theorem StructureGroupoid.mem_maximalAtlas_of_mem_groupoid {f : LocalHomeomorph H H} (hf : f ∈ G) :
    f ∈ G.maximalAtlas H := by
  rintro e (rfl : e = LocalHomeomorph.refl H)
  exact ⟨G.trans (G.symm hf) G.id_mem, G.trans (G.symm G.id_mem) hf⟩
#align structure_groupoid.mem_maximal_atlas_of_mem_groupoid StructureGroupoid.mem_maximalAtlas_of_mem_groupoid

end MaximalAtlas

section Singleton

variable {α : Type*} [TopologicalSpace α]

namespace LocalHomeomorph

variable (e : LocalHomeomorph α H)

/-- If a single local homeomorphism `e` from a space `α` into `H` has source covering the whole
space `α`, then that local homeomorphism induces an `H`-charted space structure on `α`.
(This condition is equivalent to `e` being an open embedding of `α` into `H`; see
`OpenEmbedding.singletonChartedSpace`.) -/
def singletonChartedSpace (h : e.source = Set.univ) : ChartedSpace H α where
  atlas := {e}
  chartAt _ := e
  mem_chart_source _ := by rw [h]; apply mem_univ
  chart_mem_atlas _ := by tauto
#align local_homeomorph.singleton_charted_space LocalHomeomorph.singletonChartedSpace

@[simp, mfld_simps]
theorem singletonChartedSpace_chartAt_eq (h : e.source = Set.univ) {x : α} :
    @chartAt H _ α _ (e.singletonChartedSpace h) x = e :=
  rfl
#align local_homeomorph.singleton_charted_space_chart_at_eq LocalHomeomorph.singletonChartedSpace_chartAt_eq

theorem singletonChartedSpace_chartAt_source (h : e.source = Set.univ) {x : α} :
    (@chartAt H _ α _ (e.singletonChartedSpace h) x).source = Set.univ :=
  h
#align local_homeomorph.singleton_charted_space_chart_at_source LocalHomeomorph.singletonChartedSpace_chartAt_source

theorem singletonChartedSpace_mem_atlas_eq (h : e.source = Set.univ) (e' : LocalHomeomorph α H)
    (h' : e' ∈ (e.singletonChartedSpace h).atlas) : e' = e :=
  h'
#align local_homeomorph.singleton_charted_space_mem_atlas_eq LocalHomeomorph.singletonChartedSpace_mem_atlas_eq

/-- Given a local homeomorphism `e` from a space `α` into `H`, if its source covers the whole
space `α`, then the induced charted space structure on `α` is `HasGroupoid G` for any structure
groupoid `G` which is closed under restrictions. -/
theorem singleton_hasGroupoid (h : e.source = Set.univ) (G : StructureGroupoid H)
    [ClosedUnderRestriction G] : @HasGroupoid _ _ _ _ (e.singletonChartedSpace h) G :=
  { e.singletonChartedSpace h with
    compatible := by
      intro e' e'' he' he''
      rw [e.singletonChartedSpace_mem_atlas_eq h e' he',
        e.singletonChartedSpace_mem_atlas_eq h e'' he'']
      refine' G.eq_on_source _ e.trans_symm_self
      have hle : idRestrGroupoid ≤ G := (closedUnderRestriction_iff_id_le G).mp (by assumption)
      exact StructureGroupoid.le_iff.mp hle _ (idRestrGroupoid_mem _) }
#align local_homeomorph.singleton_has_groupoid LocalHomeomorph.singleton_hasGroupoid

end LocalHomeomorph

namespace OpenEmbedding

variable [Nonempty α]

/-- An open embedding of `α` into `H` induces an `H`-charted space structure on `α`.
See `LocalHomeomorph.singletonChartedSpace`. -/
def singletonChartedSpace {f : α → H} (h : OpenEmbedding f) : ChartedSpace H α :=
  (h.toLocalHomeomorph f).singletonChartedSpace (toLocalHomeomorph_source _ _)
#align open_embedding.singleton_charted_space OpenEmbedding.singletonChartedSpace

theorem singletonChartedSpace_chartAt_eq {f : α → H} (h : OpenEmbedding f) {x : α} :
    ⇑(@chartAt H _ α _ h.singletonChartedSpace x) = f :=
  rfl
#align open_embedding.singleton_charted_space_chart_at_eq OpenEmbedding.singletonChartedSpace_chartAt_eq

theorem singleton_hasGroupoid {f : α → H} (h : OpenEmbedding f) (G : StructureGroupoid H)
    [ClosedUnderRestriction G] : @HasGroupoid _ _ _ _ h.singletonChartedSpace G :=
  (h.toLocalHomeomorph f).singleton_hasGroupoid (toLocalHomeomorph_source _ _) G
#align open_embedding.singleton_has_groupoid OpenEmbedding.singleton_hasGroupoid

end OpenEmbedding

end Singleton

namespace TopologicalSpace.Opens

open TopologicalSpace

variable (G : StructureGroupoid H) [HasGroupoid M G]

variable (s : Opens M)

/-- An open subset of a charted space is naturally a charted space. -/
protected instance instChartedSpace : ChartedSpace H s where
  atlas := ⋃ x : s, {@LocalHomeomorph.subtypeRestr _ _ _ _ (chartAt H x.1) s ⟨x⟩}
  chartAt x := @LocalHomeomorph.subtypeRestr _ _ _ _ (chartAt H x.1) s ⟨x⟩
  mem_chart_source x := ⟨trivial, mem_chart_source H x.1⟩
  chart_mem_atlas x := by
    simp only [mem_iUnion, mem_singleton_iff]
    use x
#align topological_space.opens.charted_space TopologicalSpace.Opens.instChartedSpace

/-- If a groupoid `G` is `ClosedUnderRestriction`, then an open subset of a space which is
`HasGroupoid G` is naturally `HasGroupoid G`. -/
protected instance instHasGroupoid [ClosedUnderRestriction G] : HasGroupoid s G where
  compatible := by
    rintro e e' ⟨_, ⟨x, hc⟩, he⟩ ⟨_, ⟨x', hc'⟩, he'⟩
    haveI : Nonempty s := ⟨x⟩
    have asdf := he
    rw [hc.symm, mem_singleton_iff] at he
    rw [hc'.symm, mem_singleton_iff] at he'
    rw [he, he']
    refine' G.eq_on_source _ (subtypeRestr_symm_trans_subtypeRestr s (chartAt H x) (chartAt H x'))
    apply closedUnderRestriction'
    · exact G.compatible (chart_mem_atlas _ _) (chart_mem_atlas _ _)
    · exact preimage_open_of_open_symm (chartAt _ _) s.2
#align topological_space.opens.has_groupoid TopologicalSpace.Opens.instHasGroupoid

theorem chartAt_inclusion_symm_eventuallyEq {U V : Opens M} (hUV : U ≤ V) {x : U} :
    (chartAt H (Set.inclusion hUV x)).symm
    =ᶠ[𝓝 (chartAt H (Set.inclusion hUV x) (Set.inclusion hUV x))]
    Set.inclusion hUV ∘ (chartAt H x).symm := by
  set i := Set.inclusion hUV
  set e := chartAt H (x : M)
  haveI : Nonempty U := ⟨x⟩
  haveI : Nonempty V := ⟨i x⟩
  have heUx_nhds : (e.subtypeRestr U).target ∈ 𝓝 (e x) := by
    apply (e.subtypeRestr U).open_target.mem_nhds
    exact e.map_subtype_source (mem_chart_source _ _)
  exact Filter.eventuallyEq_of_mem heUx_nhds (e.subtypeRestr_symm_eqOn_of_le hUV)
#align topological_space.opens.chart_at_inclusion_symm_eventually_eq TopologicalSpace.Opens.chartAt_inclusion_symm_eventuallyEq

end TopologicalSpace.Opens

/-! ### Structomorphisms -/

/-- A `G`-diffeomorphism between two charted spaces is a homeomorphism which, when read in the
charts, belongs to `G`. We avoid the word diffeomorph as it is too related to the smooth category,
and use structomorph instead. -/
-- @[nolint has_nonempty_instance]  -- Porting note: commented out
structure Structomorph (G : StructureGroupoid H) (M : Type*) (M' : Type*) [TopologicalSpace M]
  [TopologicalSpace M'] [ChartedSpace H M] [ChartedSpace H M'] extends Homeomorph M M' where
  mem_groupoid : ∀ c : LocalHomeomorph M H, ∀ c' : LocalHomeomorph M' H, c ∈ atlas H M →
    c' ∈ atlas H M' → c.symm ≫ₕ toHomeomorph.toLocalHomeomorph ≫ₕ c' ∈ G
#align structomorph Structomorph

variable [TopologicalSpace M'] [TopologicalSpace M''] {G : StructureGroupoid H} [ChartedSpace H M']
  [ChartedSpace H M'']

/-- The identity is a diffeomorphism of any charted space, for any groupoid. -/
def Structomorph.refl (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G] :
    Structomorph G M M :=
  { Homeomorph.refl M with
    mem_groupoid := fun c c' hc hc' ↦ by
      change LocalHomeomorph.symm c ≫ₕ LocalHomeomorph.refl M ≫ₕ c' ∈ G
      rw [LocalHomeomorph.refl_trans]
      exact G.compatible hc hc' }
#align structomorph.refl Structomorph.refl

/-- The inverse of a structomorphism is a structomorphism. -/
def Structomorph.symm (e : Structomorph G M M') : Structomorph G M' M :=
  { e.toHomeomorph.symm with
    mem_groupoid := by
      intro c c' hc hc'
      have : (c'.symm ≫ₕ e.toHomeomorph.toLocalHomeomorph ≫ₕ c).symm ∈ G :=
        G.symm (e.mem_groupoid c' c hc' hc)
      rwa [trans_symm_eq_symm_trans_symm, trans_symm_eq_symm_trans_symm, symm_symm, trans_assoc]
        at this }
#align structomorph.symm Structomorph.symm

/-- The composition of structomorphisms is a structomorphism. -/
def Structomorph.trans (e : Structomorph G M M') (e' : Structomorph G M' M'') :
    Structomorph G M M'' :=
  { Homeomorph.trans e.toHomeomorph e'.toHomeomorph with
    mem_groupoid := by
      /- Let c and c' be two charts in M and M''. We want to show that e' ∘ e is smooth in these
      charts, around any point x. For this, let y = e (c⁻¹ x), and consider a chart g around y.
      Then g ∘ e ∘ c⁻¹ and c' ∘ e' ∘ g⁻¹ are both smooth as e and e' are structomorphisms, so
      their composition is smooth, and it coincides with c' ∘ e' ∘ e ∘ c⁻¹ around x. -/
      intro c c' hc hc'
      refine' G.locality fun x hx ↦ _
      let f₁ := e.toHomeomorph.toLocalHomeomorph
      let f₂ := e'.toHomeomorph.toLocalHomeomorph
      let f := (e.toHomeomorph.trans e'.toHomeomorph).toLocalHomeomorph
      have feq : f = f₁ ≫ₕ f₂ := Homeomorph.trans_toLocalHomeomorph _ _
      -- define the atlas g around y
      let y := (c.symm ≫ₕ f₁) x
      let g := chartAt (H := H) y
      have hg₁ := chart_mem_atlas (H := H) y
      have hg₂ := mem_chart_source (H := H) y
      let s := (c.symm ≫ₕ f₁).source ∩ c.symm ≫ₕ f₁ ⁻¹' g.source
      have open_s : IsOpen s := by
        apply (c.symm ≫ₕ f₁).continuous_toFun.preimage_open_of_open <;> apply open_source
      have : x ∈ s := by
        constructor
        · simp only [trans_source, preimage_univ, inter_univ, Homeomorph.toLocalHomeomorph_source]
          rw [trans_source] at hx
          exact hx.1
        · exact hg₂
      refine' ⟨s, open_s, this, _⟩
      let F₁ := (c.symm ≫ₕ f₁ ≫ₕ g) ≫ₕ g.symm ≫ₕ f₂ ≫ₕ c'
      have A : F₁ ∈ G := G.trans (e.mem_groupoid c g hc hg₁) (e'.mem_groupoid g c' hg₁ hc')
      let F₂ := (c.symm ≫ₕ f ≫ₕ c').restr s
      have : F₁ ≈ F₂ := calc
        F₁ ≈ c.symm ≫ₕ f₁ ≫ₕ (g ≫ₕ g.symm) ≫ₕ f₂ ≫ₕ c' := by simp only [trans_assoc, _root_.refl]
        _ ≈ c.symm ≫ₕ f₁ ≫ₕ ofSet g.source g.open_source ≫ₕ f₂ ≫ₕ c' :=
          EqOnSource.trans' (_root_.refl _) (EqOnSource.trans' (_root_.refl _)
            (EqOnSource.trans' (trans_self_symm g) (_root_.refl _)))
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ ofSet g.source g.open_source) ≫ₕ f₂ ≫ₕ c' :=
          by simp only [trans_assoc, _root_.refl]
        _ ≈ (c.symm ≫ₕ f₁).restr s ≫ₕ f₂ ≫ₕ c' := by rw [trans_of_set']
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ f₂ ≫ₕ c').restr s := by rw [restr_trans]
        _ ≈ (c.symm ≫ₕ (f₁ ≫ₕ f₂) ≫ₕ c').restr s :=
          by simp only [EqOnSource.restr, trans_assoc, _root_.refl]
        _ ≈ F₂ := by simp only [feq, _root_.refl]
      have : F₂ ∈ G := G.eq_on_source A (Setoid.symm this)
      exact this }
#align structomorph.trans Structomorph.trans

end HasGroupoid

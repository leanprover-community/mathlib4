/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Order.Filter.SmallSets
import Mathlib.Tactic.Monotonicity.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.NhdsSet
import Mathlib.Algebra.Group.Defs
import Mathlib.Topology.ContinuousOn

/-!
# Uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* uniform continuity (in this file)
* completeness (in `Cauchy.lean`)
* extension of uniform continuous functions to complete spaces (in `IsUniformEmbedding.lean`)
* totally bounded sets (in `Cauchy.lean`)
* totally bounded complete sets are compact (in `Cauchy.lean`)

A uniform structure on a type `X` is a filter `𝓤 X` on `X × X` satisfying some conditions
which makes it reasonable to say that `∀ᶠ (p : X × X) in 𝓤 X, ...` means
"for all p.1 and p.2 in X close enough, ...". Elements of this filter are called entourages
of `X`. The two main examples are:

* If `X` is a metric space, `V ∈ 𝓤 X ↔ ∃ ε > 0, { p | dist p.1 p.2 < ε } ⊆ V`
* If `G` is an additive topological group, `V ∈ 𝓤 G ↔ ∃ U ∈ 𝓝 (0 : G), {p | p.2 - p.1 ∈ U} ⊆ V`

Those examples are generalizations in two different directions of the elementary example where
`X = ℝ` and `V ∈ 𝓤 ℝ ↔ ∃ ε > 0, { p | |p.2 - p.1| < ε } ⊆ V` which features both the topological
group structure on `ℝ` and its metric space structure.

Each uniform structure on `X` induces a topology on `X` characterized by

> `nhds_eq_comap_uniformity : ∀ {x : X}, 𝓝 x = comap (Prod.mk x) (𝓤 X)`

where `Prod.mk x : X → X × X := (fun y ↦ (x, y))` is the partial evaluation of the product
constructor.

The dictionary with metric spaces includes:
* an upper bound for `dist x y` translates into `(x, y) ∈ V` for some `V ∈ 𝓤 X`
* a ball `ball x r` roughly corresponds to `UniformSpace.ball x V := {y | (x, y) ∈ V}`
  for some `V ∈ 𝓤 X`, but the later is more general (it includes in
  particular both open and closed balls for suitable `V`).
  In particular we have:
  `isOpen_iff_ball_subset {s : Set X} : IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 X, ball x V ⊆ s`

The triangle inequality is abstracted to a statement involving the composition of relations in `X`.
First note that the triangle inequality in a metric space is equivalent to
`∀ (x y z : X) (r r' : ℝ), dist x y ≤ r → dist y z ≤ r' → dist x z ≤ r + r'`.
Then, for any `V` and `W` with type `Set (X × X)`, the composition `V ○ W : Set (X × X)` is
defined as `{ p : X × X | ∃ z, (p.1, z) ∈ V ∧ (z, p.2) ∈ W }`.
In the metric space case, if `V = { p | dist p.1 p.2 ≤ r }` and `W = { p | dist p.1 p.2 ≤ r' }`
then the triangle inequality, as reformulated above, says `V ○ W` is contained in
`{p | dist p.1 p.2 ≤ r + r'}` which is the entourage associated to the radius `r + r'`.
In general we have `mem_ball_comp (h : y ∈ ball x V) (h' : z ∈ ball y W) : z ∈ ball x (V ○ W)`.
Note that this discussion does not depend on any axiom imposed on the uniformity filter,
it is simply captured by the definition of composition.

The uniform space axioms ask the filter `𝓤 X` to satisfy the following:
* every `V ∈ 𝓤 X` contains the diagonal `idRel = { p | p.1 = p.2 }`. This abstracts the fact
  that `dist x x ≤ r` for every non-negative radius `r` in the metric space case and also that
  `x - x` belongs to every neighborhood of zero in the topological group case.
* `V ∈ 𝓤 X → Prod.swap '' V ∈ 𝓤 X`. This is tightly related the fact that `dist x y = dist y x`
  in a metric space, and to continuity of negation in the topological group case.
* `∀ V ∈ 𝓤 X, ∃ W ∈ 𝓤 X, W ○ W ⊆ V`. In the metric space case, it corresponds
  to cutting the radius of a ball in half and applying the triangle inequality.
  In the topological group case, it comes from continuity of addition at `(0, 0)`.

These three axioms are stated more abstractly in the definition below, in terms of
operations on filters, without directly manipulating entourages.

## Main definitions

* `UniformSpace X` is a uniform space structure on a type `X`
* `UniformContinuous f` is a predicate saying a function `f : α → β` between uniform spaces
  is uniformly continuous : `∀ r ∈ 𝓤 β, ∀ᶠ (x : α × α) in 𝓤 α, (f x.1, f x.2) ∈ r`

In this file we also define a complete lattice structure on the type `UniformSpace X`
of uniform structures on `X`, as well as the pullback (`UniformSpace.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notations

Localized in `Uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`,
and `○` for composition of relations, seen as terms with type `Set (X × X)`.

## Implementation notes

There is already a theory of relations in `Data/Rel.lean` where the main definition is
`def Rel (α β : Type*) := α → β → Prop`.
The relations used in the current file involve only one type, but this is not the reason why
we don't reuse `Data/Rel.lean`. We use `Set (α × α)`
instead of `Rel α α` because we really need sets to use the filter library, and elements
of filters on `α × α` have type `Set (α × α)`.

The structure `UniformSpace X` bundles a uniform structure on `X`, a topology on `X` and
an assumption saying those are compatible. This may not seem mathematically reasonable at first,
but is in fact an instance of the forgetful inheritance pattern. See Note [forgetful inheritance]
below.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/

open Set Filter Topology

universe u v ua ub uc ud

/-!
### Relations, seen as `Set (α × α)`
-/


variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

/-- The identity relation, or the graph of the identity function -/
def idRel {α : Type*} :=
  { p : α × α | p.1 = p.2 }

@[simp]
theorem mem_idRel {a b : α} : (a, b) ∈ @idRel α ↔ a = b :=
  Iff.rfl

@[simp]
theorem idRel_subset {s : Set (α × α)} : idRel ⊆ s ↔ ∀ a, (a, a) ∈ s := by
  simp [subset_def]

theorem eq_singleton_left_of_prod_subset_idRel {X : Type _} {S T : Set X} (hS : S.Nonempty)
    (hT : T.Nonempty) (h_diag : S ×ˢ T ⊆ idRel) : ∃ x, S = {x} := by
  rcases hS, hT with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  refine ⟨s, eq_singleton_iff_nonempty_unique_mem.mpr ⟨⟨s, hs⟩, fun x hx ↦ ?_⟩⟩
  rw [prod_subset_iff] at h_diag
  replace hs := h_diag s hs t ht
  replace hx := h_diag x hx t ht
  simp only [idRel, mem_setOf_eq] at hx hs
  rwa [← hs] at hx

theorem eq_singleton_right_prod_subset_idRel {X : Type _} {S T : Set X} (hS : S.Nonempty)
    (hT : T.Nonempty) (h_diag : S ×ˢ T ⊆ idRel) : ∃ x, T = {x} := by
  rw [Set.prod_subset_iff] at h_diag
  replace h_diag := fun x hx y hy => (h_diag y hy x hx).symm
  exact eq_singleton_left_of_prod_subset_idRel hT hS (prod_subset_iff.mpr h_diag)

theorem eq_singleton_prod_subset_idRel {X : Type _} {S T : Set X} (hS : S.Nonempty)
    (hT : T.Nonempty) (h_diag : S ×ˢ T ⊆ idRel) : ∃ x, S = {x} ∧ T = {x} := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := eq_singleton_left_of_prod_subset_idRel hS hT h_diag,
    eq_singleton_right_prod_subset_idRel hS hT h_diag
  refine ⟨x, ⟨hx, ?_⟩⟩
  rw [hy, Set.singleton_eq_singleton_iff]
  exact (Set.prod_subset_iff.mp h_diag x (by simp only [hx, Set.mem_singleton]) y
    (by simp only [hy, Set.mem_singleton])).symm

/-- The composition of relations -/
def compRel (r₁ r₂ : Set (α × α)) :=
  { p : α × α | ∃ z : α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂ }

@[inherit_doc]
scoped[Uniformity] infixl:62 " ○ " => compRel
open Uniformity

@[simp]
theorem mem_compRel {α : Type u} {r₁ r₂ : Set (α × α)} {x y : α} :
    (x, y) ∈ r₁ ○ r₂ ↔ ∃ z, (x, z) ∈ r₁ ∧ (z, y) ∈ r₂ :=
  Iff.rfl

@[simp]
theorem swap_idRel : Prod.swap '' idRel = @idRel α :=
  Set.ext fun ⟨a, b⟩ => by simpa [image_swap_eq_preimage_swap] using eq_comm

theorem Monotone.compRel [Preorder β] {f g : β → Set (α × α)} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ○ g x := fun _ _ h _ ⟨z, h₁, h₂⟩ => ⟨z, hf h h₁, hg h h₂⟩

@[mono, gcongr]
theorem compRel_mono {f g h k : Set (α × α)} (h₁ : f ⊆ h) (h₂ : g ⊆ k) : f ○ g ⊆ h ○ k :=
  fun _ ⟨z, h, h'⟩ => ⟨z, h₁ h, h₂ h'⟩

theorem prod_mk_mem_compRel {a b c : α} {s t : Set (α × α)} (h₁ : (a, c) ∈ s) (h₂ : (c, b) ∈ t) :
    (a, b) ∈ s ○ t :=
  ⟨c, h₁, h₂⟩

@[simp]
theorem id_compRel {r : Set (α × α)} : idRel ○ r = r :=
  Set.ext fun ⟨a, b⟩ => by simp

theorem compRel_assoc {r s t : Set (α × α)} : r ○ s ○ t = r ○ (s ○ t) := by
  ext ⟨a, b⟩; simp only [mem_compRel]; tauto

theorem left_subset_compRel {s t : Set (α × α)} (h : idRel ⊆ t) : s ⊆ s ○ t := fun ⟨_x, y⟩ xy_in =>
  ⟨y, xy_in, h <| rfl⟩

theorem right_subset_compRel {s t : Set (α × α)} (h : idRel ⊆ s) : t ⊆ s ○ t := fun ⟨x, _y⟩ xy_in =>
  ⟨x, h <| rfl, xy_in⟩

theorem subset_comp_self {s : Set (α × α)} (h : idRel ⊆ s) : s ⊆ s ○ s :=
  left_subset_compRel h

theorem subset_iterate_compRel {s t : Set (α × α)} (h : idRel ⊆ s) (n : ℕ) :
    t ⊆ (s ○ ·)^[n] t := by
  induction' n with n ihn generalizing t
  exacts [Subset.rfl, (right_subset_compRel h).trans ihn]

/-- The relation is invariant under swapping factors. -/
def SymmetricRel (V : Set (α × α)) : Prop :=
  Prod.swap ⁻¹' V = V

/-- The maximal symmetric relation contained in a given relation. -/
def symmetrizeRel (V : Set (α × α)) : Set (α × α) :=
  V ∩ Prod.swap ⁻¹' V

theorem symmetric_symmetrizeRel (V : Set (α × α)) : SymmetricRel (symmetrizeRel V) := by
  simp [SymmetricRel, symmetrizeRel, preimage_inter, inter_comm, ← preimage_comp]

theorem symmetrizeRel_subset_self (V : Set (α × α)) : symmetrizeRel V ⊆ V :=
  sep_subset _ _

@[mono]
theorem symmetrize_mono {V W : Set (α × α)} (h : V ⊆ W) : symmetrizeRel V ⊆ symmetrizeRel W :=
  inter_subset_inter h <| preimage_mono h

theorem SymmetricRel.mk_mem_comm {V : Set (α × α)} (hV : SymmetricRel V) {x y : α} :
    (x, y) ∈ V ↔ (y, x) ∈ V :=
  Set.ext_iff.1 hV (y, x)

theorem SymmetricRel.eq {U : Set (α × α)} (hU : SymmetricRel U) : Prod.swap ⁻¹' U = U :=
  hU

theorem SymmetricRel.inter {U V : Set (α × α)} (hU : SymmetricRel U) (hV : SymmetricRel V) :
    SymmetricRel (U ∩ V) := by rw [SymmetricRel, preimage_inter, hU.eq, hV.eq]

/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure UniformSpace.Core (α : Type u) where
  /-- The uniformity filter. Once `UniformSpace` is defined, `𝓤 α` (`_root_.uniformity`) becomes the
  normal form. -/
  uniformity : Filter (α × α)
  /-- Every set in the uniformity filter includes the diagonal. -/
  refl : 𝓟 idRel ≤ uniformity
  /-- If `s ∈ uniformity`, then `Prod.swap ⁻¹' s ∈ uniformity`. -/
  symm : Tendsto Prod.swap uniformity uniformity
  /-- For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆ u`. -/
  comp : (uniformity.lift' fun s => s ○ s) ≤ uniformity

protected theorem UniformSpace.Core.comp_mem_uniformity_sets {c : Core α} {s : Set (α × α)}
    (hs : s ∈ c.uniformity) : ∃ t ∈ c.uniformity, t ○ t ⊆ s :=
  (mem_lift'_sets <| monotone_id.compRel monotone_id).mp <| c.comp hs

/-- An alternative constructor for `UniformSpace.Core`. This version unfolds various
`Filter`-related definitions. -/
def UniformSpace.Core.mk' {α : Type u} (U : Filter (α × α)) (refl : ∀ r ∈ U, ∀ (x), (x, x) ∈ r)
    (symm : ∀ r ∈ U, Prod.swap ⁻¹' r ∈ U) (comp : ∀ r ∈ U, ∃ t ∈ U, t ○ t ⊆ r) :
    UniformSpace.Core α :=
  ⟨U, fun _r ru => idRel_subset.2 (refl _ ru), symm, fun _r ru =>
    let ⟨_s, hs, hsr⟩ := comp _ ru
    mem_of_superset (mem_lift' hs) hsr⟩

/-- Defining a `UniformSpace.Core` from a filter basis satisfying some uniformity-like axioms. -/
def UniformSpace.Core.mkOfBasis {α : Type u} (B : FilterBasis (α × α))
    (refl : ∀ r ∈ B, ∀ (x), (x, x) ∈ r) (symm : ∀ r ∈ B, ∃ t ∈ B, t ⊆ Prod.swap ⁻¹' r)
    (comp : ∀ r ∈ B, ∃ t ∈ B, t ○ t ⊆ r) : UniformSpace.Core α where
  uniformity := B.filter
  refl := B.hasBasis.ge_iff.mpr fun _r ru => idRel_subset.2 <| refl _ ru
  symm := (B.hasBasis.tendsto_iff B.hasBasis).mpr symm
  comp := (HasBasis.le_basis_iff (B.hasBasis.lift' (monotone_id.compRel monotone_id))
    B.hasBasis).2 comp

/-- A uniform space generates a topological space -/
def UniformSpace.Core.toTopologicalSpace {α : Type u} (u : UniformSpace.Core α) :
    TopologicalSpace α :=
  .mkOfNhds fun x ↦ .comap (Prod.mk x) u.uniformity

theorem UniformSpace.Core.ext :
    ∀ {u₁ u₂ : UniformSpace.Core α}, u₁.uniformity = u₂.uniformity → u₁ = u₂
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

theorem UniformSpace.Core.nhds_toTopologicalSpace {α : Type u} (u : Core α) (x : α) :
    @nhds α u.toTopologicalSpace x = comap (Prod.mk x) u.uniformity := by
  apply TopologicalSpace.nhds_mkOfNhds_of_hasBasis (fun _ ↦ (basis_sets _).comap _)
  · exact fun a U hU ↦ u.refl hU rfl
  · intro a U hU
    rcases u.comp_mem_uniformity_sets hU with ⟨V, hV, hVU⟩
    filter_upwards [preimage_mem_comap hV] with b hb
    filter_upwards [preimage_mem_comap hV] with c hc
    exact hVU ⟨b, hb, hc⟩

-- the topological structure is embedded in the uniform structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `α × α` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
class UniformSpace (α : Type u) extends TopologicalSpace α where
  /-- The uniformity filter. -/
  protected uniformity : Filter (α × α)
  /-- If `s ∈ uniformity`, then `Prod.swap ⁻¹' s ∈ uniformity`. -/
  protected symm : Tendsto Prod.swap uniformity uniformity
  /-- For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆ u`. -/
  protected comp : (uniformity.lift' fun s => s ○ s) ≤ uniformity
  /-- The uniformity agrees with the topology: the neighborhoods filter of each point `x`
  is equal to `Filter.comap (Prod.mk x) (𝓤 α)`. -/
  protected nhds_eq_comap_uniformity (x : α) : 𝓝 x = comap (Prod.mk x) uniformity

/-- The uniformity is a filter on α × α (inferred from an ambient uniform space
  structure on α). -/
def uniformity (α : Type u) [UniformSpace α] : Filter (α × α) :=
  @UniformSpace.uniformity α _

/-- Notation for the uniformity filter with respect to a non-standard `UniformSpace` instance. -/
scoped[Uniformity] notation "𝓤[" u "]" => @uniformity _ u

@[inherit_doc] -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: should we drop the `uniformity` def?
scoped[Uniformity] notation "𝓤" => uniformity

/-- Construct a `UniformSpace` from a `u : UniformSpace.Core` and a `TopologicalSpace` structure
that is equal to `u.toTopologicalSpace`. -/
abbrev UniformSpace.ofCoreEq {α : Type u} (u : UniformSpace.Core α) (t : TopologicalSpace α)
    (h : t = u.toTopologicalSpace) : UniformSpace α where
  __ := u
  toTopologicalSpace := t
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_toTopologicalSpace]

/-- Construct a `UniformSpace` from a `UniformSpace.Core`. -/
abbrev UniformSpace.ofCore {α : Type u} (u : UniformSpace.Core α) : UniformSpace α :=
  .ofCoreEq u _ rfl

/-- Construct a `UniformSpace.Core` from a `UniformSpace`. -/
abbrev UniformSpace.toCore (u : UniformSpace α) : UniformSpace.Core α where
  __ := u
  refl := by
    rintro U hU ⟨x, y⟩ (rfl : x = y)
    have : Prod.mk x ⁻¹' U ∈ 𝓝 x := by
      rw [UniformSpace.nhds_eq_comap_uniformity]
      exact preimage_mem_comap hU
    convert mem_of_mem_nhds this

theorem UniformSpace.toCore_toTopologicalSpace (u : UniformSpace α) :
    u.toCore.toTopologicalSpace = u.toTopologicalSpace :=
  TopologicalSpace.ext_nhds fun a ↦ by
    rw [u.nhds_eq_comap_uniformity, u.toCore.nhds_toTopologicalSpace]

/-- Build a `UniformSpace` from a `UniformSpace.Core` and a compatible topology.
Use `UniformSpace.mk` instead to avoid proving
the unnecessary assumption `UniformSpace.Core.refl`.

The main constructor used to use a different compatibility assumption.
This definition was created as a step towards porting to a new definition.
Now the main definition is ported,
so this constructor will be removed in a few months. -/
@[deprecated UniformSpace.mk (since := "2024-03-20")]
def UniformSpace.ofNhdsEqComap (u : UniformSpace.Core α) (_t : TopologicalSpace α)
    (h : ∀ x, 𝓝 x = u.uniformity.comap (Prod.mk x)) : UniformSpace α where
  __ := u
  nhds_eq_comap_uniformity := h

@[ext (iff := false)]
protected theorem UniformSpace.ext {u₁ u₂ : UniformSpace α} (h : 𝓤[u₁] = 𝓤[u₂]) : u₁ = u₂ := by
  have : u₁.toTopologicalSpace = u₂.toTopologicalSpace := TopologicalSpace.ext_nhds fun x ↦ by
    rw [u₁.nhds_eq_comap_uniformity, u₂.nhds_eq_comap_uniformity]
    exact congr_arg (comap _) h
  cases u₁; cases u₂; congr

protected theorem UniformSpace.ext_iff {u₁ u₂ : UniformSpace α} :
    u₁ = u₂ ↔ ∀ s, s ∈ 𝓤[u₁] ↔ s ∈ 𝓤[u₂] :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩

theorem UniformSpace.ofCoreEq_toCore (u : UniformSpace α) (t : TopologicalSpace α)
    (h : t = u.toCore.toTopologicalSpace) : .ofCoreEq u.toCore t h = u :=
  UniformSpace.ext rfl

/-- Replace topology in a `UniformSpace` instance with a propositionally (but possibly not
definitionally) equal one. -/
abbrev UniformSpace.replaceTopology {α : Type*} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : UniformSpace α where
  __ := u
  toTopologicalSpace := i
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_eq_comap_uniformity]

theorem UniformSpace.replaceTopology_eq {α : Type*} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : u.replaceTopology h = u :=
  UniformSpace.ext rfl

section UniformSpace

variable [UniformSpace α]

theorem nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α).comap (Prod.mk x) :=
  UniformSpace.nhds_eq_comap_uniformity x

theorem isOpen_uniformity {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α := by
  simp only [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap_prod_mk]

theorem refl_le_uniformity : 𝓟 idRel ≤ 𝓤 α :=
  (@UniformSpace.toCore α _).refl

instance uniformity.neBot [Nonempty α] : NeBot (𝓤 α) :=
  diagonal_nonempty.principal_neBot.mono refl_le_uniformity

theorem refl_mem_uniformity {x : α} {s : Set (α × α)} (h : s ∈ 𝓤 α) : (x, x) ∈ s :=
  refl_le_uniformity h rfl

theorem mem_uniformity_of_eq {x y : α} {s : Set (α × α)} (h : s ∈ 𝓤 α) (hx : x = y) : (x, y) ∈ s :=
  refl_le_uniformity h hx

theorem symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) ≤ 𝓤 _ :=
  UniformSpace.symm

theorem comp_le_uniformity : ((𝓤 α).lift' fun s : Set (α × α) => s ○ s) ≤ 𝓤 α :=
  UniformSpace.comp

theorem lift'_comp_uniformity : ((𝓤 α).lift' fun s : Set (α × α) => s ○ s) = 𝓤 α :=
  comp_le_uniformity.antisymm <| le_lift'.2 fun _s hs ↦ mem_of_superset hs <|
    subset_comp_self <| idRel_subset.2 fun _ ↦ refl_mem_uniformity hs

theorem tendsto_swap_uniformity : Tendsto (@Prod.swap α α) (𝓤 α) (𝓤 α) :=
  symm_le_uniformity

theorem comp_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ t ⊆ s :=
  (mem_lift'_sets <| monotone_id.compRel monotone_id).mp <| comp_le_uniformity hs

/-- If `s ∈ 𝓤 α`, then for any natural `n`, for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ○ ... ○ t ⊆ s` (`n` compositions). -/
theorem eventually_uniformity_iterate_comp_subset {s : Set (α × α)} (hs : s ∈ 𝓤 α) (n : ℕ) :
    ∀ᶠ t in (𝓤 α).smallSets, (t ○ ·)^[n] t ⊆ s := by
  suffices ∀ᶠ t in (𝓤 α).smallSets, t ⊆ s ∧ (t ○ ·)^[n] t ⊆ s from (eventually_and.1 this).2
  induction' n with n ihn generalizing s
  · simpa
  rcases comp_mem_uniformity_sets hs with ⟨t, htU, hts⟩
  refine (ihn htU).mono fun U hU => ?_
  rw [Function.iterate_succ_apply']
  exact
    ⟨hU.1.trans <| (subset_comp_self <| refl_le_uniformity htU).trans hts,
      (compRel_mono hU.1 hU.2).trans hts⟩

/-- If `s ∈ 𝓤 α`, then for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ⊆ s`. -/
theorem eventually_uniformity_comp_subset {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∀ᶠ t in (𝓤 α).smallSets, t ○ t ⊆ s :=
  eventually_uniformity_iterate_comp_subset hs 1

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is transitive. -/
theorem Filter.Tendsto.uniformity_trans {l : Filter β} {f₁ f₂ f₃ : β → α}
    (h₁₂ : Tendsto (fun x => (f₁ x, f₂ x)) l (𝓤 α))
    (h₂₃ : Tendsto (fun x => (f₂ x, f₃ x)) l (𝓤 α)) : Tendsto (fun x => (f₁ x, f₃ x)) l (𝓤 α) := by
  refine le_trans (le_lift'.2 fun s hs => mem_map.2 ?_) comp_le_uniformity
  filter_upwards [mem_map.1 (h₁₂ hs), mem_map.1 (h₂₃ hs)] with x hx₁₂ hx₂₃ using ⟨_, hx₁₂, hx₂₃⟩

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is symmetric. -/
theorem Filter.Tendsto.uniformity_symm {l : Filter β} {f : β → α × α} (h : Tendsto f l (𝓤 α)) :
    Tendsto (fun x => ((f x).2, (f x).1)) l (𝓤 α) :=
  tendsto_swap_uniformity.comp h

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is reflexive. -/
theorem tendsto_diag_uniformity (f : β → α) (l : Filter β) :
    Tendsto (fun x => (f x, f x)) l (𝓤 α) := fun _s hs =>
  mem_map.2 <| univ_mem' fun _ => refl_mem_uniformity hs

theorem tendsto_const_uniformity {a : α} {f : Filter β} : Tendsto (fun _ => (a, a)) f (𝓤 α) :=
  tendsto_diag_uniformity (fun _ => a) f

theorem symm_of_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, (∀ a b, (a, b) ∈ t → (b, a) ∈ t) ∧ t ⊆ s :=
  have : preimage Prod.swap s ∈ 𝓤 α := symm_le_uniformity hs
  ⟨s ∩ preimage Prod.swap s, inter_mem hs this, fun _ _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, inter_subset_left⟩

theorem comp_symm_of_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, (∀ {a b}, (a, b) ∈ t → (b, a) ∈ t) ∧ t ○ t ⊆ s :=
  let ⟨_t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  let ⟨t', ht', ht'₁, ht'₂⟩ := symm_of_uniformity ht₁
  ⟨t', ht', ht'₁ _ _, Subset.trans (monotone_id.compRel monotone_id ht'₂) ht₂⟩

theorem uniformity_le_symm : 𝓤 α ≤ @Prod.swap α α <$> 𝓤 α := by
  rw [map_swap_eq_comap_swap]; exact tendsto_swap_uniformity.le_comap

theorem uniformity_eq_symm : 𝓤 α = @Prod.swap α α <$> 𝓤 α :=
  le_antisymm uniformity_le_symm symm_le_uniformity

@[simp]
theorem comap_swap_uniformity : comap (@Prod.swap α α) (𝓤 α) = 𝓤 α :=
  (congr_arg _ uniformity_eq_symm).trans <| comap_map Prod.swap_injective

theorem symmetrize_mem_uniformity {V : Set (α × α)} (h : V ∈ 𝓤 α) : symmetrizeRel V ∈ 𝓤 α := by
  apply (𝓤 α).inter_sets h
  rw [← image_swap_eq_preimage_swap, uniformity_eq_symm]
  exact image_mem_map h

/-- Symmetric entourages form a basis of `𝓤 α` -/
theorem UniformSpace.hasBasis_symmetric :
    (𝓤 α).HasBasis (fun s : Set (α × α) => s ∈ 𝓤 α ∧ SymmetricRel s) id :=
  hasBasis_self.2 fun t t_in =>
    ⟨symmetrizeRel t, symmetrize_mem_uniformity t_in, symmetric_symmetrizeRel t,
      symmetrizeRel_subset_self t⟩

theorem uniformity_lift_le_swap {g : Set (α × α) → Filter β} {f : Filter β} (hg : Monotone g)
    (h : ((𝓤 α).lift fun s => g (preimage Prod.swap s)) ≤ f) : (𝓤 α).lift g ≤ f :=
  calc
    (𝓤 α).lift g ≤ (Filter.map (@Prod.swap α α) <| 𝓤 α).lift g :=
      lift_mono uniformity_le_symm le_rfl
    _ ≤ _ := by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h

theorem uniformity_lift_le_comp {f : Set (α × α) → Filter β} (h : Monotone f) :
    ((𝓤 α).lift fun s => f (s ○ s)) ≤ (𝓤 α).lift f :=
  calc
    ((𝓤 α).lift fun s => f (s ○ s)) = ((𝓤 α).lift' fun s : Set (α × α) => s ○ s).lift f := by
      rw [lift_lift'_assoc]
      · exact monotone_id.compRel monotone_id
      · exact h
    _ ≤ (𝓤 α).lift f := lift_mono comp_le_uniformity le_rfl

theorem comp3_mem_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ (t ○ t) ⊆ s :=
  let ⟨_t', ht', ht's⟩ := comp_mem_uniformity_sets hs
  let ⟨t, ht, htt'⟩ := comp_mem_uniformity_sets ht'
  ⟨t, ht, (compRel_mono ((subset_comp_self (refl_le_uniformity ht)).trans htt') htt').trans ht's⟩

/-- See also `comp3_mem_uniformity`. -/
theorem comp_le_uniformity3 : ((𝓤 α).lift' fun s : Set (α × α) => s ○ (s ○ s)) ≤ 𝓤 α := fun _ h =>
  let ⟨_t, htU, ht⟩ := comp3_mem_uniformity h
  mem_of_superset (mem_lift' htU) ht

/-- See also `comp_open_symm_mem_uniformity_sets`. -/
theorem comp_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SymmetricRel t ∧ t ○ t ⊆ s := by
  obtain ⟨w, w_in, w_sub⟩ : ∃ w ∈ 𝓤 α, w ○ w ⊆ s := comp_mem_uniformity_sets hs
  use symmetrizeRel w, symmetrize_mem_uniformity w_in, symmetric_symmetrizeRel w
  have : symmetrizeRel w ⊆ w := symmetrizeRel_subset_self w
  calc symmetrizeRel w ○ symmetrizeRel w
    _ ⊆ w ○ w := by gcongr
    _ ⊆ s     := w_sub

theorem subset_comp_self_of_mem_uniformity {s : Set (α × α)} (h : s ∈ 𝓤 α) : s ⊆ s ○ s :=
  subset_comp_self (refl_le_uniformity h)

theorem comp_comp_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SymmetricRel t ∧ t ○ t ○ t ⊆ s := by
  rcases comp_symm_mem_uniformity_sets hs with ⟨w, w_in, _, w_sub⟩
  rcases comp_symm_mem_uniformity_sets w_in with ⟨t, t_in, t_symm, t_sub⟩
  use t, t_in, t_symm
  have : t ⊆ t ○ t := subset_comp_self_of_mem_uniformity t_in
  -- Porting note: Needed the following `have`s to make `mono` work
  have ht := Subset.refl t
  have hw := Subset.refl w
  calc
    t ○ t ○ t ⊆ w ○ t := by mono
    _ ⊆ w ○ (t ○ t) := by mono
    _ ⊆ w ○ w := by mono
    _ ⊆ s := w_sub

/-!
### Balls in uniform spaces
-/

namespace UniformSpace

/-- The ball around `(x : β)` with respect to `(V : Set (β × β))`. Intended to be
used for `V ∈ 𝓤 β`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`. -/
def ball (x : β) (V : Set (β × β)) : Set β := Prod.mk x ⁻¹' V

open UniformSpace (ball)

lemma mem_ball_self (x : α) {V : Set (α × α)} : V ∈ 𝓤 α → x ∈ ball x V := refl_mem_uniformity

/-- The triangle inequality for `UniformSpace.ball` -/
theorem mem_ball_comp {V W : Set (β × β)} {x y z} (h : y ∈ ball x V) (h' : z ∈ ball y W) :
    z ∈ ball x (V ○ W) :=
  prod_mk_mem_compRel h h'

theorem ball_subset_of_comp_subset {V W : Set (β × β)} {x y} (h : x ∈ ball y W) (h' : W ○ W ⊆ V) :
    ball x W ⊆ ball y V := fun _z z_in => h' (mem_ball_comp h z_in)

theorem ball_mono {V W : Set (β × β)} (h : V ⊆ W) (x : β) : ball x V ⊆ ball x W :=
  preimage_mono h

theorem ball_inter (x : β) (V W : Set (β × β)) : ball x (V ∩ W) = ball x V ∩ ball x W :=
  preimage_inter

theorem ball_inter_left (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x V :=
  ball_mono inter_subset_left x

theorem ball_inter_right (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x W :=
  ball_mono inter_subset_right x

theorem ball_sInter {s : Set (Set (β × β))} {x: β} : ball x (⋂₀ s) = ⋂ i ∈ s, ball x i :=
  preimage_sInter

theorem ball_iInter {ι : Type*} {f : ι → Set (β × β)} {x : β} :
    ball x (⋂ i : ι, f i) = ⋂ i : ι, ball x (f i) := preimage_iInter

theorem mem_ball_symmetry {V : Set (β × β)} (hV : SymmetricRel V) {x y} :
    x ∈ ball y V ↔ y ∈ ball x V :=
  show (x, y) ∈ Prod.swap ⁻¹' V ↔ (x, y) ∈ V by
    unfold SymmetricRel at hV
    rw [hV]

theorem ball_eq_of_symmetry {V : Set (β × β)} (hV : SymmetricRel V) {x} :
    ball x V = { y | (y, x) ∈ V } := by
  ext y
  rw [mem_ball_symmetry hV]
  exact Iff.rfl

theorem mem_comp_of_mem_ball {V W : Set (β × β)} {x y z : β} (hV : SymmetricRel V)
    (hx : x ∈ ball z V) (hy : y ∈ ball z W) : (x, y) ∈ V ○ W := by
  rw [mem_ball_symmetry hV] at hx
  exact ⟨z, hx, hy⟩

lemma isOpen_ball (x : α) {V : Set (α × α)} (hV : IsOpen V) : IsOpen (ball x V) :=
  hV.preimage <| continuous_const.prod_mk continuous_id

lemma isClosed_ball (x : α) {V : Set (α × α)} (hV : IsClosed V) : IsClosed (ball x V) :=
  hV.preimage <| continuous_const.prod_mk continuous_id

theorem mem_comp_comp {V W M : Set (β × β)} (hW' : SymmetricRel W) {p : β × β} :
    p ∈ V ○ M ○ W ↔ (ball p.1 V ×ˢ ball p.2 W ∩ M).Nonempty := by
  cases' p with x y
  constructor
  · rintro ⟨z, ⟨w, hpw, hwz⟩, hzy⟩
    exact ⟨(w, z), ⟨hpw, by rwa [mem_ball_symmetry hW']⟩, hwz⟩
  · rintro ⟨⟨w, z⟩, ⟨w_in, z_in⟩, hwz⟩
    rw [mem_ball_symmetry hW'] at z_in
    exact ⟨z, ⟨w, w_in, hwz⟩, z_in⟩

end UniformSpace

/-!
### Neighborhoods in uniform spaces
-/

open UniformSpace

theorem mem_nhds_uniformity_iff_right {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α := by
  simp only [nhds_eq_comap_uniformity, mem_comap_prod_mk]

theorem mem_nhds_uniformity_iff_left {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ { p : α × α | p.2 = x → p.1 ∈ s } ∈ 𝓤 α := by
  rw [uniformity_eq_symm, mem_nhds_uniformity_iff_right]
  simp only [map_def, mem_map, preimage_setOf_eq, Prod.snd_swap, Prod.fst_swap]

theorem nhdsWithin_eq_comap_uniformity_of_mem {x : α} {T : Set α} (hx : x ∈ T) (S : Set α) :
    𝓝[S] x = (𝓤 α ⊓ 𝓟 (T ×ˢ S)).comap (Prod.mk x) := by
  simp [nhdsWithin, nhds_eq_comap_uniformity, hx]

theorem nhdsWithin_eq_comap_uniformity {x : α} (S : Set α) :
    𝓝[S] x = (𝓤 α ⊓ 𝓟 (univ ×ˢ S)).comap (Prod.mk x) :=
  nhdsWithin_eq_comap_uniformity_of_mem (mem_univ _) S

/-- See also `isOpen_iff_isOpen_ball_subset`. -/
theorem isOpen_iff_ball_subset {s : Set α} : IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, ball x V ⊆ s := by
  simp_rw [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap, ball]

theorem nhds_basis_uniformity' {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => ball x (s i) := by
  rw [nhds_eq_comap_uniformity]
  exact h.comap (Prod.mk x)

theorem nhds_basis_uniformity {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => { y | (y, x) ∈ s i } := by
  replace h := h.comap Prod.swap
  rw [comap_swap_uniformity] at h
  exact nhds_basis_uniformity' h

theorem nhds_eq_comap_uniformity' {x : α} : 𝓝 x = (𝓤 α).comap fun y => (y, x) :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_of_same_basis <| (𝓤 α).basis_sets.comap _

theorem UniformSpace.mem_nhds_iff {x : α} {s : Set α} : s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, ball x V ⊆ s := by
  rw [nhds_eq_comap_uniformity, mem_comap]
  simp_rw [ball]

theorem UniformSpace.ball_mem_nhds (x : α) ⦃V : Set (α × α)⦄ (V_in : V ∈ 𝓤 α) : ball x V ∈ 𝓝 x := by
  rw [UniformSpace.mem_nhds_iff]
  exact ⟨V, V_in, Subset.rfl⟩

theorem UniformSpace.ball_mem_nhdsWithin {x : α} {S : Set α} ⦃V : Set (α × α)⦄ (x_in : x ∈ S)
    (V_in : V ∈ 𝓤 α ⊓ 𝓟 (S ×ˢ S)) : ball x V ∈ 𝓝[S] x := by
  rw [nhdsWithin_eq_comap_uniformity_of_mem x_in, mem_comap]
  exact ⟨V, V_in, Subset.rfl⟩

theorem UniformSpace.mem_nhds_iff_symm {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, SymmetricRel V ∧ ball x V ⊆ s := by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    use symmetrizeRel V, symmetrize_mem_uniformity V_in, symmetric_symmetrizeRel V
    exact Subset.trans (ball_mono (symmetrizeRel_subset_self V) x) V_sub
  · rintro ⟨V, V_in, _, V_sub⟩
    exact ⟨V, V_in, V_sub⟩

theorem UniformSpace.hasBasis_nhds (x : α) :
    HasBasis (𝓝 x) (fun s : Set (α × α) => s ∈ 𝓤 α ∧ SymmetricRel s) fun s => ball x s :=
  ⟨fun t => by simp [UniformSpace.mem_nhds_iff_symm, and_assoc]⟩

open UniformSpace

theorem UniformSpace.mem_closure_iff_symm_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (s ∩ ball x V).Nonempty := by
  simp [mem_closure_iff_nhds_basis (hasBasis_nhds x), Set.Nonempty]

theorem UniformSpace.mem_closure_iff_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → (ball x V ∩ s).Nonempty := by
  simp [mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (𝓤 α).basis_sets)]

theorem UniformSpace.hasBasis_nhds_prod (x y : α) :
    HasBasis (𝓝 (x, y)) (fun s => s ∈ 𝓤 α ∧ SymmetricRel s) fun s => ball x s ×ˢ ball y s := by
  rw [nhds_prod_eq]
  apply (hasBasis_nhds x).prod_same_index (hasBasis_nhds y)
  rintro U V ⟨U_in, U_symm⟩ ⟨V_in, V_symm⟩
  exact
    ⟨U ∩ V, ⟨(𝓤 α).inter_sets U_in V_in, U_symm.inter V_symm⟩, ball_inter_left x U V,
      ball_inter_right y U V⟩

theorem nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball x) :=
  (nhds_basis_uniformity' (𝓤 α).basis_sets).eq_biInf

theorem nhds_eq_uniformity' {x : α} : 𝓝 x = (𝓤 α).lift' fun s => { y | (y, x) ∈ s } :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_biInf

theorem mem_nhds_left (x : α) {s : Set (α × α)} (h : s ∈ 𝓤 α) : { y : α | (x, y) ∈ s } ∈ 𝓝 x :=
  ball_mem_nhds x h

theorem mem_nhds_right (y : α) {s : Set (α × α)} (h : s ∈ 𝓤 α) : { x : α | (x, y) ∈ s } ∈ 𝓝 y :=
  mem_nhds_left _ (symm_le_uniformity h)

theorem exists_mem_nhds_ball_subset_of_mem_nhds {a : α} {U : Set α} (h : U ∈ 𝓝 a) :
    ∃ V ∈ 𝓝 a, ∃ t ∈ 𝓤 α, ∀ a' ∈ V, UniformSpace.ball a' t ⊆ U :=
  let ⟨t, ht, htU⟩ := comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 h)
  ⟨_, mem_nhds_left a ht, t, ht, fun a₁ h₁ a₂ h₂ => @htU (a, a₂) ⟨a₁, h₁, h₂⟩ rfl⟩

theorem tendsto_right_nhds_uniformity {a : α} : Tendsto (fun a' => (a', a)) (𝓝 a) (𝓤 α) := fun _ =>
  mem_nhds_right a

theorem tendsto_left_nhds_uniformity {a : α} : Tendsto (fun a' => (a, a')) (𝓝 a) (𝓤 α) := fun _ =>
  mem_nhds_left a

theorem lift_nhds_left {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : Set (α × α) => g (ball x s) := by
  rw [nhds_eq_comap_uniformity, comap_lift_eq2 hg]
  simp_rw [ball, Function.comp_def]

theorem lift_nhds_right {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : Set (α × α) => g { y | (y, x) ∈ s } := by
  rw [nhds_eq_comap_uniformity', comap_lift_eq2 hg]
  simp_rw [Function.comp_def, preimage]

theorem nhds_nhds_eq_uniformity_uniformity_prod {a b : α} :
    𝓝 a ×ˢ 𝓝 b = (𝓤 α).lift fun s : Set (α × α) =>
      (𝓤 α).lift' fun t => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ t } := by
  rw [nhds_eq_uniformity', nhds_eq_uniformity, prod_lift'_lift']
  exacts [rfl, monotone_preimage, monotone_preimage]

theorem nhds_eq_uniformity_prod {a b : α} :
    𝓝 (a, b) =
      (𝓤 α).lift' fun s : Set (α × α) => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ s } := by
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift']
  · exact fun s => monotone_const.set_prod monotone_preimage
  · refine fun t => Monotone.set_prod ?_ monotone_const
    exact monotone_preimage (f := fun y => (y, a))

theorem nhdset_of_mem_uniformity {d : Set (α × α)} (s : Set (α × α)) (hd : d ∈ 𝓤 α) :
    ∃ t : Set (α × α), IsOpen t ∧ s ⊆ t ∧
      t ⊆ { p | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d } := by
  let cl_d := { p : α × α | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d }
  have : ∀ p ∈ s, ∃ t, t ⊆ cl_d ∧ IsOpen t ∧ p ∈ t := fun ⟨x, y⟩ hp =>
    mem_nhds_iff.mp <|
      show cl_d ∈ 𝓝 (x, y) by
        rw [nhds_eq_uniformity_prod, mem_lift'_sets]
        · exact ⟨d, hd, fun ⟨a, b⟩ ⟨ha, hb⟩ => ⟨x, y, ha, hp, hb⟩⟩
        · exact fun _ _ h _ h' => ⟨h h'.1, h h'.2⟩
  choose t ht using this
  exact ⟨(⋃ p : α × α, ⋃ h : p ∈ s, t p h : Set (α × α)),
    isOpen_iUnion fun p : α × α => isOpen_iUnion fun hp => (ht p hp).right.left,
    fun ⟨a, b⟩ hp => by
      simp only [mem_iUnion, Prod.exists]; exact ⟨a, b, hp, (ht (a, b) hp).right.right⟩,
    iUnion_subset fun p => iUnion_subset fun hp => (ht p hp).left⟩

/-- Entourages are neighborhoods of the diagonal. -/
theorem nhds_le_uniformity (x : α) : 𝓝 (x, x) ≤ 𝓤 α := by
  intro V V_in
  rcases comp_symm_mem_uniformity_sets V_in with ⟨w, w_in, w_symm, w_sub⟩
  have : ball x w ×ˢ ball x w ∈ 𝓝 (x, x) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in)
  apply mem_of_superset this
  rintro ⟨u, v⟩ ⟨u_in, v_in⟩
  exact w_sub (mem_comp_of_mem_ball w_symm u_in v_in)

/-- Entourages are neighborhoods of the diagonal. -/
theorem iSup_nhds_le_uniformity : ⨆ x : α, 𝓝 (x, x) ≤ 𝓤 α :=
  iSup_le nhds_le_uniformity

/-- Entourages are neighborhoods of the diagonal. -/
theorem nhdsSet_diagonal_le_uniformity : 𝓝ˢ (diagonal α) ≤ 𝓤 α :=
  (nhdsSet_diagonal α).trans_le iSup_nhds_le_uniformity

/-!
### Closure and interior in uniform spaces
-/

theorem closure_eq_uniformity (s : Set <| α × α) :
    closure s = ⋂ V ∈ { V | V ∈ 𝓤 α ∧ SymmetricRel V }, V ○ s ○ V := by
  ext ⟨x, y⟩
  simp +contextual only
    [mem_closure_iff_nhds_basis (UniformSpace.hasBasis_nhds_prod x y), mem_iInter, mem_setOf_eq,
      and_imp, mem_comp_comp, exists_prop, ← mem_inter_iff, inter_comm, Set.Nonempty]

theorem uniformity_hasBasis_closed :
    HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α ∧ IsClosed V) id := by
  refine Filter.hasBasis_self.2 fun t h => ?_
  rcases comp_comp_symm_mem_uniformity_sets h with ⟨w, w_in, w_symm, r⟩
  refine ⟨closure w, mem_of_superset w_in subset_closure, isClosed_closure, ?_⟩
  refine Subset.trans ?_ r
  rw [closure_eq_uniformity]
  apply iInter_subset_of_subset
  apply iInter_subset
  exact ⟨w_in, w_symm⟩

theorem uniformity_eq_uniformity_closure : 𝓤 α = (𝓤 α).lift' closure :=
  Eq.symm <| uniformity_hasBasis_closed.lift'_closure_eq_self fun _ => And.right

theorem Filter.HasBasis.uniformity_closure {p : ι → Prop} {U : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p U) : (𝓤 α).HasBasis p fun i => closure (U i) :=
  (@uniformity_eq_uniformity_closure α _).symm ▸ h.lift'_closure

/-- Closed entourages form a basis of the uniformity filter. -/
theorem uniformity_hasBasis_closure : HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α) closure :=
  (𝓤 α).basis_sets.uniformity_closure

theorem closure_eq_inter_uniformity {t : Set (α × α)} : closure t = ⋂ d ∈ 𝓤 α, d ○ (t ○ d) :=
  calc
    closure t = ⋂ (V) (_ : V ∈ 𝓤 α ∧ SymmetricRel V), V ○ t ○ V := closure_eq_uniformity t
    _ = ⋂ V ∈ 𝓤 α, V ○ t ○ V :=
      Eq.symm <|
        UniformSpace.hasBasis_symmetric.biInter_mem fun _ _ hV =>
          compRel_mono (compRel_mono hV Subset.rfl) hV
    _ = ⋂ V ∈ 𝓤 α, V ○ (t ○ V) := by simp only [compRel_assoc]

theorem uniformity_eq_uniformity_interior : 𝓤 α = (𝓤 α).lift' interior :=
  le_antisymm
    (le_iInf₂ fun d hd => by
      let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
      let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs
      have : s ⊆ interior d :=
        calc
          s ⊆ t := hst
          _ ⊆ interior d :=
            ht.subset_interior_iff.mpr fun x (hx : x ∈ t) =>
              let ⟨x, y, h₁, h₂, h₃⟩ := ht_comp hx
              hs_comp ⟨x, h₁, y, h₂, h₃⟩
      have : interior d ∈ 𝓤 α := by filter_upwards [hs] using this
      simp [this])
    fun _ hs => ((𝓤 α).lift' interior).sets_of_superset (mem_lift' hs) interior_subset

theorem interior_mem_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) : interior s ∈ 𝓤 α := by
  rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs

theorem mem_uniformity_isClosed {s : Set (α × α)} (h : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, IsClosed t ∧ t ⊆ s :=
  let ⟨t, ⟨ht_mem, htc⟩, hts⟩ := uniformity_hasBasis_closed.mem_iff.1 h
  ⟨t, ht_mem, htc, hts⟩

theorem isOpen_iff_isOpen_ball_subset {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, IsOpen V ∧ ball x V ⊆ s := by
  rw [isOpen_iff_ball_subset]
  constructor <;> intro h x hx
  · obtain ⟨V, hV, hV'⟩ := h x hx
    exact
      ⟨interior V, interior_mem_uniformity hV, isOpen_interior,
        (ball_mono interior_subset x).trans hV'⟩
  · obtain ⟨V, hV, -, hV'⟩ := h x hx
    exact ⟨V, hV, hV'⟩

@[deprecated (since := "2024-11-18")] alias
isOpen_iff_open_ball_subset := isOpen_iff_isOpen_ball_subset

/-- The uniform neighborhoods of all points of a dense set cover the whole space. -/
theorem Dense.biUnion_uniformity_ball {s : Set α} {U : Set (α × α)} (hs : Dense s) (hU : U ∈ 𝓤 α) :
    ⋃ x ∈ s, ball x U = univ := by
  refine iUnion₂_eq_univ_iff.2 fun y => ?_
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with ⟨x, hxs, hxy : (x, y) ∈ U⟩
  exact ⟨x, hxs, hxy⟩

/-- The uniform neighborhoods of all points of a dense indexed collection cover the whole space. -/
lemma DenseRange.iUnion_uniformity_ball {ι : Type*} {xs : ι → α}
    (xs_dense : DenseRange xs) {U : Set (α × α)} (hU : U ∈ uniformity α) :
    ⋃ i, UniformSpace.ball (xs i) U = univ := by
  rw [← biUnion_range (f := xs) (g := fun x ↦ UniformSpace.ball x U)]
  exact Dense.biUnion_uniformity_ball xs_dense hU

/-!
### Uniformity bases
-/

/-- Open elements of `𝓤 α` form a basis of `𝓤 α`. -/
theorem uniformity_hasBasis_open : HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α ∧ IsOpen V) id :=
  hasBasis_self.2 fun s hs =>
    ⟨interior s, interior_mem_uniformity hs, isOpen_interior, interior_subset⟩

theorem Filter.HasBasis.mem_uniformity_iff {p : β → Prop} {s : β → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {t : Set (α × α)} :
    t ∈ 𝓤 α ↔ ∃ i, p i ∧ ∀ a b, (a, b) ∈ s i → (a, b) ∈ t :=
  h.mem_iff.trans <| by simp only [Prod.forall, subset_def]

/-- Open elements `s : Set (α × α)` of `𝓤 α` such that `(x, y) ∈ s ↔ (y, x) ∈ s` form a basis
of `𝓤 α`. -/
theorem uniformity_hasBasis_open_symmetric :
    HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α ∧ IsOpen V ∧ SymmetricRel V) id := by
  simp only [← and_assoc]
  refine uniformity_hasBasis_open.restrict fun s hs => ⟨symmetrizeRel s, ?_⟩
  exact
    ⟨⟨symmetrize_mem_uniformity hs.1, IsOpen.inter hs.2 (hs.2.preimage continuous_swap)⟩,
      symmetric_symmetrizeRel s, symmetrizeRel_subset_self s⟩

theorem comp_open_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, IsOpen t ∧ SymmetricRel t ∧ t ○ t ⊆ s := by
  obtain ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hu₄ : u ⊆ t⟩ := uniformity_hasBasis_open_symmetric.mem_iff.mp ht₁
  exact ⟨u, hu₁, hu₂, hu₃, (compRel_mono hu₄ hu₄).trans ht₂⟩

section

variable (α)

theorem UniformSpace.has_seq_basis [IsCountablyGenerated <| 𝓤 α] :
    ∃ V : ℕ → Set (α × α), HasAntitoneBasis (𝓤 α) V ∧ ∀ n, SymmetricRel (V n) :=
  let ⟨U, hsym, hbasis⟩ := (@UniformSpace.hasBasis_symmetric α _).exists_antitone_subbasis
  ⟨U, hbasis, fun n => (hsym n).2⟩

end

theorem Filter.HasBasis.biInter_biUnion_ball {p : ι → Prop} {U : ι → Set (α × α)}
    (h : HasBasis (𝓤 α) p U) (s : Set α) :
    (⋂ (i) (_ : p i), ⋃ x ∈ s, ball x (U i)) = closure s := by
  ext x
  simp [mem_closure_iff_nhds_basis (nhds_basis_uniformity h), ball]

/-! ### Uniform continuity -/


/-- A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `α`. -/
def UniformContinuous [UniformSpace β] (f : α → β) :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α) (𝓤 β)

/-- Notation for uniform continuity with respect to non-standard `UniformSpace` instances. -/
scoped[Uniformity] notation "UniformContinuous[" u₁ ", " u₂ "]" => @UniformContinuous _ _ u₁ u₂

/-- A function `f : α → β` is *uniformly continuous* on `s : Set α` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s ×ˢ s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`. -/
def UniformContinuousOn [UniformSpace β] (f : α → β) (s : Set α) : Prop :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 β)

theorem uniformContinuous_def [UniformSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, { x : α × α | (f x.1, f x.2) ∈ r } ∈ 𝓤 α :=
  Iff.rfl

theorem uniformContinuous_iff_eventually [UniformSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, ∀ᶠ x : α × α in 𝓤 α, (f x.1, f x.2) ∈ r :=
  Iff.rfl

theorem uniformContinuousOn_univ [UniformSpace β] {f : α → β} :
    UniformContinuousOn f univ ↔ UniformContinuous f := by
  rw [UniformContinuousOn, UniformContinuous, univ_prod_univ, principal_univ, inf_top_eq]

theorem uniformContinuous_of_const [UniformSpace β] {c : α → β} (h : ∀ a b, c a = c b) :
    UniformContinuous c :=
  have : (fun x : α × α => (c x.fst, c x.snd)) ⁻¹' idRel = univ :=
    eq_univ_iff_forall.2 fun ⟨a, b⟩ => h a b
  le_trans (map_le_iff_le_comap.2 <| by simp [comap_principal, this, univ_mem]) refl_le_uniformity

theorem uniformContinuous_id : UniformContinuous (@id α) := tendsto_id

theorem uniformContinuous_const [UniformSpace β] {b : β} : UniformContinuous fun _ : α => b :=
  uniformContinuous_of_const fun _ _ => rfl

nonrec theorem UniformContinuous.comp [UniformSpace β] [UniformSpace γ] {g : β → γ} {f : α → β}
    (hg : UniformContinuous g) (hf : UniformContinuous f) : UniformContinuous (g ∘ f) :=
  hg.comp hf

/--If a function `T` is uniformly continuous in a uniform space `β`,
then its `n`-th iterate `T^[n]` is also uniformly continuous.-/
theorem UniformContinuous.iterate [UniformSpace β] (T : β → β) (n : ℕ) (h : UniformContinuous T) :
    UniformContinuous T^[n] := by
  induction n with
  | zero => exact uniformContinuous_id
  | succ n hn => exact Function.iterate_succ _ _ ▸ UniformContinuous.comp hn h

theorem Filter.HasBasis.uniformContinuous_iff {ι'} [UniformSpace β] {p : ι → Prop}
    {s : ι → Set (α × α)} (ha : (𝓤 α).HasBasis p s) {q : ι' → Prop} {t : ι' → Set (β × β)}
    (hb : (𝓤 β).HasBasis q t) {f : α → β} :
    UniformContinuous f ↔ ∀ i, q i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ t i :=
  (ha.tendsto_iff hb).trans <| by simp only [Prod.forall]

theorem Filter.HasBasis.uniformContinuousOn_iff {ι'} [UniformSpace β] {p : ι → Prop}
    {s : ι → Set (α × α)} (ha : (𝓤 α).HasBasis p s) {q : ι' → Prop} {t : ι' → Set (β × β)}
    (hb : (𝓤 β).HasBasis q t) {f : α → β} {S : Set α} :
    UniformContinuousOn f S ↔
      ∀ i, q i → ∃ j, p j ∧ ∀ x, x ∈ S → ∀ y, y ∈ S → (x, y) ∈ s j → (f x, f y) ∈ t i :=
  ((ha.inf_principal (S ×ˢ S)).tendsto_iff hb).trans <| by
    simp_rw [Prod.forall, Set.inter_comm (s _), forall_mem_comm, mem_inter_iff, mem_prod, and_imp]

end UniformSpace

open uniformity

section Constructions

instance : PartialOrder (UniformSpace α) :=
  PartialOrder.lift (fun u => 𝓤[u]) fun _ _ => UniformSpace.ext

protected theorem UniformSpace.le_def {u₁ u₂ : UniformSpace α} : u₁ ≤ u₂ ↔ 𝓤[u₁] ≤ 𝓤[u₂] := Iff.rfl

instance : InfSet (UniformSpace α) :=
  ⟨fun s =>
    UniformSpace.ofCore
      { uniformity := ⨅ u ∈ s, 𝓤[u]
        refl := le_iInf fun u => le_iInf fun _ => u.toCore.refl
        symm := le_iInf₂ fun u hu =>
          le_trans (map_mono <| iInf_le_of_le _ <| iInf_le _ hu) u.symm
        comp := le_iInf₂ fun u hu =>
          le_trans (lift'_mono (iInf_le_of_le _ <| iInf_le _ hu) <| le_rfl) u.comp }⟩

protected theorem UniformSpace.sInf_le {tt : Set (UniformSpace α)} {t : UniformSpace α}
    (h : t ∈ tt) : sInf tt ≤ t :=
  show ⨅ u ∈ tt, 𝓤[u] ≤ 𝓤[t] from iInf₂_le t h

protected theorem UniformSpace.le_sInf {tt : Set (UniformSpace α)} {t : UniformSpace α}
    (h : ∀ t' ∈ tt, t ≤ t') : t ≤ sInf tt :=
  show 𝓤[t] ≤ ⨅ u ∈ tt, 𝓤[u] from le_iInf₂ h

instance : Top (UniformSpace α) :=
  ⟨@UniformSpace.mk α ⊤ ⊤ le_top le_top fun x ↦ by simp only [nhds_top, comap_top]⟩

instance : Bot (UniformSpace α) :=
  ⟨{  toTopologicalSpace := ⊥
      uniformity := 𝓟 idRel
      symm := by simp [Tendsto]
      comp := lift'_le (mem_principal_self _) <| principal_mono.2 id_compRel.subset
      nhds_eq_comap_uniformity := fun s => by
        let _ : TopologicalSpace α := ⊥; have := discreteTopology_bot α
        simp [idRel] }⟩

instance : Min (UniformSpace α) :=
  ⟨fun u₁ u₂ =>
    { uniformity := 𝓤[u₁] ⊓ 𝓤[u₂]
      symm := u₁.symm.inf u₂.symm
      comp := (lift'_inf_le _ _ _).trans <| inf_le_inf u₁.comp u₂.comp
      toTopologicalSpace := u₁.toTopologicalSpace ⊓ u₂.toTopologicalSpace
      nhds_eq_comap_uniformity := fun _ ↦ by
        rw [@nhds_inf _ u₁.toTopologicalSpace _, @nhds_eq_comap_uniformity _ u₁,
          @nhds_eq_comap_uniformity _ u₂, comap_inf] }⟩

instance : CompleteLattice (UniformSpace α) :=
  { inferInstanceAs (PartialOrder (UniformSpace α)) with
    sup := fun a b => sInf { x | a ≤ x ∧ b ≤ x }
    le_sup_left := fun _ _ => UniformSpace.le_sInf fun _ ⟨h, _⟩ => h
    le_sup_right := fun _ _ => UniformSpace.le_sInf fun _ ⟨_, h⟩ => h
    sup_le := fun _ _ _ h₁ h₂ => UniformSpace.sInf_le ⟨h₁, h₂⟩
    inf := (· ⊓ ·)
    le_inf := fun a _ _ h₁ h₂ => show a.uniformity ≤ _ from le_inf h₁ h₂
    inf_le_left := fun a _ => show _ ≤ a.uniformity from inf_le_left
    inf_le_right := fun _ b => show _ ≤ b.uniformity from inf_le_right
    top := ⊤
    le_top := fun a => show a.uniformity ≤ ⊤ from le_top
    bot := ⊥
    bot_le := fun u => u.toCore.refl
    sSup := fun tt => sInf { t | ∀ t' ∈ tt, t' ≤ t }
    le_sSup := fun _ _ h => UniformSpace.le_sInf fun _ h' => h' _ h
    sSup_le := fun _ _ h => UniformSpace.sInf_le h
    sInf := sInf
    le_sInf := fun _ _ hs => UniformSpace.le_sInf hs
    sInf_le := fun _ _ ha => UniformSpace.sInf_le ha }

theorem iInf_uniformity {ι : Sort*} {u : ι → UniformSpace α} : 𝓤[iInf u] = ⨅ i, 𝓤[u i] :=
  iInf_range

theorem inf_uniformity {u v : UniformSpace α} : 𝓤[u ⊓ v] = 𝓤[u] ⊓ 𝓤[v] := rfl

lemma bot_uniformity : 𝓤[(⊥ : UniformSpace α)] = 𝓟 idRel := rfl

lemma top_uniformity : 𝓤[(⊤ : UniformSpace α)] = ⊤ := rfl

instance inhabitedUniformSpace : Inhabited (UniformSpace α) :=
  ⟨⊥⟩

instance inhabitedUniformSpaceCore : Inhabited (UniformSpace.Core α) :=
  ⟨@UniformSpace.toCore _ default⟩

instance [Subsingleton α] : Unique (UniformSpace α) where
  uniq u := bot_unique <| le_principal_iff.2 <| by
    rw [idRel, ← diagonal, diagonal_eq_univ]; exact univ_mem

/-- Given `f : α → β` and a uniformity `u` on `β`, the inverse image of `u` under `f`
  is the inverse image in the filter sense of the induced function `α × α → β × β`.
  See note [reducible non-instances]. -/
abbrev UniformSpace.comap (f : α → β) (u : UniformSpace β) : UniformSpace α where
  uniformity := 𝓤[u].comap fun p : α × α => (f p.1, f p.2)
  symm := by
    simp only [tendsto_comap_iff, Prod.swap, (· ∘ ·)]
    exact tendsto_swap_uniformity.comp tendsto_comap
  comp := le_trans
    (by
      rw [comap_lift'_eq, comap_lift'_eq2]
      · exact lift'_mono' fun s _ ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩ => ⟨f x, h₁, h₂⟩
      · exact monotone_id.compRel monotone_id)
    (comap_mono u.comp)
  toTopologicalSpace := u.toTopologicalSpace.induced f
  nhds_eq_comap_uniformity x := by
    simp only [nhds_induced, nhds_eq_comap_uniformity, comap_comap, Function.comp_def]

theorem uniformity_comap {_ : UniformSpace β} (f : α → β) :
    𝓤[UniformSpace.comap f ‹_›] = comap (Prod.map f f) (𝓤 β) :=
  rfl

lemma ball_preimage {f : α → β} {U : Set (β × β)} {x : α} :
    UniformSpace.ball x (Prod.map f f ⁻¹' U) = f ⁻¹' UniformSpace.ball (f x) U := by
  ext : 1
  simp only [UniformSpace.ball, mem_preimage, Prod.map_apply]

@[simp]
theorem uniformSpace_comap_id {α : Type*} : UniformSpace.comap (id : α → α) = id := by
  ext : 2
  rw [uniformity_comap, Prod.map_id, comap_id]

theorem UniformSpace.comap_comap {α β γ} {uγ : UniformSpace γ} {f : α → β} {g : β → γ} :
    UniformSpace.comap (g ∘ f) uγ = UniformSpace.comap f (UniformSpace.comap g uγ) := by
  ext1
  simp only [uniformity_comap, Filter.comap_comap, Prod.map_comp_map]

theorem UniformSpace.comap_inf {α γ} {u₁ u₂ : UniformSpace γ} {f : α → γ} :
    (u₁ ⊓ u₂).comap f = u₁.comap f ⊓ u₂.comap f :=
  UniformSpace.ext Filter.comap_inf

theorem UniformSpace.comap_iInf {ι α γ} {u : ι → UniformSpace γ} {f : α → γ} :
    (⨅ i, u i).comap f = ⨅ i, (u i).comap f := by
  ext : 1
  simp [uniformity_comap, iInf_uniformity]

theorem UniformSpace.comap_mono {α γ} {f : α → γ} :
    Monotone fun u : UniformSpace γ => u.comap f := fun _ _ hu =>
  Filter.comap_mono hu

theorem uniformContinuous_iff {α β} {uα : UniformSpace α} {uβ : UniformSpace β} {f : α → β} :
    UniformContinuous f ↔ uα ≤ uβ.comap f :=
  Filter.map_le_iff_le_comap

theorem le_iff_uniformContinuous_id {u v : UniformSpace α} :
    u ≤ v ↔ @UniformContinuous _ _ u v id := by
  rw [uniformContinuous_iff, uniformSpace_comap_id, id]

theorem uniformContinuous_comap {f : α → β} [u : UniformSpace β] :
    @UniformContinuous α β (UniformSpace.comap f u) u f :=
  tendsto_comap

theorem uniformContinuous_comap' {f : γ → β} {g : α → γ} [v : UniformSpace β] [u : UniformSpace α]
    (h : UniformContinuous (f ∘ g)) : @UniformContinuous α γ u (UniformSpace.comap f v) g :=
  tendsto_comap_iff.2 h

namespace UniformSpace

theorem to_nhds_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) (a : α) :
    @nhds _ (@UniformSpace.toTopologicalSpace _ u₁) a ≤
      @nhds _ (@UniformSpace.toTopologicalSpace _ u₂) a := by
  rw [@nhds_eq_uniformity α u₁ a, @nhds_eq_uniformity α u₂ a]; exact lift'_mono h le_rfl

theorem toTopologicalSpace_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) :
    @UniformSpace.toTopologicalSpace _ u₁ ≤ @UniformSpace.toTopologicalSpace _ u₂ :=
  le_of_nhds_le_nhds <| to_nhds_mono h

theorem toTopologicalSpace_comap {f : α → β} {u : UniformSpace β} :
    @UniformSpace.toTopologicalSpace _ (UniformSpace.comap f u) =
      TopologicalSpace.induced f (@UniformSpace.toTopologicalSpace β u) :=
  rfl

lemma uniformSpace_eq_bot {u : UniformSpace α} : u = ⊥ ↔ idRel ∈ 𝓤[u] :=
  le_bot_iff.symm.trans le_principal_iff

protected lemma _root_.Filter.HasBasis.uniformSpace_eq_bot {ι p} {s : ι → Set (α × α)}
    {u : UniformSpace α} (h : 𝓤[u].HasBasis p s) :
    u = ⊥ ↔ ∃ i, p i ∧ Pairwise fun x y : α ↦ (x, y) ∉ s i := by
  simp [uniformSpace_eq_bot, h.mem_iff, subset_def, Pairwise, not_imp_not]

theorem toTopologicalSpace_bot : @UniformSpace.toTopologicalSpace α ⊥ = ⊥ := rfl

theorem toTopologicalSpace_top : @UniformSpace.toTopologicalSpace α ⊤ = ⊤ := rfl

theorem toTopologicalSpace_iInf {ι : Sort*} {u : ι → UniformSpace α} :
    (iInf u).toTopologicalSpace = ⨅ i, (u i).toTopologicalSpace :=
  TopologicalSpace.ext_nhds fun a ↦ by simp only [@nhds_eq_comap_uniformity _ (iInf u), nhds_iInf,
    iInf_uniformity, @nhds_eq_comap_uniformity _ (u _), Filter.comap_iInf]

theorem toTopologicalSpace_sInf {s : Set (UniformSpace α)} :
    (sInf s).toTopologicalSpace = ⨅ i ∈ s, @UniformSpace.toTopologicalSpace α i := by
  rw [sInf_eq_iInf]
  simp only [← toTopologicalSpace_iInf]

theorem toTopologicalSpace_inf {u v : UniformSpace α} :
    (u ⊓ v).toTopologicalSpace = u.toTopologicalSpace ⊓ v.toTopologicalSpace :=
  rfl

end UniformSpace

theorem UniformContinuous.continuous [UniformSpace α] [UniformSpace β] {f : α → β}
    (hf : UniformContinuous f) : Continuous f :=
  continuous_iff_le_induced.mpr <| UniformSpace.toTopologicalSpace_mono <|
    uniformContinuous_iff.1 hf

/-- Uniform space structure on `ULift α`. -/
instance ULift.uniformSpace [UniformSpace α] : UniformSpace (ULift α) :=
  UniformSpace.comap ULift.down ‹_›

/-- Uniform space structure on `αᵒᵈ`. -/
instance OrderDual.instUniformSpace [UniformSpace α] : UniformSpace (αᵒᵈ) :=
  ‹UniformSpace α›

section UniformContinuousInfi

-- Porting note: renamed for dot notation; add an `iff` lemma?
theorem UniformContinuous.inf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ u₃ : UniformSpace β}
    (h₁ : UniformContinuous[u₁, u₂] f) (h₂ : UniformContinuous[u₁, u₃] f) :
    UniformContinuous[u₁, u₂ ⊓ u₃] f :=
  tendsto_inf.mpr ⟨h₁, h₂⟩

-- Porting note: renamed for dot notation
theorem UniformContinuous.inf_dom_left {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : UniformContinuous[u₁, u₃] f) : UniformContinuous[u₁ ⊓ u₂, u₃] f :=
  tendsto_inf_left hf

-- Porting note: renamed for dot notation
theorem UniformContinuous.inf_dom_right {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : UniformContinuous[u₂, u₃] f) : UniformContinuous[u₁ ⊓ u₂, u₃] f :=
  tendsto_inf_right hf

theorem uniformContinuous_sInf_dom {f : α → β} {u₁ : Set (UniformSpace α)} {u₂ : UniformSpace β}
    {u : UniformSpace α} (h₁ : u ∈ u₁) (hf : UniformContinuous[u, u₂] f) :
    UniformContinuous[sInf u₁, u₂] f := by
  delta UniformContinuous
  rw [sInf_eq_iInf', iInf_uniformity]
  exact tendsto_iInf' ⟨u, h₁⟩ hf

theorem uniformContinuous_sInf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : Set (UniformSpace β)} :
    UniformContinuous[u₁, sInf u₂] f ↔ ∀ u ∈ u₂, UniformContinuous[u₁, u] f := by
  delta UniformContinuous
  rw [sInf_eq_iInf', iInf_uniformity, tendsto_iInf, SetCoe.forall]

theorem uniformContinuous_iInf_dom {f : α → β} {u₁ : ι → UniformSpace α} {u₂ : UniformSpace β}
    {i : ι} (hf : UniformContinuous[u₁ i, u₂] f) : UniformContinuous[iInf u₁, u₂] f := by
  delta UniformContinuous
  rw [iInf_uniformity]
  exact tendsto_iInf' i hf

theorem uniformContinuous_iInf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : ι → UniformSpace β} :
    UniformContinuous[u₁, iInf u₂] f ↔ ∀ i, UniformContinuous[u₁, u₂ i] f := by
  delta UniformContinuous
  rw [iInf_uniformity, tendsto_iInf]

end UniformContinuousInfi

/-- A uniform space with the discrete uniformity has the discrete topology. -/
theorem discreteTopology_of_discrete_uniformity [hα : UniformSpace α] (h : uniformity α = 𝓟 idRel) :
    DiscreteTopology α :=
  ⟨(UniformSpace.ext h.symm : ⊥ = hα) ▸ rfl⟩

instance : UniformSpace Empty := ⊥
instance : UniformSpace PUnit := ⊥
instance : UniformSpace Bool := ⊥
instance : UniformSpace ℕ := ⊥
instance : UniformSpace ℤ := ⊥

section

variable [UniformSpace α]

open Additive Multiplicative

instance : UniformSpace (Additive α) := ‹UniformSpace α›
instance : UniformSpace (Multiplicative α) := ‹UniformSpace α›

theorem uniformContinuous_ofMul : UniformContinuous (ofMul : α → Additive α) :=
  uniformContinuous_id

theorem uniformContinuous_toMul : UniformContinuous (toMul : Additive α → α) :=
  uniformContinuous_id

theorem uniformContinuous_ofAdd : UniformContinuous (ofAdd : α → Multiplicative α) :=
  uniformContinuous_id

theorem uniformContinuous_toAdd : UniformContinuous (toAdd : Multiplicative α → α) :=
  uniformContinuous_id

theorem uniformity_additive : 𝓤 (Additive α) = (𝓤 α).map (Prod.map ofMul ofMul) := rfl

theorem uniformity_multiplicative : 𝓤 (Multiplicative α) = (𝓤 α).map (Prod.map ofAdd ofAdd) := rfl

end

instance instUniformSpaceSubtype {p : α → Prop} [t : UniformSpace α] : UniformSpace (Subtype p) :=
  UniformSpace.comap Subtype.val t

theorem uniformity_subtype {p : α → Prop} [UniformSpace α] :
    𝓤 (Subtype p) = comap (fun q : Subtype p × Subtype p => (q.1.1, q.2.1)) (𝓤 α) :=
  rfl

theorem uniformity_setCoe {s : Set α} [UniformSpace α] :
    𝓤 s = comap (Prod.map ((↑) : s → α) ((↑) : s → α)) (𝓤 α) :=
  rfl

theorem map_uniformity_set_coe {s : Set α} [UniformSpace α] :
    map (Prod.map (↑) (↑)) (𝓤 s) = 𝓤 α ⊓ 𝓟 (s ×ˢ s) := by
  rw [uniformity_setCoe, map_comap, range_prod_map, Subtype.range_val]

theorem uniformContinuous_subtype_val {p : α → Prop} [UniformSpace α] :
    UniformContinuous (Subtype.val : { a : α // p a } → α) :=
  uniformContinuous_comap

theorem UniformContinuous.subtype_mk {p : α → Prop} [UniformSpace α] [UniformSpace β] {f : β → α}
    (hf : UniformContinuous f) (h : ∀ x, p (f x)) :
    UniformContinuous (fun x => ⟨f x, h x⟩ : β → Subtype p) :=
  uniformContinuous_comap' hf

theorem uniformContinuousOn_iff_restrict [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔ UniformContinuous (s.restrict f) := by
  delta UniformContinuousOn UniformContinuous
  rw [← map_uniformity_set_coe, tendsto_map'_iff]; rfl

theorem tendsto_of_uniformContinuous_subtype [UniformSpace α] [UniformSpace β] {f : α → β}
    {s : Set α} {a : α} (hf : UniformContinuous fun x : s => f x.val) (ha : s ∈ 𝓝 a) :
    Tendsto f (𝓝 a) (𝓝 (f a)) := by
  rw [(@map_nhds_subtype_coe_eq_nhds α _ s a (mem_of_mem_nhds ha) ha).symm]
  exact tendsto_map' hf.continuous.continuousAt

theorem UniformContinuousOn.continuousOn [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α}
    (h : UniformContinuousOn f s) : ContinuousOn f s := by
  rw [uniformContinuousOn_iff_restrict] at h
  rw [continuousOn_iff_continuous_restrict]
  exact h.continuous

@[to_additive]
instance [UniformSpace α] : UniformSpace αᵐᵒᵖ :=
  UniformSpace.comap MulOpposite.unop ‹_›

@[to_additive]
theorem uniformity_mulOpposite [UniformSpace α] :
    𝓤 αᵐᵒᵖ = comap (fun q : αᵐᵒᵖ × αᵐᵒᵖ => (q.1.unop, q.2.unop)) (𝓤 α) :=
  rfl

@[to_additive (attr := simp)]
theorem comap_uniformity_mulOpposite [UniformSpace α] :
    comap (fun p : α × α => (MulOpposite.op p.1, MulOpposite.op p.2)) (𝓤 αᵐᵒᵖ) = 𝓤 α := by
  simpa [uniformity_mulOpposite, comap_comap, (· ∘ ·)] using comap_id

namespace MulOpposite

@[to_additive]
theorem uniformContinuous_unop [UniformSpace α] : UniformContinuous (unop : αᵐᵒᵖ → α) :=
  uniformContinuous_comap

@[to_additive]
theorem uniformContinuous_op [UniformSpace α] : UniformContinuous (op : α → αᵐᵒᵖ) :=
  uniformContinuous_comap' uniformContinuous_id

end MulOpposite

section Prod

open UniformSpace

/- a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/
instance instUniformSpaceProd [u₁ : UniformSpace α] [u₂ : UniformSpace β] : UniformSpace (α × β) :=
  u₁.comap Prod.fst ⊓ u₂.comap Prod.snd

-- check the above produces no diamond for `simp` and typeclass search
example [UniformSpace α] [UniformSpace β] :
    (instTopologicalSpaceProd : TopologicalSpace (α × β)) = UniformSpace.toTopologicalSpace := by
  with_reducible_and_instances rfl

theorem uniformity_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) =
      ((𝓤 α).comap fun p : (α × β) × α × β => (p.1.1, p.2.1)) ⊓
        (𝓤 β).comap fun p : (α × β) × α × β => (p.1.2, p.2.2) :=
  rfl

instance [UniformSpace α] [IsCountablyGenerated (𝓤 α)]
    [UniformSpace β] [IsCountablyGenerated (𝓤 β)] : IsCountablyGenerated (𝓤 (α × β)) := by
  rw [uniformity_prod]
  infer_instance

theorem uniformity_prod_eq_comap_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) =
      comap (fun p : (α × β) × α × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 𝓤 β) := by
  simp_rw [uniformity_prod, prod_eq_inf, Filter.comap_inf, Filter.comap_comap, Function.comp_def]

theorem uniformity_prod_eq_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 𝓤 β) := by
  rw [map_swap4_eq_comap, uniformity_prod_eq_comap_prod]

theorem mem_uniformity_of_uniformContinuous_invariant [UniformSpace α] [UniformSpace β]
    {s : Set (β × β)} {f : α → α → β} (hf : UniformContinuous fun p : α × α => f p.1 p.2)
    (hs : s ∈ 𝓤 β) : ∃ u ∈ 𝓤 α, ∀ a b c, (a, b) ∈ u → (f a c, f b c) ∈ s := by
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff] at hf
  rcases mem_prod_iff.1 (mem_map.1 <| hf hs) with ⟨u, hu, v, hv, huvt⟩
  exact ⟨u, hu, fun a b c hab => @huvt ((_, _), (_, _)) ⟨hab, refl_mem_uniformity hv⟩⟩

/-- An entourage of the diagonal in `α` and an entourage in `β` yield an entourage in `α × β`
once we permute coordinates.-/
def entourageProd (u : Set (α × α)) (v : Set (β × β)) : Set ((α × β) × α × β) :=
  {((a₁, b₁),(a₂, b₂)) | (a₁, a₂) ∈ u ∧ (b₁, b₂) ∈ v}

theorem mem_entourageProd {u : Set (α × α)} {v : Set (β × β)} {p : (α × β) × α × β} :
    p ∈ entourageProd u v ↔ (p.1.1, p.2.1) ∈ u ∧ (p.1.2, p.2.2) ∈ v := Iff.rfl

theorem entourageProd_mem_uniformity [t₁ : UniformSpace α] [t₂ : UniformSpace β] {u : Set (α × α)}
    {v : Set (β × β)} (hu : u ∈ 𝓤 α) (hv : v ∈ 𝓤 β) :
    entourageProd u v ∈ 𝓤 (α × β) := by
  rw [uniformity_prod]; exact inter_mem_inf (preimage_mem_comap hu) (preimage_mem_comap hv)

theorem ball_entourageProd (u : Set (α × α)) (v : Set (β × β)) (x : α × β) :
    ball x (entourageProd u v) = ball x.1 u ×ˢ ball x.2 v := by
  ext p; simp only [ball, entourageProd, Set.mem_setOf_eq, Set.mem_prod, Set.mem_preimage]

theorem Filter.HasBasis.uniformity_prod {ιa ιb : Type*} [UniformSpace α] [UniformSpace β]
    {pa : ιa → Prop} {pb : ιb → Prop} {sa : ιa → Set (α × α)} {sb : ιb → Set (β × β)}
    (ha : (𝓤 α).HasBasis pa sa) (hb : (𝓤 β).HasBasis pb sb) :
    (𝓤 (α × β)).HasBasis (fun i : ιa × ιb ↦ pa i.1 ∧ pb i.2)
    (fun i ↦ entourageProd (sa i.1) (sb i.2)) :=
  (ha.comap _).inf (hb.comap _)

theorem entourageProd_subset [UniformSpace α] [UniformSpace β]
    {s : Set ((α × β) × α × β)} (h : s ∈ 𝓤 (α × β)) :
    ∃ u ∈ 𝓤 α, ∃ v ∈ 𝓤 β, entourageProd u v ⊆ s := by
  rcases (((𝓤 α).basis_sets.uniformity_prod (𝓤 β).basis_sets).mem_iff' s).1 h with ⟨w, hw⟩
  use w.1, hw.1.1, w.2, hw.1.2, hw.2

theorem tendsto_prod_uniformity_fst [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.1, p.2.1)) (𝓤 (α × β)) (𝓤 α) :=
  le_trans (map_mono inf_le_left) map_comap_le

theorem tendsto_prod_uniformity_snd [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.2, p.2.2)) (𝓤 (α × β)) (𝓤 β) :=
  le_trans (map_mono inf_le_right) map_comap_le

theorem uniformContinuous_fst [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.1 :=
  tendsto_prod_uniformity_fst

theorem uniformContinuous_snd [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.2 :=
  tendsto_prod_uniformity_snd

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

theorem UniformContinuous.prod_mk {f₁ : α → β} {f₂ : α → γ} (h₁ : UniformContinuous f₁)
    (h₂ : UniformContinuous f₂) : UniformContinuous fun a => (f₁ a, f₂ a) := by
  rw [UniformContinuous, uniformity_prod]
  exact tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

theorem UniformContinuous.prod_mk_left {f : α × β → γ} (h : UniformContinuous f) (b) :
    UniformContinuous fun a => f (a, b) :=
  h.comp (uniformContinuous_id.prod_mk uniformContinuous_const)

theorem UniformContinuous.prod_mk_right {f : α × β → γ} (h : UniformContinuous f) (a) :
    UniformContinuous fun b => f (a, b) :=
  h.comp (uniformContinuous_const.prod_mk uniformContinuous_id)

theorem UniformContinuous.prodMap [UniformSpace δ] {f : α → γ} {g : β → δ}
    (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformContinuous (Prod.map f g) :=
  (hf.comp uniformContinuous_fst).prod_mk (hg.comp uniformContinuous_snd)

@[deprecated (since := "2024-10-06")] alias UniformContinuous.prod_map := UniformContinuous.prodMap

theorem toTopologicalSpace_prod {α} {β} [u : UniformSpace α] [v : UniformSpace β] :
    @UniformSpace.toTopologicalSpace (α × β) instUniformSpaceProd =
      @instTopologicalSpaceProd α β u.toTopologicalSpace v.toTopologicalSpace :=
  rfl

/-- A version of `UniformContinuous.inf_dom_left` for binary functions -/
theorem uniformContinuous_inf_dom_left₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua1; haveI := ub1; exact UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_left₂`
  have ha := @UniformContinuous.inf_dom_left _ _ id ua1 ua2 ua1 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_left _ _ id ub1 ub2 ub1 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prodMap _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua1 ub1 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id

/-- A version of `UniformContinuous.inf_dom_right` for binary functions -/
theorem uniformContinuous_inf_dom_right₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua2; haveI := ub2; exact UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_right₂`
  have ha := @UniformContinuous.inf_dom_right _ _ id ua1 ua2 ua2 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_right _ _ id ub1 ub2 ub2 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prodMap _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua2 ub2 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id

/-- A version of `uniformContinuous_sInf_dom` for binary functions -/
theorem uniformContinuous_sInf_dom₂ {α β γ} {f : α → β → γ} {uas : Set (UniformSpace α)}
    {ubs : Set (UniformSpace β)} {ua : UniformSpace α} {ub : UniformSpace β} {uc : UniformSpace γ}
    (ha : ua ∈ uas) (hb : ub ∈ ubs) (hf : UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := sInf uas; haveI := sInf ubs
      exact @UniformContinuous _ _ _ uc fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_sInf_dom`
  let _ : UniformSpace (α × β) := instUniformSpaceProd
  have ha := uniformContinuous_sInf_dom ha uniformContinuous_id
  have hb := uniformContinuous_sInf_dom hb uniformContinuous_id
  have h_unif_cont_id := @UniformContinuous.prodMap _ _ _ _ (sInf uas) (sInf ubs) ua ub _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ hf h_unif_cont_id

end Prod

section

open UniformSpace Function

variable {δ' : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]
  [UniformSpace δ']
local notation f " ∘₂ " g => Function.bicompr f g

/-- Uniform continuity for functions of two variables. -/
def UniformContinuous₂ (f : α → β → γ) :=
  UniformContinuous (uncurry f)

theorem uniformContinuous₂_def (f : α → β → γ) :
    UniformContinuous₂ f ↔ UniformContinuous (uncurry f) :=
  Iff.rfl

theorem UniformContinuous₂.uniformContinuous {f : α → β → γ} (h : UniformContinuous₂ f) :
    UniformContinuous (uncurry f) :=
  h

theorem uniformContinuous₂_curry (f : α × β → γ) :
    UniformContinuous₂ (Function.curry f) ↔ UniformContinuous f := by
  rw [UniformContinuous₂, uncurry_curry]

theorem UniformContinuous₂.comp {f : α → β → γ} {g : γ → δ} (hg : UniformContinuous g)
    (hf : UniformContinuous₂ f) : UniformContinuous₂ (g ∘₂ f) :=
  hg.comp hf

theorem UniformContinuous₂.bicompl {f : α → β → γ} {ga : δ → α} {gb : δ' → β}
    (hf : UniformContinuous₂ f) (hga : UniformContinuous ga) (hgb : UniformContinuous gb) :
    UniformContinuous₂ (bicompl f ga gb) :=
  hf.uniformContinuous.comp (hga.prodMap hgb)

end

theorem toTopologicalSpace_subtype [u : UniformSpace α] {p : α → Prop} :
    @UniformSpace.toTopologicalSpace (Subtype p) instUniformSpaceSubtype =
      @instTopologicalSpaceSubtype α p u.toTopologicalSpace :=
  rfl

section Sum

variable [UniformSpace α] [UniformSpace β]

open Sum

-- Obsolete auxiliary definitions and lemmas

/-- Uniformity on a disjoint union. Entourages of the diagonal in the union are obtained
by taking independently an entourage of the diagonal in the first part, and an entourage of
the diagonal in the second part. -/
instance Sum.instUniformSpace : UniformSpace (α ⊕ β) where
  uniformity := map (fun p : α × α => (inl p.1, inl p.2)) (𝓤 α) ⊔
    map (fun p : β × β => (inr p.1, inr p.2)) (𝓤 β)
  symm := fun _ hs ↦ ⟨symm_le_uniformity hs.1, symm_le_uniformity hs.2⟩
  comp := fun s hs ↦ by
    rcases comp_mem_uniformity_sets hs.1 with ⟨tα, htα, Htα⟩
    rcases comp_mem_uniformity_sets hs.2 with ⟨tβ, htβ, Htβ⟩
    filter_upwards [mem_lift' (union_mem_sup (image_mem_map htα) (image_mem_map htβ))]
    rintro ⟨_, _⟩ ⟨z, ⟨⟨a, b⟩, hab, ⟨⟩⟩ | ⟨⟨a, b⟩, hab, ⟨⟩⟩, ⟨⟨_, c⟩, hbc, ⟨⟩⟩ | ⟨⟨_, c⟩, hbc, ⟨⟩⟩⟩
    exacts [@Htα (_, _) ⟨b, hab, hbc⟩, @Htβ (_, _) ⟨b, hab, hbc⟩]
  nhds_eq_comap_uniformity x := by
    ext
    cases x <;> simp [mem_comap', -mem_comap, nhds_inl, nhds_inr, nhds_eq_comap_uniformity,
      Prod.ext_iff]

@[reducible, deprecated (since := "2024-02-15")] alias Sum.uniformSpace := Sum.instUniformSpace

/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage
of the diagonal. -/
theorem union_mem_uniformity_sum {a : Set (α × α)} (ha : a ∈ 𝓤 α) {b : Set (β × β)} (hb : b ∈ 𝓤 β) :
    Prod.map inl inl '' a ∪ Prod.map inr inr '' b ∈ 𝓤 (α ⊕ β) :=
  union_mem_sup (image_mem_map ha) (image_mem_map hb)

theorem Sum.uniformity : 𝓤 (α ⊕ β) = map (Prod.map inl inl) (𝓤 α) ⊔ map (Prod.map inr inr) (𝓤 β) :=
  rfl

lemma uniformContinuous_inl : UniformContinuous (Sum.inl : α → α ⊕ β) := le_sup_left
lemma uniformContinuous_inr : UniformContinuous (Sum.inr : β → α ⊕ β) := le_sup_right

instance [IsCountablyGenerated (𝓤 α)] [IsCountablyGenerated (𝓤 β)] :
    IsCountablyGenerated (𝓤 (α ⊕ β)) := by
  rw [Sum.uniformity]
  infer_instance

end Sum

end Constructions

/-!
### Expressing continuity properties in uniform spaces

We reformulate the various continuity properties of functions taking values in a uniform space
in terms of the uniformity in the target. Since the same lemmas (essentially with the same names)
also exist for metric spaces and emetric spaces (reformulating things in terms of the distance or
the edistance in the target), we put them in a namespace `Uniform` here.

In the metric and emetric space setting, there are also similar lemmas where one assumes that
both the source and the target are metric spaces, reformulating things in terms of the distance
on both sides. These lemmas are generally written without primes, and the versions where only
the target is a metric space is primed. We follow the same convention here, thus giving lemmas
with primes.
-/


namespace Uniform

variable [UniformSpace α]

theorem tendsto_nhds_right {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α) := by
  rw [nhds_eq_comap_uniformity, tendsto_comap_iff]; rfl

theorem tendsto_nhds_left {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (u x, a)) f (𝓤 α) := by
  rw [nhds_eq_comap_uniformity', tendsto_comap_iff]; rfl

theorem continuousAt_iff'_right [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt, tendsto_nhds_right]

theorem continuousAt_iff'_left [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt, tendsto_nhds_left]

theorem continuousAt_iff_prod [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x : β × β => (f x.1, f x.2)) (𝓝 (b, b)) (𝓤 α) :=
  ⟨fun H => le_trans (H.prodMap' H) (nhds_le_uniformity _), fun H =>
    continuousAt_iff'_left.2 <| H.comp <| tendsto_id.prod_mk_nhds tendsto_const_nhds⟩

theorem continuousWithinAt_iff'_right [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_right]

theorem continuousWithinAt_iff'_left [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_left]

theorem continuousOn_iff'_right [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuousWithinAt_iff'_right]

theorem continuousOn_iff'_left [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuousWithinAt_iff'_left]

theorem continuous_iff'_right [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds_right

theorem continuous_iff'_left [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds_left

/-- Consider two functions `f` and `g` which coincide on a set `s` and are continuous there.
Then there is an open neighborhood of `s` on which `f` and `g` are uniformly close. -/
lemma exists_is_open_mem_uniformity_of_forall_mem_eq
    [TopologicalSpace β] {r : Set (α × α)} {s : Set β}
    {f g : β → α} (hf : ∀ x ∈ s, ContinuousAt f x) (hg : ∀ x ∈ s, ContinuousAt g x)
    (hfg : s.EqOn f g) (hr : r ∈ 𝓤 α) :
    ∃ t, IsOpen t ∧ s ⊆ t ∧ ∀ x ∈ t, (f x, g x) ∈ r := by
  have A : ∀ x ∈ s, ∃ t, IsOpen t ∧ x ∈ t ∧ ∀ z ∈ t, (f z, g z) ∈ r := by
    intro x hx
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    have A : {z | (f x, f z) ∈ t} ∈ 𝓝 x := (hf x hx).preimage_mem_nhds (mem_nhds_left (f x) ht)
    have B : {z | (g x, g z) ∈ t} ∈ 𝓝 x := (hg x hx).preimage_mem_nhds (mem_nhds_left (g x) ht)
    rcases _root_.mem_nhds_iff.1 (inter_mem A B) with ⟨u, hu, u_open, xu⟩
    refine ⟨u, u_open, xu, fun y hy ↦ ?_⟩
    have I1 : (f y, f x) ∈ t := (htsymm.mk_mem_comm).2 (hu hy).1
    have I2 : (g x, g y) ∈ t := (hu hy).2
    rw [hfg hx] at I1
    exact htr (prod_mk_mem_compRel I1 I2)
  choose! t t_open xt ht using A
  refine ⟨⋃ x ∈ s, t x, isOpen_biUnion t_open, fun x hx ↦ mem_biUnion hx (xt x hx), ?_⟩
  rintro x hx
  simp only [mem_iUnion, exists_prop] at hx
  rcases hx with ⟨y, ys, hy⟩
  exact ht y ys x hy

end Uniform

theorem Filter.Tendsto.congr_uniformity {α β} [UniformSpace β] {f g : α → β} {l : Filter α} {b : β}
    (hf : Tendsto f l (𝓝 b)) (hg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto g l (𝓝 b) :=
  Uniform.tendsto_nhds_right.2 <| (Uniform.tendsto_nhds_right.1 hf).uniformity_trans hg

theorem Uniform.tendsto_congr {α β} [UniformSpace β] {f g : α → β} {l : Filter α} {b : β}
    (hfg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto f l (𝓝 b) ↔ Tendsto g l (𝓝 b) :=
  ⟨fun h => h.congr_uniformity hfg, fun h => h.congr_uniformity hfg.uniformity_symm⟩

set_option linter.style.longFile 1900

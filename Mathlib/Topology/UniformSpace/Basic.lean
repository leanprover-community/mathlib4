/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Order.Filter.SmallSets
import Mathlib.Tactic.Monotonicity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.NhdsSet
import Mathlib.Algebra.Group.Defs

#align_import topology.uniform_space.basic from "leanprover-community/mathlib"@"195fcd60ff2bfe392543bceb0ec2adcdb472db4c"

/-!
# Uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* uniform continuity (in this file)
* completeness (in `Cauchy.lean`)
* extension of uniform continuous functions to complete spaces (in `UniformEmbedding.lean`)
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
#align id_rel idRel

@[simp]
theorem mem_idRel {a b : α} : (a, b) ∈ @idRel α ↔ a = b :=
  Iff.rfl
#align mem_id_rel mem_idRel

@[simp]
theorem idRel_subset {s : Set (α × α)} : idRel ⊆ s ↔ ∀ a, (a, a) ∈ s := by
  simp [subset_def]
#align id_rel_subset idRel_subset

/-- The composition of relations -/
def compRel (r₁ r₂ : Set (α × α)) :=
  { p : α × α | ∃ z : α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂ }
#align comp_rel compRel

@[inherit_doc]
scoped[Uniformity] infixl:62 " ○ " => compRel
open Uniformity

@[simp]
theorem mem_compRel {α : Type u} {r₁ r₂ : Set (α × α)} {x y : α} :
    (x, y) ∈ r₁ ○ r₂ ↔ ∃ z, (x, z) ∈ r₁ ∧ (z, y) ∈ r₂ :=
  Iff.rfl
#align mem_comp_rel mem_compRel

@[simp]
theorem swap_idRel : Prod.swap '' idRel = @idRel α :=
  Set.ext fun ⟨a, b⟩ => by simpa [image_swap_eq_preimage_swap] using eq_comm
#align swap_id_rel swap_idRel

theorem Monotone.compRel [Preorder β] {f g : β → Set (α × α)} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ○ g x := fun _ _ h _ ⟨z, h₁, h₂⟩ => ⟨z, hf h h₁, hg h h₂⟩
#align monotone.comp_rel Monotone.compRel

@[mono]
theorem compRel_mono {f g h k : Set (α × α)} (h₁ : f ⊆ h) (h₂ : g ⊆ k) : f ○ g ⊆ h ○ k :=
  fun _ ⟨z, h, h'⟩ => ⟨z, h₁ h, h₂ h'⟩
#align comp_rel_mono compRel_mono

theorem prod_mk_mem_compRel {a b c : α} {s t : Set (α × α)} (h₁ : (a, c) ∈ s) (h₂ : (c, b) ∈ t) :
    (a, b) ∈ s ○ t :=
  ⟨c, h₁, h₂⟩
#align prod_mk_mem_comp_rel prod_mk_mem_compRel

@[simp]
theorem id_compRel {r : Set (α × α)} : idRel ○ r = r :=
  Set.ext fun ⟨a, b⟩ => by simp
#align id_comp_rel id_compRel

theorem compRel_assoc {r s t : Set (α × α)} : r ○ s ○ t = r ○ (s ○ t) := by
  ext ⟨a, b⟩; simp only [mem_compRel]; tauto
#align comp_rel_assoc compRel_assoc

theorem left_subset_compRel {s t : Set (α × α)} (h : idRel ⊆ t) : s ⊆ s ○ t := fun ⟨_x, y⟩ xy_in =>
  ⟨y, xy_in, h <| rfl⟩
#align left_subset_comp_rel left_subset_compRel

theorem right_subset_compRel {s t : Set (α × α)} (h : idRel ⊆ s) : t ⊆ s ○ t := fun ⟨x, _y⟩ xy_in =>
  ⟨x, h <| rfl, xy_in⟩
#align right_subset_comp_rel right_subset_compRel

theorem subset_comp_self {s : Set (α × α)} (h : idRel ⊆ s) : s ⊆ s ○ s :=
  left_subset_compRel h
#align subset_comp_self subset_comp_self

theorem subset_iterate_compRel {s t : Set (α × α)} (h : idRel ⊆ s) (n : ℕ) :
    t ⊆ (s ○ ·)^[n] t := by
  induction' n with n ihn generalizing t
  exacts [Subset.rfl, (right_subset_compRel h).trans ihn]
#align subset_iterate_comp_rel subset_iterate_compRel

/-- The relation is invariant under swapping factors. -/
def SymmetricRel (V : Set (α × α)) : Prop :=
  Prod.swap ⁻¹' V = V
#align symmetric_rel SymmetricRel

/-- The maximal symmetric relation contained in a given relation. -/
def symmetrizeRel (V : Set (α × α)) : Set (α × α) :=
  V ∩ Prod.swap ⁻¹' V
#align symmetrize_rel symmetrizeRel

theorem symmetric_symmetrizeRel (V : Set (α × α)) : SymmetricRel (symmetrizeRel V) := by
  simp [SymmetricRel, symmetrizeRel, preimage_inter, inter_comm, ← preimage_comp]
#align symmetric_symmetrize_rel symmetric_symmetrizeRel

theorem symmetrizeRel_subset_self (V : Set (α × α)) : symmetrizeRel V ⊆ V :=
  sep_subset _ _
#align symmetrize_rel_subset_self symmetrizeRel_subset_self

@[mono]
theorem symmetrize_mono {V W : Set (α × α)} (h : V ⊆ W) : symmetrizeRel V ⊆ symmetrizeRel W :=
  inter_subset_inter h <| preimage_mono h
#align symmetrize_mono symmetrize_mono

theorem SymmetricRel.mk_mem_comm {V : Set (α × α)} (hV : SymmetricRel V) {x y : α} :
    (x, y) ∈ V ↔ (y, x) ∈ V :=
  Set.ext_iff.1 hV (y, x)
#align symmetric_rel.mk_mem_comm SymmetricRel.mk_mem_comm

theorem SymmetricRel.eq {U : Set (α × α)} (hU : SymmetricRel U) : Prod.swap ⁻¹' U = U :=
  hU
#align symmetric_rel.eq SymmetricRel.eq

theorem SymmetricRel.inter {U V : Set (α × α)} (hU : SymmetricRel U) (hV : SymmetricRel V) :
    SymmetricRel (U ∩ V) := by rw [SymmetricRel, preimage_inter, hU.eq, hV.eq]
#align symmetric_rel.inter SymmetricRel.inter

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
#align uniform_space.core UniformSpace.Core

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
#align uniform_space.core.mk' UniformSpace.Core.mk'

/-- Defining a `UniformSpace.Core` from a filter basis satisfying some uniformity-like axioms. -/
def UniformSpace.Core.mkOfBasis {α : Type u} (B : FilterBasis (α × α))
    (refl : ∀ r ∈ B, ∀ (x), (x, x) ∈ r) (symm : ∀ r ∈ B, ∃ t ∈ B, t ⊆ Prod.swap ⁻¹' r)
    (comp : ∀ r ∈ B, ∃ t ∈ B, t ○ t ⊆ r) : UniformSpace.Core α where
  uniformity := B.filter
  refl := B.hasBasis.ge_iff.mpr fun _r ru => idRel_subset.2 <| refl _ ru
  symm := (B.hasBasis.tendsto_iff B.hasBasis).mpr symm
  comp := (HasBasis.le_basis_iff (B.hasBasis.lift' (monotone_id.compRel monotone_id))
    B.hasBasis).2 comp
#align uniform_space.core.mk_of_basis UniformSpace.Core.mkOfBasis

/-- A uniform space generates a topological space -/
def UniformSpace.Core.toTopologicalSpace {α : Type u} (u : UniformSpace.Core α) :
    TopologicalSpace α :=
  .mkOfNhds fun x ↦ .comap (Prod.mk x) u.uniformity
#align uniform_space.core.to_topological_space UniformSpace.Core.toTopologicalSpace

theorem UniformSpace.Core.ext :
    ∀ {u₁ u₂ : UniformSpace.Core α}, u₁.uniformity = u₂.uniformity → u₁ = u₂
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
#align uniform_space.core_eq UniformSpace.Core.ext

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
#align uniform_space UniformSpace

#noalign uniform_space.mk' -- Can't be a `match_pattern`, so not useful anymore

/-- The uniformity is a filter on α × α (inferred from an ambient uniform space
  structure on α). -/
def uniformity (α : Type u) [UniformSpace α] : Filter (α × α) :=
  @UniformSpace.uniformity α _
#align uniformity uniformity

/-- Notation for the uniformity filter with respect to a non-standard `UniformSpace` instance. -/
scoped[Uniformity] notation "𝓤[" u "]" => @uniformity _ u

@[inherit_doc] -- Porting note (#11215): TODO: should we drop the `uniformity` def?
scoped[Uniformity] notation "𝓤" => uniformity

/-- Construct a `UniformSpace` from a `u : UniformSpace.Core` and a `TopologicalSpace` structure
that is equal to `u.toTopologicalSpace`. -/
abbrev UniformSpace.ofCoreEq {α : Type u} (u : UniformSpace.Core α) (t : TopologicalSpace α)
    (h : t = u.toTopologicalSpace) : UniformSpace α where
  __ := u
  toTopologicalSpace := t
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_toTopologicalSpace]
#align uniform_space.of_core_eq UniformSpace.ofCoreEq

/-- Construct a `UniformSpace` from a `UniformSpace.Core`. -/
abbrev UniformSpace.ofCore {α : Type u} (u : UniformSpace.Core α) : UniformSpace α :=
  .ofCoreEq u _ rfl
#align uniform_space.of_core UniformSpace.ofCore

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
#align uniform_space.to_core_to_topological_space UniformSpace.toCore_toTopologicalSpace

/-- Build a `UniformSpace` from a `UniformSpace.Core` and a compatible topology.
Use `UnifiormSpace.mk` instead to avoid proving
the unnecessary assumption `UniformSpace.Core.refl`.

The main constructor used to use a different compatibility assumption.
This definition was created as a step towards porting to a new definition.
Now the main definition is ported,
so this constructor will be removed in a few months. -/
@[deprecated UniformSpace.mk]
def UniformSpace.ofNhdsEqComap (u : UniformSpace.Core α) (_t : TopologicalSpace α)
    (h : ∀ x, 𝓝 x = u.uniformity.comap (Prod.mk x)) : UniformSpace α where
  __ := u
  nhds_eq_comap_uniformity := h

@[ext]
protected theorem UniformSpace.ext {u₁ u₂ : UniformSpace α} (h : 𝓤[u₁] = 𝓤[u₂]) : u₁ = u₂ := by
  have : u₁.toTopologicalSpace = u₂.toTopologicalSpace := TopologicalSpace.ext_nhds fun x ↦ by
    rw [u₁.nhds_eq_comap_uniformity, u₂.nhds_eq_comap_uniformity]
    exact congr_arg (comap _) h
  cases u₁; cases u₂; congr
#align uniform_space_eq UniformSpace.ext

protected theorem UniformSpace.ext_iff {u₁ u₂ : UniformSpace α} :
    u₁ = u₂ ↔ ∀ s, s ∈ 𝓤[u₁] ↔ s ∈ 𝓤[u₂] :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩

theorem UniformSpace.ofCoreEq_toCore (u : UniformSpace α) (t : TopologicalSpace α)
    (h : t = u.toCore.toTopologicalSpace) : .ofCoreEq u.toCore t h = u :=
  UniformSpace.ext rfl
#align uniform_space.of_core_eq_to_core UniformSpace.ofCoreEq_toCore

/-- Replace topology in a `UniformSpace` instance with a propositionally (but possibly not
definitionally) equal one. -/
abbrev UniformSpace.replaceTopology {α : Type*} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : UniformSpace α where
  __ := u
  toTopologicalSpace := i
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_eq_comap_uniformity]
#align uniform_space.replace_topology UniformSpace.replaceTopology

theorem UniformSpace.replaceTopology_eq {α : Type*} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : u.replaceTopology h = u :=
  UniformSpace.ext rfl
#align uniform_space.replace_topology_eq UniformSpace.replaceTopology_eq

-- Porting note: rfc: use `UniformSpace.Core.mkOfBasis`? This will change defeq here and there
/-- Define a `UniformSpace` using a "distance" function. The function can be, e.g., the
distance in a (usual or extended) metric space or an absolute value on a ring. -/
def UniformSpace.ofFun {α : Type u} {β : Type v} [OrderedAddCommMonoid β]
    (d : α → α → β) (refl : ∀ x, d x x = 0) (symm : ∀ x y, d x y = d y x)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (half : ∀ ε > (0 : β), ∃ δ > (0 : β), ∀ x < δ, ∀ y < δ, x + y < ε) :
    UniformSpace α :=
  .ofCore
    { uniformity := ⨅ r > 0, 𝓟 { x | d x.1 x.2 < r }
      refl := le_iInf₂ fun r hr => principal_mono.2 <| idRel_subset.2 fun x => by simpa [refl]
      symm := tendsto_iInf_iInf fun r => tendsto_iInf_iInf fun _ => tendsto_principal_principal.2
        fun x hx => by rwa [mem_setOf, symm]
      comp := le_iInf₂ fun r hr => let ⟨δ, h0, hδr⟩ := half r hr; le_principal_iff.2 <|
        mem_of_superset
          (mem_lift' <| mem_iInf_of_mem δ <| mem_iInf_of_mem h0 <| mem_principal_self _)
          fun (x, z) ⟨y, h₁, h₂⟩ => (triangle _ _ _).trans_lt (hδr _ h₁ _ h₂) }
#align uniform_space.of_fun UniformSpace.ofFun

theorem UniformSpace.hasBasis_ofFun {α : Type u} {β : Type v} [LinearOrderedAddCommMonoid β]
    (h₀ : ∃ x : β, 0 < x) (d : α → α → β) (refl : ∀ x, d x x = 0) (symm : ∀ x y, d x y = d y x)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (half : ∀ ε > (0 : β), ∃ δ > (0 : β), ∀ x < δ, ∀ y < δ, x + y < ε) :
    𝓤[.ofFun d refl symm triangle half].HasBasis ((0 : β) < ·) (fun ε => { x | d x.1 x.2 < ε }) :=
  hasBasis_biInf_principal'
    (fun ε₁ h₁ ε₂ h₂ => ⟨min ε₁ ε₂, lt_min h₁ h₂, fun _x hx => lt_of_lt_of_le hx (min_le_left _ _),
      fun _x hx => lt_of_lt_of_le hx (min_le_right _ _)⟩) h₀
#align uniform_space.has_basis_of_fun UniformSpace.hasBasis_ofFun

section UniformSpace

variable [UniformSpace α]

theorem nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α).comap (Prod.mk x) :=
  UniformSpace.nhds_eq_comap_uniformity x
#align nhds_eq_comap_uniformity nhds_eq_comap_uniformity

theorem isOpen_uniformity {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α := by
  simp only [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap_prod_mk]
#align is_open_uniformity isOpen_uniformity

theorem refl_le_uniformity : 𝓟 idRel ≤ 𝓤 α :=
  (@UniformSpace.toCore α _).refl
#align refl_le_uniformity refl_le_uniformity

instance uniformity.neBot [Nonempty α] : NeBot (𝓤 α) :=
  diagonal_nonempty.principal_neBot.mono refl_le_uniformity
#align uniformity.ne_bot uniformity.neBot

theorem refl_mem_uniformity {x : α} {s : Set (α × α)} (h : s ∈ 𝓤 α) : (x, x) ∈ s :=
  refl_le_uniformity h rfl
#align refl_mem_uniformity refl_mem_uniformity

theorem mem_uniformity_of_eq {x y : α} {s : Set (α × α)} (h : s ∈ 𝓤 α) (hx : x = y) : (x, y) ∈ s :=
  refl_le_uniformity h hx
#align mem_uniformity_of_eq mem_uniformity_of_eq

theorem symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) ≤ 𝓤 _ :=
  UniformSpace.symm
#align symm_le_uniformity symm_le_uniformity

theorem comp_le_uniformity : ((𝓤 α).lift' fun s : Set (α × α) => s ○ s) ≤ 𝓤 α :=
  UniformSpace.comp
#align comp_le_uniformity comp_le_uniformity

theorem lift'_comp_uniformity : ((𝓤 α).lift' fun s : Set (α × α) => s ○ s) = 𝓤 α :=
  comp_le_uniformity.antisymm <| le_lift'.2 fun _s hs ↦ mem_of_superset hs <|
    subset_comp_self <| idRel_subset.2 fun _ ↦ refl_mem_uniformity hs

theorem tendsto_swap_uniformity : Tendsto (@Prod.swap α α) (𝓤 α) (𝓤 α) :=
  symm_le_uniformity
#align tendsto_swap_uniformity tendsto_swap_uniformity

theorem comp_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ t ⊆ s :=
  (mem_lift'_sets <| monotone_id.compRel monotone_id).mp <| comp_le_uniformity hs
#align comp_mem_uniformity_sets comp_mem_uniformity_sets

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
#align eventually_uniformity_iterate_comp_subset eventually_uniformity_iterate_comp_subset

/-- If `s ∈ 𝓤 α`, then for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ⊆ s`. -/
theorem eventually_uniformity_comp_subset {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∀ᶠ t in (𝓤 α).smallSets, t ○ t ⊆ s :=
  eventually_uniformity_iterate_comp_subset hs 1
#align eventually_uniformity_comp_subset eventually_uniformity_comp_subset

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is transitive. -/
theorem Filter.Tendsto.uniformity_trans {l : Filter β} {f₁ f₂ f₃ : β → α}
    (h₁₂ : Tendsto (fun x => (f₁ x, f₂ x)) l (𝓤 α))
    (h₂₃ : Tendsto (fun x => (f₂ x, f₃ x)) l (𝓤 α)) : Tendsto (fun x => (f₁ x, f₃ x)) l (𝓤 α) := by
  refine le_trans (le_lift'.2 fun s hs => mem_map.2 ?_) comp_le_uniformity
  filter_upwards [mem_map.1 (h₁₂ hs), mem_map.1 (h₂₃ hs)] with x hx₁₂ hx₂₃ using ⟨_, hx₁₂, hx₂₃⟩
#align filter.tendsto.uniformity_trans Filter.Tendsto.uniformity_trans

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is symmetric. -/
theorem Filter.Tendsto.uniformity_symm {l : Filter β} {f : β → α × α} (h : Tendsto f l (𝓤 α)) :
    Tendsto (fun x => ((f x).2, (f x).1)) l (𝓤 α) :=
  tendsto_swap_uniformity.comp h
#align filter.tendsto.uniformity_symm Filter.Tendsto.uniformity_symm

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is reflexive. -/
theorem tendsto_diag_uniformity (f : β → α) (l : Filter β) :
    Tendsto (fun x => (f x, f x)) l (𝓤 α) := fun _s hs =>
  mem_map.2 <| univ_mem' fun _ => refl_mem_uniformity hs
#align tendsto_diag_uniformity tendsto_diag_uniformity

theorem tendsto_const_uniformity {a : α} {f : Filter β} : Tendsto (fun _ => (a, a)) f (𝓤 α) :=
  tendsto_diag_uniformity (fun _ => a) f
#align tendsto_const_uniformity tendsto_const_uniformity

theorem symm_of_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, (∀ a b, (a, b) ∈ t → (b, a) ∈ t) ∧ t ⊆ s :=
  have : preimage Prod.swap s ∈ 𝓤 α := symm_le_uniformity hs
  ⟨s ∩ preimage Prod.swap s, inter_mem hs this, fun _ _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, inter_subset_left _ _⟩
#align symm_of_uniformity symm_of_uniformity

theorem comp_symm_of_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, (∀ {a b}, (a, b) ∈ t → (b, a) ∈ t) ∧ t ○ t ⊆ s :=
  let ⟨_t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  let ⟨t', ht', ht'₁, ht'₂⟩ := symm_of_uniformity ht₁
  ⟨t', ht', ht'₁ _ _, Subset.trans (monotone_id.compRel monotone_id ht'₂) ht₂⟩
#align comp_symm_of_uniformity comp_symm_of_uniformity

theorem uniformity_le_symm : 𝓤 α ≤ @Prod.swap α α <$> 𝓤 α := by
  rw [map_swap_eq_comap_swap]; exact tendsto_swap_uniformity.le_comap
#align uniformity_le_symm uniformity_le_symm

theorem uniformity_eq_symm : 𝓤 α = @Prod.swap α α <$> 𝓤 α :=
  le_antisymm uniformity_le_symm symm_le_uniformity
#align uniformity_eq_symm uniformity_eq_symm

@[simp]
theorem comap_swap_uniformity : comap (@Prod.swap α α) (𝓤 α) = 𝓤 α :=
  (congr_arg _ uniformity_eq_symm).trans <| comap_map Prod.swap_injective
#align comap_swap_uniformity comap_swap_uniformity

theorem symmetrize_mem_uniformity {V : Set (α × α)} (h : V ∈ 𝓤 α) : symmetrizeRel V ∈ 𝓤 α := by
  apply (𝓤 α).inter_sets h
  rw [← image_swap_eq_preimage_swap, uniformity_eq_symm]
  exact image_mem_map h
#align symmetrize_mem_uniformity symmetrize_mem_uniformity

/-- Symmetric entourages form a basis of `𝓤 α` -/
theorem UniformSpace.hasBasis_symmetric :
    (𝓤 α).HasBasis (fun s : Set (α × α) => s ∈ 𝓤 α ∧ SymmetricRel s) id :=
  hasBasis_self.2 fun t t_in =>
    ⟨symmetrizeRel t, symmetrize_mem_uniformity t_in, symmetric_symmetrizeRel t,
      symmetrizeRel_subset_self t⟩
#align uniform_space.has_basis_symmetric UniformSpace.hasBasis_symmetric

theorem uniformity_lift_le_swap {g : Set (α × α) → Filter β} {f : Filter β} (hg : Monotone g)
    (h : ((𝓤 α).lift fun s => g (preimage Prod.swap s)) ≤ f) : (𝓤 α).lift g ≤ f :=
  calc
    (𝓤 α).lift g ≤ (Filter.map (@Prod.swap α α) <| 𝓤 α).lift g :=
      lift_mono uniformity_le_symm le_rfl
    _ ≤ _ := by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h
#align uniformity_lift_le_swap uniformity_lift_le_swap

theorem uniformity_lift_le_comp {f : Set (α × α) → Filter β} (h : Monotone f) :
    ((𝓤 α).lift fun s => f (s ○ s)) ≤ (𝓤 α).lift f :=
  calc
    ((𝓤 α).lift fun s => f (s ○ s)) = ((𝓤 α).lift' fun s : Set (α × α) => s ○ s).lift f := by
      rw [lift_lift'_assoc]
      · exact monotone_id.compRel monotone_id
      · exact h
    _ ≤ (𝓤 α).lift f := lift_mono comp_le_uniformity le_rfl
#align uniformity_lift_le_comp uniformity_lift_le_comp

-- Porting note (#10756): new lemma
theorem comp3_mem_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ (t ○ t) ⊆ s :=
  let ⟨_t', ht', ht's⟩ := comp_mem_uniformity_sets hs
  let ⟨t, ht, htt'⟩ := comp_mem_uniformity_sets ht'
  ⟨t, ht, (compRel_mono ((subset_comp_self (refl_le_uniformity ht)).trans htt') htt').trans ht's⟩

/-- See also `comp3_mem_uniformity`. -/
theorem comp_le_uniformity3 : ((𝓤 α).lift' fun s : Set (α × α) => s ○ (s ○ s)) ≤ 𝓤 α := fun _ h =>
  let ⟨_t, htU, ht⟩ := comp3_mem_uniformity h
  mem_of_superset (mem_lift' htU) ht
#align comp_le_uniformity3 comp_le_uniformity3

/-- See also `comp_open_symm_mem_uniformity_sets`. -/
theorem comp_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SymmetricRel t ∧ t ○ t ⊆ s := by
  obtain ⟨w, w_in, w_sub⟩ : ∃ w ∈ 𝓤 α, w ○ w ⊆ s := comp_mem_uniformity_sets hs
  use symmetrizeRel w, symmetrize_mem_uniformity w_in, symmetric_symmetrizeRel w
  have : symmetrizeRel w ⊆ w := symmetrizeRel_subset_self w
  calc symmetrizeRel w ○ symmetrizeRel w
    _ ⊆ w ○ w := by mono
    _ ⊆ s     := w_sub
#align comp_symm_mem_uniformity_sets comp_symm_mem_uniformity_sets

theorem subset_comp_self_of_mem_uniformity {s : Set (α × α)} (h : s ∈ 𝓤 α) : s ⊆ s ○ s :=
  subset_comp_self (refl_le_uniformity h)
#align subset_comp_self_of_mem_uniformity subset_comp_self_of_mem_uniformity

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
#align comp_comp_symm_mem_uniformity_sets comp_comp_symm_mem_uniformity_sets

/-!
### Balls in uniform spaces
-/

/-- The ball around `(x : β)` with respect to `(V : Set (β × β))`. Intended to be
used for `V ∈ 𝓤 β`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`.  -/
def UniformSpace.ball (x : β) (V : Set (β × β)) : Set β :=
  Prod.mk x ⁻¹' V
#align uniform_space.ball UniformSpace.ball

open UniformSpace (ball)

theorem UniformSpace.mem_ball_self (x : α) {V : Set (α × α)} (hV : V ∈ 𝓤 α) : x ∈ ball x V :=
  refl_mem_uniformity hV
#align uniform_space.mem_ball_self UniformSpace.mem_ball_self

/-- The triangle inequality for `UniformSpace.ball` -/
theorem mem_ball_comp {V W : Set (β × β)} {x y z} (h : y ∈ ball x V) (h' : z ∈ ball y W) :
    z ∈ ball x (V ○ W) :=
  prod_mk_mem_compRel h h'
#align mem_ball_comp mem_ball_comp

theorem ball_subset_of_comp_subset {V W : Set (β × β)} {x y} (h : x ∈ ball y W) (h' : W ○ W ⊆ V) :
    ball x W ⊆ ball y V := fun _z z_in => h' (mem_ball_comp h z_in)
#align ball_subset_of_comp_subset ball_subset_of_comp_subset

theorem ball_mono {V W : Set (β × β)} (h : V ⊆ W) (x : β) : ball x V ⊆ ball x W :=
  preimage_mono h
#align ball_mono ball_mono

theorem ball_inter (x : β) (V W : Set (β × β)) : ball x (V ∩ W) = ball x V ∩ ball x W :=
  preimage_inter
#align ball_inter ball_inter

theorem ball_inter_left (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x V :=
  ball_mono (inter_subset_left V W) x
#align ball_inter_left ball_inter_left

theorem ball_inter_right (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x W :=
  ball_mono (inter_subset_right V W) x
#align ball_inter_right ball_inter_right

theorem mem_ball_symmetry {V : Set (β × β)} (hV : SymmetricRel V) {x y} :
    x ∈ ball y V ↔ y ∈ ball x V :=
  show (x, y) ∈ Prod.swap ⁻¹' V ↔ (x, y) ∈ V by
    unfold SymmetricRel at hV
    rw [hV]
#align mem_ball_symmetry mem_ball_symmetry

theorem ball_eq_of_symmetry {V : Set (β × β)} (hV : SymmetricRel V) {x} :
    ball x V = { y | (y, x) ∈ V } := by
  ext y
  rw [mem_ball_symmetry hV]
  exact Iff.rfl
#align ball_eq_of_symmetry ball_eq_of_symmetry

theorem mem_comp_of_mem_ball {V W : Set (β × β)} {x y z : β} (hV : SymmetricRel V)
    (hx : x ∈ ball z V) (hy : y ∈ ball z W) : (x, y) ∈ V ○ W := by
  rw [mem_ball_symmetry hV] at hx
  exact ⟨z, hx, hy⟩
#align mem_comp_of_mem_ball mem_comp_of_mem_ball

theorem UniformSpace.isOpen_ball (x : α) {V : Set (α × α)} (hV : IsOpen V) : IsOpen (ball x V) :=
  hV.preimage <| continuous_const.prod_mk continuous_id
#align uniform_space.is_open_ball UniformSpace.isOpen_ball

theorem UniformSpace.isClosed_ball (x : α) {V : Set (α × α)} (hV : IsClosed V) :
    IsClosed (ball x V) :=
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
#align mem_comp_comp mem_comp_comp

/-!
### Neighborhoods in uniform spaces
-/

theorem mem_nhds_uniformity_iff_right {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α := by
  simp only [nhds_eq_comap_uniformity, mem_comap_prod_mk]
#align mem_nhds_uniformity_iff_right mem_nhds_uniformity_iff_right

theorem mem_nhds_uniformity_iff_left {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ { p : α × α | p.2 = x → p.1 ∈ s } ∈ 𝓤 α := by
  rw [uniformity_eq_symm, mem_nhds_uniformity_iff_right]
  simp only [map_def, mem_map, preimage_setOf_eq, Prod.snd_swap, Prod.fst_swap]
#align mem_nhds_uniformity_iff_left mem_nhds_uniformity_iff_left

theorem nhdsWithin_eq_comap_uniformity_of_mem {x : α} {T : Set α} (hx : x ∈ T) (S : Set α) :
    𝓝[S] x = (𝓤 α ⊓ 𝓟 (T ×ˢ S)).comap (Prod.mk x) := by
  simp [nhdsWithin, nhds_eq_comap_uniformity, hx]

theorem nhdsWithin_eq_comap_uniformity {x : α} (S : Set α) :
    𝓝[S] x = (𝓤 α ⊓ 𝓟 (univ ×ˢ S)).comap (Prod.mk x) :=
  nhdsWithin_eq_comap_uniformity_of_mem (mem_univ _) S

/-- See also `isOpen_iff_open_ball_subset`. -/
theorem isOpen_iff_ball_subset {s : Set α} : IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, ball x V ⊆ s := by
  simp_rw [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap, ball]
#align is_open_iff_ball_subset isOpen_iff_ball_subset

theorem nhds_basis_uniformity' {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => ball x (s i) := by
  rw [nhds_eq_comap_uniformity]
  exact h.comap (Prod.mk x)
#align nhds_basis_uniformity' nhds_basis_uniformity'

theorem nhds_basis_uniformity {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => { y | (y, x) ∈ s i } := by
  replace h := h.comap Prod.swap
  rw [comap_swap_uniformity] at h
  exact nhds_basis_uniformity' h
#align nhds_basis_uniformity nhds_basis_uniformity

theorem nhds_eq_comap_uniformity' {x : α} : 𝓝 x = (𝓤 α).comap fun y => (y, x) :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_of_same_basis <| (𝓤 α).basis_sets.comap _
#align nhds_eq_comap_uniformity' nhds_eq_comap_uniformity'

theorem UniformSpace.mem_nhds_iff {x : α} {s : Set α} : s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, ball x V ⊆ s := by
  rw [nhds_eq_comap_uniformity, mem_comap]
  simp_rw [ball]
#align uniform_space.mem_nhds_iff UniformSpace.mem_nhds_iff

theorem UniformSpace.ball_mem_nhds (x : α) ⦃V : Set (α × α)⦄ (V_in : V ∈ 𝓤 α) : ball x V ∈ 𝓝 x := by
  rw [UniformSpace.mem_nhds_iff]
  exact ⟨V, V_in, Subset.rfl⟩
#align uniform_space.ball_mem_nhds UniformSpace.ball_mem_nhds

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
#align uniform_space.mem_nhds_iff_symm UniformSpace.mem_nhds_iff_symm

theorem UniformSpace.hasBasis_nhds (x : α) :
    HasBasis (𝓝 x) (fun s : Set (α × α) => s ∈ 𝓤 α ∧ SymmetricRel s) fun s => ball x s :=
  ⟨fun t => by simp [UniformSpace.mem_nhds_iff_symm, and_assoc]⟩
#align uniform_space.has_basis_nhds UniformSpace.hasBasis_nhds

open UniformSpace

theorem UniformSpace.mem_closure_iff_symm_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (s ∩ ball x V).Nonempty := by
  simp [mem_closure_iff_nhds_basis (hasBasis_nhds x), Set.Nonempty]
#align uniform_space.mem_closure_iff_symm_ball UniformSpace.mem_closure_iff_symm_ball

theorem UniformSpace.mem_closure_iff_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → (ball x V ∩ s).Nonempty := by
  simp [mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (𝓤 α).basis_sets)]
#align uniform_space.mem_closure_iff_ball UniformSpace.mem_closure_iff_ball

theorem UniformSpace.hasBasis_nhds_prod (x y : α) :
    HasBasis (𝓝 (x, y)) (fun s => s ∈ 𝓤 α ∧ SymmetricRel s) fun s => ball x s ×ˢ ball y s := by
  rw [nhds_prod_eq]
  apply (hasBasis_nhds x).prod_same_index (hasBasis_nhds y)
  rintro U V ⟨U_in, U_symm⟩ ⟨V_in, V_symm⟩
  exact
    ⟨U ∩ V, ⟨(𝓤 α).inter_sets U_in V_in, U_symm.inter V_symm⟩, ball_inter_left x U V,
      ball_inter_right y U V⟩
#align uniform_space.has_basis_nhds_prod UniformSpace.hasBasis_nhds_prod

theorem nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball x) :=
  (nhds_basis_uniformity' (𝓤 α).basis_sets).eq_biInf
#align nhds_eq_uniformity nhds_eq_uniformity

theorem nhds_eq_uniformity' {x : α} : 𝓝 x = (𝓤 α).lift' fun s => { y | (y, x) ∈ s } :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_biInf
#align nhds_eq_uniformity' nhds_eq_uniformity'

theorem mem_nhds_left (x : α) {s : Set (α × α)} (h : s ∈ 𝓤 α) : { y : α | (x, y) ∈ s } ∈ 𝓝 x :=
  ball_mem_nhds x h
#align mem_nhds_left mem_nhds_left

theorem mem_nhds_right (y : α) {s : Set (α × α)} (h : s ∈ 𝓤 α) : { x : α | (x, y) ∈ s } ∈ 𝓝 y :=
  mem_nhds_left _ (symm_le_uniformity h)
#align mem_nhds_right mem_nhds_right

theorem exists_mem_nhds_ball_subset_of_mem_nhds {a : α} {U : Set α} (h : U ∈ 𝓝 a) :
    ∃ V ∈ 𝓝 a, ∃ t ∈ 𝓤 α, ∀ a' ∈ V, UniformSpace.ball a' t ⊆ U :=
  let ⟨t, ht, htU⟩ := comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 h)
  ⟨_, mem_nhds_left a ht, t, ht, fun a₁ h₁ a₂ h₂ => @htU (a, a₂) ⟨a₁, h₁, h₂⟩ rfl⟩
#align exists_mem_nhds_ball_subset_of_mem_nhds exists_mem_nhds_ball_subset_of_mem_nhds

theorem tendsto_right_nhds_uniformity {a : α} : Tendsto (fun a' => (a', a)) (𝓝 a) (𝓤 α) := fun _ =>
  mem_nhds_right a
#align tendsto_right_nhds_uniformity tendsto_right_nhds_uniformity

theorem tendsto_left_nhds_uniformity {a : α} : Tendsto (fun a' => (a, a')) (𝓝 a) (𝓤 α) := fun _ =>
  mem_nhds_left a
#align tendsto_left_nhds_uniformity tendsto_left_nhds_uniformity

theorem lift_nhds_left {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : Set (α × α) => g (ball x s) := by
  rw [nhds_eq_comap_uniformity, comap_lift_eq2 hg]
  simp_rw [ball, Function.comp]
#align lift_nhds_left lift_nhds_left

theorem lift_nhds_right {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : Set (α × α) => g { y | (y, x) ∈ s } := by
  rw [nhds_eq_comap_uniformity', comap_lift_eq2 hg]
  simp_rw [Function.comp, preimage]
#align lift_nhds_right lift_nhds_right

theorem nhds_nhds_eq_uniformity_uniformity_prod {a b : α} :
    𝓝 a ×ˢ 𝓝 b = (𝓤 α).lift fun s : Set (α × α) =>
      (𝓤 α).lift' fun t => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ t } := by
  rw [nhds_eq_uniformity', nhds_eq_uniformity, prod_lift'_lift']
  exacts [rfl, monotone_preimage, monotone_preimage]
#align nhds_nhds_eq_uniformity_uniformity_prod nhds_nhds_eq_uniformity_uniformity_prod

theorem nhds_eq_uniformity_prod {a b : α} :
    𝓝 (a, b) =
      (𝓤 α).lift' fun s : Set (α × α) => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ s } := by
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift']
  · exact fun s => monotone_const.set_prod monotone_preimage
  · refine fun t => Monotone.set_prod ?_ monotone_const
    exact monotone_preimage (f := fun y => (y, a))
#align nhds_eq_uniformity_prod nhds_eq_uniformity_prod

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
#align nhdset_of_mem_uniformity nhdset_of_mem_uniformity

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
#align nhds_le_uniformity nhds_le_uniformity

/-- Entourages are neighborhoods of the diagonal. -/
theorem iSup_nhds_le_uniformity : ⨆ x : α, 𝓝 (x, x) ≤ 𝓤 α :=
  iSup_le nhds_le_uniformity
#align supr_nhds_le_uniformity iSup_nhds_le_uniformity

/-- Entourages are neighborhoods of the diagonal. -/
theorem nhdsSet_diagonal_le_uniformity : 𝓝ˢ (diagonal α) ≤ 𝓤 α :=
  (nhdsSet_diagonal α).trans_le iSup_nhds_le_uniformity
#align nhds_set_diagonal_le_uniformity nhdsSet_diagonal_le_uniformity

/-!
### Closure and interior in uniform spaces
-/

theorem closure_eq_uniformity (s : Set <| α × α) :
    closure s = ⋂ V ∈ { V | V ∈ 𝓤 α ∧ SymmetricRel V }, V ○ s ○ V := by
  ext ⟨x, y⟩
  simp (config := { contextual := true }) only
    [mem_closure_iff_nhds_basis (UniformSpace.hasBasis_nhds_prod x y), mem_iInter, mem_setOf_eq,
      and_imp, mem_comp_comp, exists_prop, ← mem_inter_iff, inter_comm, Set.Nonempty]
#align closure_eq_uniformity closure_eq_uniformity

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
#align uniformity_has_basis_closed uniformity_hasBasis_closed

theorem uniformity_eq_uniformity_closure : 𝓤 α = (𝓤 α).lift' closure :=
  Eq.symm <| uniformity_hasBasis_closed.lift'_closure_eq_self fun _ => And.right
#align uniformity_eq_uniformity_closure uniformity_eq_uniformity_closure

theorem Filter.HasBasis.uniformity_closure {p : ι → Prop} {U : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p U) : (𝓤 α).HasBasis p fun i => closure (U i) :=
  (@uniformity_eq_uniformity_closure α _).symm ▸ h.lift'_closure
#align filter.has_basis.uniformity_closure Filter.HasBasis.uniformity_closure

/-- Closed entourages form a basis of the uniformity filter. -/
theorem uniformity_hasBasis_closure : HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α) closure :=
  (𝓤 α).basis_sets.uniformity_closure
#align uniformity_has_basis_closure uniformity_hasBasis_closure

theorem closure_eq_inter_uniformity {t : Set (α × α)} : closure t = ⋂ d ∈ 𝓤 α, d ○ (t ○ d) :=
  calc
    closure t = ⋂ (V) (_ : V ∈ 𝓤 α ∧ SymmetricRel V), V ○ t ○ V := closure_eq_uniformity t
    _ = ⋂ V ∈ 𝓤 α, V ○ t ○ V :=
      Eq.symm <|
        UniformSpace.hasBasis_symmetric.biInter_mem fun V₁ V₂ hV =>
          compRel_mono (compRel_mono hV Subset.rfl) hV
    _ = ⋂ V ∈ 𝓤 α, V ○ (t ○ V) := by simp only [compRel_assoc]
#align closure_eq_inter_uniformity closure_eq_inter_uniformity

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
    fun s hs => ((𝓤 α).lift' interior).sets_of_superset (mem_lift' hs) interior_subset
#align uniformity_eq_uniformity_interior uniformity_eq_uniformity_interior

theorem interior_mem_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) : interior s ∈ 𝓤 α := by
  rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs
#align interior_mem_uniformity interior_mem_uniformity

theorem mem_uniformity_isClosed {s : Set (α × α)} (h : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, IsClosed t ∧ t ⊆ s :=
  let ⟨t, ⟨ht_mem, htc⟩, hts⟩ := uniformity_hasBasis_closed.mem_iff.1 h
  ⟨t, ht_mem, htc, hts⟩
#align mem_uniformity_is_closed mem_uniformity_isClosed

theorem isOpen_iff_open_ball_subset {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, IsOpen V ∧ ball x V ⊆ s := by
  rw [isOpen_iff_ball_subset]
  constructor <;> intro h x hx
  · obtain ⟨V, hV, hV'⟩ := h x hx
    exact
      ⟨interior V, interior_mem_uniformity hV, isOpen_interior,
        (ball_mono interior_subset x).trans hV'⟩
  · obtain ⟨V, hV, -, hV'⟩ := h x hx
    exact ⟨V, hV, hV'⟩
#align is_open_iff_open_ball_subset isOpen_iff_open_ball_subset

/-- The uniform neighborhoods of all points of a dense set cover the whole space. -/
theorem Dense.biUnion_uniformity_ball {s : Set α} {U : Set (α × α)} (hs : Dense s) (hU : U ∈ 𝓤 α) :
    ⋃ x ∈ s, ball x U = univ := by
  refine iUnion₂_eq_univ_iff.2 fun y => ?_
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with ⟨x, hxs, hxy : (x, y) ∈ U⟩
  exact ⟨x, hxs, hxy⟩
#align dense.bUnion_uniformity_ball Dense.biUnion_uniformity_ball

/-!
### Uniformity bases
-/


/-- Open elements of `𝓤 α` form a basis of `𝓤 α`. -/
theorem uniformity_hasBasis_open : HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α ∧ IsOpen V) id :=
  hasBasis_self.2 fun s hs =>
    ⟨interior s, interior_mem_uniformity hs, isOpen_interior, interior_subset⟩
#align uniformity_has_basis_open uniformity_hasBasis_open

theorem Filter.HasBasis.mem_uniformity_iff {p : β → Prop} {s : β → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {t : Set (α × α)} :
    t ∈ 𝓤 α ↔ ∃ i, p i ∧ ∀ a b, (a, b) ∈ s i → (a, b) ∈ t :=
  h.mem_iff.trans <| by simp only [Prod.forall, subset_def]
#align filter.has_basis.mem_uniformity_iff Filter.HasBasis.mem_uniformity_iff

/-- Open elements `s : Set (α × α)` of `𝓤 α` such that `(x, y) ∈ s ↔ (y, x) ∈ s` form a basis
of `𝓤 α`. -/
theorem uniformity_hasBasis_open_symmetric :
    HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α ∧ IsOpen V ∧ SymmetricRel V) id := by
  simp only [← and_assoc]
  refine uniformity_hasBasis_open.restrict fun s hs => ⟨symmetrizeRel s, ?_⟩
  exact
    ⟨⟨symmetrize_mem_uniformity hs.1, IsOpen.inter hs.2 (hs.2.preimage continuous_swap)⟩,
      symmetric_symmetrizeRel s, symmetrizeRel_subset_self s⟩
#align uniformity_has_basis_open_symmetric uniformity_hasBasis_open_symmetric

theorem comp_open_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, IsOpen t ∧ SymmetricRel t ∧ t ○ t ⊆ s := by
  obtain ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hu₄ : u ⊆ t⟩ := uniformity_hasBasis_open_symmetric.mem_iff.mp ht₁
  exact ⟨u, hu₁, hu₂, hu₃, (compRel_mono hu₄ hu₄).trans ht₂⟩
#align comp_open_symm_mem_uniformity_sets comp_open_symm_mem_uniformity_sets

section

variable (α)

theorem UniformSpace.has_seq_basis [IsCountablyGenerated <| 𝓤 α] :
    ∃ V : ℕ → Set (α × α), HasAntitoneBasis (𝓤 α) V ∧ ∀ n, SymmetricRel (V n) :=
  let ⟨U, hsym, hbasis⟩ := (@UniformSpace.hasBasis_symmetric α _).exists_antitone_subbasis
  ⟨U, hbasis, fun n => (hsym n).2⟩
#align uniform_space.has_seq_basis UniformSpace.has_seq_basis

end

theorem Filter.HasBasis.biInter_biUnion_ball {p : ι → Prop} {U : ι → Set (α × α)}
    (h : HasBasis (𝓤 α) p U) (s : Set α) :
    (⋂ (i) (_ : p i), ⋃ x ∈ s, ball x (U i)) = closure s := by
  ext x
  simp [mem_closure_iff_nhds_basis (nhds_basis_uniformity h), ball]
#align filter.has_basis.bInter_bUnion_ball Filter.HasBasis.biInter_biUnion_ball

/-! ### Uniform continuity -/


/-- A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `α`. -/
def UniformContinuous [UniformSpace β] (f : α → β) :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α) (𝓤 β)
#align uniform_continuous UniformContinuous

/-- Notation for uniform continuity with respect to non-standard `UniformSpace` instances. -/
scoped[Uniformity] notation "UniformContinuous[" u₁ ", " u₂ "]" => @UniformContinuous _ _ u₁ u₂

/-- A function `f : α → β` is *uniformly continuous* on `s : Set α` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s ×ˢ s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`. -/
def UniformContinuousOn [UniformSpace β] (f : α → β) (s : Set α) : Prop :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 β)
#align uniform_continuous_on UniformContinuousOn

theorem uniformContinuous_def [UniformSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, { x : α × α | (f x.1, f x.2) ∈ r } ∈ 𝓤 α :=
  Iff.rfl
#align uniform_continuous_def uniformContinuous_def

theorem uniformContinuous_iff_eventually [UniformSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, ∀ᶠ x : α × α in 𝓤 α, (f x.1, f x.2) ∈ r :=
  Iff.rfl
#align uniform_continuous_iff_eventually uniformContinuous_iff_eventually

theorem uniformContinuousOn_univ [UniformSpace β] {f : α → β} :
    UniformContinuousOn f univ ↔ UniformContinuous f := by
  rw [UniformContinuousOn, UniformContinuous, univ_prod_univ, principal_univ, inf_top_eq]
#align uniform_continuous_on_univ uniformContinuousOn_univ

theorem uniformContinuous_of_const [UniformSpace β] {c : α → β} (h : ∀ a b, c a = c b) :
    UniformContinuous c :=
  have : (fun x : α × α => (c x.fst, c x.snd)) ⁻¹' idRel = univ :=
    eq_univ_iff_forall.2 fun ⟨a, b⟩ => h a b
  le_trans (map_le_iff_le_comap.2 <| by simp [comap_principal, this, univ_mem]) refl_le_uniformity
#align uniform_continuous_of_const uniformContinuous_of_const

theorem uniformContinuous_id : UniformContinuous (@id α) := tendsto_id
#align uniform_continuous_id uniformContinuous_id

theorem uniformContinuous_const [UniformSpace β] {b : β} : UniformContinuous fun _ : α => b :=
  uniformContinuous_of_const fun _ _ => rfl
#align uniform_continuous_const uniformContinuous_const

nonrec theorem UniformContinuous.comp [UniformSpace β] [UniformSpace γ] {g : β → γ} {f : α → β}
    (hg : UniformContinuous g) (hf : UniformContinuous f) : UniformContinuous (g ∘ f) :=
  hg.comp hf
#align uniform_continuous.comp UniformContinuous.comp

theorem Filter.HasBasis.uniformContinuous_iff {ι'} [UniformSpace β] {p : ι → Prop}
    {s : ι → Set (α × α)} (ha : (𝓤 α).HasBasis p s) {q : ι' → Prop} {t : ι' → Set (β × β)}
    (hb : (𝓤 β).HasBasis q t) {f : α → β} :
    UniformContinuous f ↔ ∀ i, q i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ t i :=
  (ha.tendsto_iff hb).trans <| by simp only [Prod.forall]
#align filter.has_basis.uniform_continuous_iff Filter.HasBasis.uniformContinuous_iff

theorem Filter.HasBasis.uniformContinuousOn_iff {ι'} [UniformSpace β] {p : ι → Prop}
    {s : ι → Set (α × α)} (ha : (𝓤 α).HasBasis p s) {q : ι' → Prop} {t : ι' → Set (β × β)}
    (hb : (𝓤 β).HasBasis q t) {f : α → β} {S : Set α} :
    UniformContinuousOn f S ↔
      ∀ i, q i → ∃ j, p j ∧ ∀ x, x ∈ S → ∀ y, y ∈ S → (x, y) ∈ s j → (f x, f y) ∈ t i :=
  ((ha.inf_principal (S ×ˢ S)).tendsto_iff hb).trans <| by
    simp_rw [Prod.forall, Set.inter_comm (s _), forall_mem_comm, mem_inter_iff, mem_prod, and_imp]
#align filter.has_basis.uniform_continuous_on_iff Filter.HasBasis.uniformContinuousOn_iff

end UniformSpace

open uniformity

section Constructions

instance : PartialOrder (UniformSpace α) :=
  PartialOrder.lift (fun u => 𝓤[u]) fun _ _ => UniformSpace.ext

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

set_option linter.deprecated false in
-- TODO update this code to avoid the deprecation
instance : Top (UniformSpace α) :=
  ⟨.ofNhdsEqComap ⟨⊤, le_top, le_top, le_top⟩ ⊤ fun x ↦ by simp only [nhds_top, comap_top]⟩

instance : Bot (UniformSpace α) :=
  ⟨{  toTopologicalSpace := ⊥
      uniformity := 𝓟 idRel
      symm := by simp [Tendsto]
      comp := lift'_le (mem_principal_self _) <| principal_mono.2 id_compRel.subset
      nhds_eq_comap_uniformity := fun s => by
        let _ : TopologicalSpace α := ⊥; have := discreteTopology_bot α
        simp [idRel] }⟩

instance : Inf (UniformSpace α) :=
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
#align infi_uniformity iInf_uniformity

theorem inf_uniformity {u v : UniformSpace α} : 𝓤[u ⊓ v] = 𝓤[u] ⊓ 𝓤[v] := rfl
#align inf_uniformity inf_uniformity

lemma bot_uniformity : 𝓤[(⊥ : UniformSpace α)] = 𝓟 idRel := rfl

lemma top_uniformity : 𝓤[(⊤ : UniformSpace α)] = ⊤ := rfl

instance inhabitedUniformSpace : Inhabited (UniformSpace α) :=
  ⟨⊥⟩
#align inhabited_uniform_space inhabitedUniformSpace

instance inhabitedUniformSpaceCore : Inhabited (UniformSpace.Core α) :=
  ⟨@UniformSpace.toCore _ default⟩
#align inhabited_uniform_space_core inhabitedUniformSpaceCore

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
    simp only [nhds_induced, nhds_eq_comap_uniformity, comap_comap, Function.comp]
#align uniform_space.comap UniformSpace.comap

theorem uniformity_comap {_ : UniformSpace β} (f : α → β) :
    𝓤[UniformSpace.comap f ‹_›] = comap (Prod.map f f) (𝓤 β) :=
  rfl
#align uniformity_comap uniformity_comap

@[simp]
theorem uniformSpace_comap_id {α : Type*} : UniformSpace.comap (id : α → α) = id := by
  ext : 2
  rw [uniformity_comap, Prod.map_id, comap_id]
#align uniform_space_comap_id uniformSpace_comap_id

theorem UniformSpace.comap_comap {α β γ} {uγ : UniformSpace γ} {f : α → β} {g : β → γ} :
    UniformSpace.comap (g ∘ f) uγ = UniformSpace.comap f (UniformSpace.comap g uγ) := by
  ext1
  simp only [uniformity_comap, Filter.comap_comap, Prod.map_comp_map]
#align uniform_space.comap_comap UniformSpace.comap_comap

theorem UniformSpace.comap_inf {α γ} {u₁ u₂ : UniformSpace γ} {f : α → γ} :
    (u₁ ⊓ u₂).comap f = u₁.comap f ⊓ u₂.comap f :=
  UniformSpace.ext Filter.comap_inf
#align uniform_space.comap_inf UniformSpace.comap_inf

theorem UniformSpace.comap_iInf {ι α γ} {u : ι → UniformSpace γ} {f : α → γ} :
    (⨅ i, u i).comap f = ⨅ i, (u i).comap f := by
  ext : 1
  simp [uniformity_comap, iInf_uniformity]
#align uniform_space.comap_infi UniformSpace.comap_iInf

theorem UniformSpace.comap_mono {α γ} {f : α → γ} :
    Monotone fun u : UniformSpace γ => u.comap f := fun _ _ hu =>
  Filter.comap_mono hu
#align uniform_space.comap_mono UniformSpace.comap_mono

theorem uniformContinuous_iff {α β} {uα : UniformSpace α} {uβ : UniformSpace β} {f : α → β} :
    UniformContinuous f ↔ uα ≤ uβ.comap f :=
  Filter.map_le_iff_le_comap
#align uniform_continuous_iff uniformContinuous_iff

theorem le_iff_uniformContinuous_id {u v : UniformSpace α} :
    u ≤ v ↔ @UniformContinuous _ _ u v id := by
  rw [uniformContinuous_iff, uniformSpace_comap_id, id]
#align le_iff_uniform_continuous_id le_iff_uniformContinuous_id

theorem uniformContinuous_comap {f : α → β} [u : UniformSpace β] :
    @UniformContinuous α β (UniformSpace.comap f u) u f :=
  tendsto_comap
#align uniform_continuous_comap uniformContinuous_comap

theorem uniformContinuous_comap' {f : γ → β} {g : α → γ} [v : UniformSpace β] [u : UniformSpace α]
    (h : UniformContinuous (f ∘ g)) : @UniformContinuous α γ u (UniformSpace.comap f v) g :=
  tendsto_comap_iff.2 h
#align uniform_continuous_comap' uniformContinuous_comap'

namespace UniformSpace

theorem to_nhds_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) (a : α) :
    @nhds _ (@UniformSpace.toTopologicalSpace _ u₁) a ≤
      @nhds _ (@UniformSpace.toTopologicalSpace _ u₂) a := by
  rw [@nhds_eq_uniformity α u₁ a, @nhds_eq_uniformity α u₂ a]; exact lift'_mono h le_rfl
#align to_nhds_mono UniformSpace.to_nhds_mono

theorem toTopologicalSpace_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) :
    @UniformSpace.toTopologicalSpace _ u₁ ≤ @UniformSpace.toTopologicalSpace _ u₂ :=
  le_of_nhds_le_nhds <| to_nhds_mono h
#align to_topological_space_mono UniformSpace.toTopologicalSpace_mono

theorem toTopologicalSpace_comap {f : α → β} {u : UniformSpace β} :
    @UniformSpace.toTopologicalSpace _ (UniformSpace.comap f u) =
      TopologicalSpace.induced f (@UniformSpace.toTopologicalSpace β u) :=
  rfl
#align to_topological_space_comap UniformSpace.toTopologicalSpace_comap

theorem toTopologicalSpace_bot : @UniformSpace.toTopologicalSpace α ⊥ = ⊥ := rfl
#align to_topological_space_bot UniformSpace.toTopologicalSpace_bot

theorem toTopologicalSpace_top : @UniformSpace.toTopologicalSpace α ⊤ = ⊤ := rfl
#align to_topological_space_top UniformSpace.toTopologicalSpace_top

theorem toTopologicalSpace_iInf {ι : Sort*} {u : ι → UniformSpace α} :
    (iInf u).toTopologicalSpace = ⨅ i, (u i).toTopologicalSpace :=
  TopologicalSpace.ext_nhds fun a ↦ by simp only [@nhds_eq_comap_uniformity _ (iInf u), nhds_iInf,
    iInf_uniformity, @nhds_eq_comap_uniformity _ (u _), Filter.comap_iInf]
#align to_topological_space_infi UniformSpace.toTopologicalSpace_iInf

theorem toTopologicalSpace_sInf {s : Set (UniformSpace α)} :
    (sInf s).toTopologicalSpace = ⨅ i ∈ s, @UniformSpace.toTopologicalSpace α i := by
  rw [sInf_eq_iInf]
  simp only [← toTopologicalSpace_iInf]
#align to_topological_space_Inf UniformSpace.toTopologicalSpace_sInf

theorem toTopologicalSpace_inf {u v : UniformSpace α} :
    (u ⊓ v).toTopologicalSpace = u.toTopologicalSpace ⊓ v.toTopologicalSpace :=
  rfl
#align to_topological_space_inf UniformSpace.toTopologicalSpace_inf

end UniformSpace

theorem UniformContinuous.continuous [UniformSpace α] [UniformSpace β] {f : α → β}
    (hf : UniformContinuous f) : Continuous f :=
  continuous_iff_le_induced.mpr <| UniformSpace.toTopologicalSpace_mono <|
    uniformContinuous_iff.1 hf
#align uniform_continuous.continuous UniformContinuous.continuous

/-- Uniform space structure on `ULift α`. -/
instance ULift.uniformSpace [UniformSpace α] : UniformSpace (ULift α) :=
  UniformSpace.comap ULift.down ‹_›
#align ulift.uniform_space ULift.uniformSpace

section UniformContinuousInfi

-- Porting note: renamed for dot notation; add an `iff` lemma?
theorem UniformContinuous.inf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ u₃ : UniformSpace β}
    (h₁ : UniformContinuous[u₁, u₂] f) (h₂ : UniformContinuous[u₁, u₃] f) :
    UniformContinuous[u₁, u₂ ⊓ u₃] f :=
  tendsto_inf.mpr ⟨h₁, h₂⟩
#align uniform_continuous_inf_rng UniformContinuous.inf_rng

-- Porting note: renamed for dot notation
theorem UniformContinuous.inf_dom_left {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : UniformContinuous[u₁, u₃] f) : UniformContinuous[u₁ ⊓ u₂, u₃] f :=
  tendsto_inf_left hf
#align uniform_continuous_inf_dom_left UniformContinuous.inf_dom_left

-- Porting note: renamed for dot notation
theorem UniformContinuous.inf_dom_right {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : UniformContinuous[u₂, u₃] f) : UniformContinuous[u₁ ⊓ u₂, u₃] f :=
  tendsto_inf_right hf
#align uniform_continuous_inf_dom_right UniformContinuous.inf_dom_right

theorem uniformContinuous_sInf_dom {f : α → β} {u₁ : Set (UniformSpace α)} {u₂ : UniformSpace β}
    {u : UniformSpace α} (h₁ : u ∈ u₁) (hf : UniformContinuous[u, u₂] f) :
    UniformContinuous[sInf u₁, u₂] f := by
  delta UniformContinuous
  rw [sInf_eq_iInf', iInf_uniformity]
  exact tendsto_iInf' ⟨u, h₁⟩ hf
#align uniform_continuous_Inf_dom uniformContinuous_sInf_dom

theorem uniformContinuous_sInf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : Set (UniformSpace β)} :
    UniformContinuous[u₁, sInf u₂] f ↔ ∀ u ∈ u₂, UniformContinuous[u₁, u] f := by
  delta UniformContinuous
  rw [sInf_eq_iInf', iInf_uniformity, tendsto_iInf, SetCoe.forall]
#align uniform_continuous_Inf_rng uniformContinuous_sInf_rng

theorem uniformContinuous_iInf_dom {f : α → β} {u₁ : ι → UniformSpace α} {u₂ : UniformSpace β}
    {i : ι} (hf : UniformContinuous[u₁ i, u₂] f) : UniformContinuous[iInf u₁, u₂] f := by
  delta UniformContinuous
  rw [iInf_uniformity]
  exact tendsto_iInf' i hf
#align uniform_continuous_infi_dom uniformContinuous_iInf_dom

theorem uniformContinuous_iInf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : ι → UniformSpace β} :
    UniformContinuous[u₁, iInf u₂] f ↔ ∀ i, UniformContinuous[u₁, u₂ i] f := by
  delta UniformContinuous
  rw [iInf_uniformity, tendsto_iInf]
#align uniform_continuous_infi_rng uniformContinuous_iInf_rng

end UniformContinuousInfi

/-- A uniform space with the discrete uniformity has the discrete topology. -/
theorem discreteTopology_of_discrete_uniformity [hα : UniformSpace α] (h : uniformity α = 𝓟 idRel) :
    DiscreteTopology α :=
  ⟨(UniformSpace.ext h.symm : ⊥ = hα) ▸ rfl⟩
#align discrete_topology_of_discrete_uniformity discreteTopology_of_discrete_uniformity

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
#align uniform_continuous_of_mul uniformContinuous_ofMul

theorem uniformContinuous_toMul : UniformContinuous (toMul : Additive α → α) :=
  uniformContinuous_id
#align uniform_continuous_to_mul uniformContinuous_toMul

theorem uniformContinuous_ofAdd : UniformContinuous (ofAdd : α → Multiplicative α) :=
  uniformContinuous_id
#align uniform_continuous_of_add uniformContinuous_ofAdd

theorem uniformContinuous_toAdd : UniformContinuous (toAdd : Multiplicative α → α) :=
  uniformContinuous_id
#align uniform_continuous_to_add uniformContinuous_toAdd

theorem uniformity_additive : 𝓤 (Additive α) = (𝓤 α).map (Prod.map ofMul ofMul) := rfl
#align uniformity_additive uniformity_additive

theorem uniformity_multiplicative : 𝓤 (Multiplicative α) = (𝓤 α).map (Prod.map ofAdd ofAdd) := rfl
#align uniformity_multiplicative uniformity_multiplicative

end

instance instUniformSpaceSubtype {p : α → Prop} [t : UniformSpace α] : UniformSpace (Subtype p) :=
  UniformSpace.comap Subtype.val t

theorem uniformity_subtype {p : α → Prop} [UniformSpace α] :
    𝓤 (Subtype p) = comap (fun q : Subtype p × Subtype p => (q.1.1, q.2.1)) (𝓤 α) :=
  rfl
#align uniformity_subtype uniformity_subtype

theorem uniformity_setCoe {s : Set α} [UniformSpace α] :
    𝓤 s = comap (Prod.map ((↑) : s → α) ((↑) : s → α)) (𝓤 α) :=
  rfl
#align uniformity_set_coe uniformity_setCoe

-- Porting note (#10756): new lemma
theorem map_uniformity_set_coe {s : Set α} [UniformSpace α] :
    map (Prod.map (↑) (↑)) (𝓤 s) = 𝓤 α ⊓ 𝓟 (s ×ˢ s) := by
  rw [uniformity_setCoe, map_comap, range_prod_map, Subtype.range_val]

theorem uniformContinuous_subtype_val {p : α → Prop} [UniformSpace α] :
    UniformContinuous (Subtype.val : { a : α // p a } → α) :=
  uniformContinuous_comap
#align uniform_continuous_subtype_val uniformContinuous_subtype_val
#align uniform_continuous_subtype_coe uniformContinuous_subtype_val

theorem UniformContinuous.subtype_mk {p : α → Prop} [UniformSpace α] [UniformSpace β] {f : β → α}
    (hf : UniformContinuous f) (h : ∀ x, p (f x)) :
    UniformContinuous (fun x => ⟨f x, h x⟩ : β → Subtype p) :=
  uniformContinuous_comap' hf
#align uniform_continuous.subtype_mk UniformContinuous.subtype_mk

theorem uniformContinuousOn_iff_restrict [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔ UniformContinuous (s.restrict f) := by
  delta UniformContinuousOn UniformContinuous
  rw [← map_uniformity_set_coe, tendsto_map'_iff]; rfl
#align uniform_continuous_on_iff_restrict uniformContinuousOn_iff_restrict

theorem tendsto_of_uniformContinuous_subtype [UniformSpace α] [UniformSpace β] {f : α → β}
    {s : Set α} {a : α} (hf : UniformContinuous fun x : s => f x.val) (ha : s ∈ 𝓝 a) :
    Tendsto f (𝓝 a) (𝓝 (f a)) := by
  rw [(@map_nhds_subtype_coe_eq_nhds α _ s a (mem_of_mem_nhds ha) ha).symm]
  exact tendsto_map' hf.continuous.continuousAt
#align tendsto_of_uniform_continuous_subtype tendsto_of_uniformContinuous_subtype

theorem UniformContinuousOn.continuousOn [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α}
    (h : UniformContinuousOn f s) : ContinuousOn f s := by
  rw [uniformContinuousOn_iff_restrict] at h
  rw [continuousOn_iff_continuous_restrict]
  exact h.continuous
#align uniform_continuous_on.continuous_on UniformContinuousOn.continuousOn

@[to_additive]
instance [UniformSpace α] : UniformSpace αᵐᵒᵖ :=
  UniformSpace.comap MulOpposite.unop ‹_›

@[to_additive]
theorem uniformity_mulOpposite [UniformSpace α] :
    𝓤 αᵐᵒᵖ = comap (fun q : αᵐᵒᵖ × αᵐᵒᵖ => (q.1.unop, q.2.unop)) (𝓤 α) :=
  rfl
#align uniformity_mul_opposite uniformity_mulOpposite
#align uniformity_add_opposite uniformity_addOpposite

@[to_additive (attr := simp)]
theorem comap_uniformity_mulOpposite [UniformSpace α] :
    comap (fun p : α × α => (MulOpposite.op p.1, MulOpposite.op p.2)) (𝓤 αᵐᵒᵖ) = 𝓤 α := by
  simpa [uniformity_mulOpposite, comap_comap, (· ∘ ·)] using comap_id
#align comap_uniformity_mul_opposite comap_uniformity_mulOpposite
#align comap_uniformity_add_opposite comap_uniformity_addOpposite

namespace MulOpposite

@[to_additive]
theorem uniformContinuous_unop [UniformSpace α] : UniformContinuous (unop : αᵐᵒᵖ → α) :=
  uniformContinuous_comap
#align mul_opposite.uniform_continuous_unop MulOpposite.uniformContinuous_unop
#align add_opposite.uniform_continuous_unop AddOpposite.uniformContinuous_unop

@[to_additive]
theorem uniformContinuous_op [UniformSpace α] : UniformContinuous (op : α → αᵐᵒᵖ) :=
  uniformContinuous_comap' uniformContinuous_id
#align mul_opposite.uniform_continuous_op MulOpposite.uniformContinuous_op
#align add_opposite.uniform_continuous_op AddOpposite.uniformContinuous_op

end MulOpposite

section Prod

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
#align uniformity_prod uniformity_prod

instance [UniformSpace α] [IsCountablyGenerated (𝓤 α)]
    [UniformSpace β] [IsCountablyGenerated (𝓤 β)] : IsCountablyGenerated (𝓤 (α × β)) := by
  rw [uniformity_prod]
  infer_instance

theorem uniformity_prod_eq_comap_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) =
      comap (fun p : (α × β) × α × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 𝓤 β) := by
  dsimp [SProd.sprod]
  rw [uniformity_prod, Filter.prod, comap_inf, comap_comap, comap_comap]; rfl
#align uniformity_prod_eq_comap_prod uniformity_prod_eq_comap_prod

theorem uniformity_prod_eq_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 𝓤 β) := by
  rw [map_swap4_eq_comap, uniformity_prod_eq_comap_prod]
#align uniformity_prod_eq_prod uniformity_prod_eq_prod

theorem mem_uniformity_of_uniformContinuous_invariant [UniformSpace α] [UniformSpace β]
    {s : Set (β × β)} {f : α → α → β} (hf : UniformContinuous fun p : α × α => f p.1 p.2)
    (hs : s ∈ 𝓤 β) : ∃ u ∈ 𝓤 α, ∀ a b c, (a, b) ∈ u → (f a c, f b c) ∈ s := by
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff] at hf
  rcases mem_prod_iff.1 (mem_map.1 <| hf hs) with ⟨u, hu, v, hv, huvt⟩
  exact ⟨u, hu, fun a b c hab => @huvt ((_, _), (_, _)) ⟨hab, refl_mem_uniformity hv⟩⟩
#align mem_uniformity_of_uniform_continuous_invariant mem_uniformity_of_uniformContinuous_invariant

theorem mem_uniform_prod [t₁ : UniformSpace α] [t₂ : UniformSpace β] {a : Set (α × α)}
    {b : Set (β × β)} (ha : a ∈ 𝓤 α) (hb : b ∈ 𝓤 β) :
    { p : (α × β) × α × β | (p.1.1, p.2.1) ∈ a ∧ (p.1.2, p.2.2) ∈ b } ∈ 𝓤 (α × β) := by
  rw [uniformity_prod]; exact inter_mem_inf (preimage_mem_comap ha) (preimage_mem_comap hb)
#align mem_uniform_prod mem_uniform_prod

theorem tendsto_prod_uniformity_fst [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.1, p.2.1)) (𝓤 (α × β)) (𝓤 α) :=
  le_trans (map_mono inf_le_left) map_comap_le
#align tendsto_prod_uniformity_fst tendsto_prod_uniformity_fst

theorem tendsto_prod_uniformity_snd [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.2, p.2.2)) (𝓤 (α × β)) (𝓤 β) :=
  le_trans (map_mono inf_le_right) map_comap_le
#align tendsto_prod_uniformity_snd tendsto_prod_uniformity_snd

theorem uniformContinuous_fst [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.1 :=
  tendsto_prod_uniformity_fst
#align uniform_continuous_fst uniformContinuous_fst

theorem uniformContinuous_snd [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.2 :=
  tendsto_prod_uniformity_snd
#align uniform_continuous_snd uniformContinuous_snd

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

theorem UniformContinuous.prod_mk {f₁ : α → β} {f₂ : α → γ} (h₁ : UniformContinuous f₁)
    (h₂ : UniformContinuous f₂) : UniformContinuous fun a => (f₁ a, f₂ a) := by
  rw [UniformContinuous, uniformity_prod]
  exact tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩
#align uniform_continuous.prod_mk UniformContinuous.prod_mk

theorem UniformContinuous.prod_mk_left {f : α × β → γ} (h : UniformContinuous f) (b) :
    UniformContinuous fun a => f (a, b) :=
  h.comp (uniformContinuous_id.prod_mk uniformContinuous_const)
#align uniform_continuous.prod_mk_left UniformContinuous.prod_mk_left

theorem UniformContinuous.prod_mk_right {f : α × β → γ} (h : UniformContinuous f) (a) :
    UniformContinuous fun b => f (a, b) :=
  h.comp (uniformContinuous_const.prod_mk uniformContinuous_id)
#align uniform_continuous.prod_mk_right UniformContinuous.prod_mk_right

theorem UniformContinuous.prod_map [UniformSpace δ] {f : α → γ} {g : β → δ}
    (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformContinuous (Prod.map f g) :=
  (hf.comp uniformContinuous_fst).prod_mk (hg.comp uniformContinuous_snd)
#align uniform_continuous.prod_map UniformContinuous.prod_map

theorem toTopologicalSpace_prod {α} {β} [u : UniformSpace α] [v : UniformSpace β] :
    @UniformSpace.toTopologicalSpace (α × β) instUniformSpaceProd =
      @instTopologicalSpaceProd α β u.toTopologicalSpace v.toTopologicalSpace :=
  rfl
#align to_topological_space_prod toTopologicalSpace_prod

/-- A version of `UniformContinuous.inf_dom_left` for binary functions -/
theorem uniformContinuous_inf_dom_left₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua1; haveI := ub1; exact UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2;
        exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_left₂`
  have ha := @UniformContinuous.inf_dom_left _ _ id ua1 ua2 ua1 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_left _ _ id ub1 ub2 ub1 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prod_map _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua1 ub1 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id
#align uniform_continuous_inf_dom_left₂ uniformContinuous_inf_dom_left₂

/-- A version of `UniformContinuous.inf_dom_right` for binary functions -/
theorem uniformContinuous_inf_dom_right₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua2; haveI := ub2; exact UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2;
        exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_right₂`
  have ha := @UniformContinuous.inf_dom_right _ _ id ua1 ua2 ua2 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_right _ _ id ub1 ub2 ub2 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prod_map _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua2 ub2 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id
#align uniform_continuous_inf_dom_right₂ uniformContinuous_inf_dom_right₂

/-- A version of `uniformContinuous_sInf_dom` for binary functions -/
theorem uniformContinuous_sInf_dom₂ {α β γ} {f : α → β → γ} {uas : Set (UniformSpace α)}
    {ubs : Set (UniformSpace β)} {ua : UniformSpace α} {ub : UniformSpace β} {uc : UniformSpace γ}
    (ha : ua ∈ uas) (hb : ub ∈ ubs) (hf : UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := sInf uas; haveI := sInf ubs;
        exact @UniformContinuous _ _ _ uc fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_sInf_dom`
  let _ : UniformSpace (α × β) := instUniformSpaceProd
  have ha := uniformContinuous_sInf_dom ha uniformContinuous_id
  have hb := uniformContinuous_sInf_dom hb uniformContinuous_id
  have h_unif_cont_id := @UniformContinuous.prod_map _ _ _ _ (sInf uas) (sInf ubs) ua ub _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ hf h_unif_cont_id
#align uniform_continuous_Inf_dom₂ uniformContinuous_sInf_dom₂

end Prod

section

open UniformSpace Function

variable {δ' : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]
  [UniformSpace δ']
local notation f " ∘₂ " g => Function.bicompr f g

/-- Uniform continuity for functions of two variables. -/
def UniformContinuous₂ (f : α → β → γ) :=
  UniformContinuous (uncurry f)
#align uniform_continuous₂ UniformContinuous₂

theorem uniformContinuous₂_def (f : α → β → γ) :
    UniformContinuous₂ f ↔ UniformContinuous (uncurry f) :=
  Iff.rfl
#align uniform_continuous₂_def uniformContinuous₂_def

theorem UniformContinuous₂.uniformContinuous {f : α → β → γ} (h : UniformContinuous₂ f) :
    UniformContinuous (uncurry f) :=
  h
#align uniform_continuous₂.uniform_continuous UniformContinuous₂.uniformContinuous

theorem uniformContinuous₂_curry (f : α × β → γ) :
    UniformContinuous₂ (Function.curry f) ↔ UniformContinuous f := by
  rw [UniformContinuous₂, uncurry_curry]
#align uniform_continuous₂_curry uniformContinuous₂_curry

theorem UniformContinuous₂.comp {f : α → β → γ} {g : γ → δ} (hg : UniformContinuous g)
    (hf : UniformContinuous₂ f) : UniformContinuous₂ (g ∘₂ f) :=
  hg.comp hf
#align uniform_continuous₂.comp UniformContinuous₂.comp

theorem UniformContinuous₂.bicompl {f : α → β → γ} {ga : δ → α} {gb : δ' → β}
    (hf : UniformContinuous₂ f) (hga : UniformContinuous ga) (hgb : UniformContinuous gb) :
    UniformContinuous₂ (bicompl f ga gb) :=
  hf.uniformContinuous.comp (hga.prod_map hgb)
#align uniform_continuous₂.bicompl UniformContinuous₂.bicompl

end

theorem toTopologicalSpace_subtype [u : UniformSpace α] {p : α → Prop} :
    @UniformSpace.toTopologicalSpace (Subtype p) instUniformSpaceSubtype =
      @instTopologicalSpaceSubtype α p u.toTopologicalSpace :=
  rfl
#align to_topological_space_subtype toTopologicalSpace_subtype

section Sum

variable [UniformSpace α] [UniformSpace β]

open Sum

-- Obsolete auxiliary definitions and lemmas
#noalign uniform_space.core.sum
#noalign uniformity_sum_of_open_aux
#noalign open_of_uniformity_sum_aux

/-- Uniformity on a disjoint union. Entourages of the diagonal in the union are obtained
by taking independently an entourage of the diagonal in the first part, and an entourage of
the diagonal in the second part. -/
instance Sum.instUniformSpace : UniformSpace (α ⊕ β) where
  uniformity := map (fun p : α × α => (inl p.1, inl p.2)) (𝓤 α) ⊔
    map (fun p : β × β => (inr p.1, inr p.2)) (𝓤 β)
  symm := fun s hs ↦ ⟨symm_le_uniformity hs.1, symm_le_uniformity hs.2⟩
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
#align sum.uniform_space Sum.instUniformSpace

@[reducible, deprecated] alias Sum.uniformSpace := Sum.instUniformSpace -- 2024-02-15

/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage
of the diagonal. -/
theorem union_mem_uniformity_sum {a : Set (α × α)} (ha : a ∈ 𝓤 α) {b : Set (β × β)} (hb : b ∈ 𝓤 β) :
    Prod.map inl inl '' a ∪ Prod.map inr inr '' b ∈ 𝓤 (α ⊕ β) :=
  union_mem_sup (image_mem_map ha) (image_mem_map hb)
#align union_mem_uniformity_sum union_mem_uniformity_sum

theorem Sum.uniformity : 𝓤 (α ⊕ β) = map (Prod.map inl inl) (𝓤 α) ⊔ map (Prod.map inr inr) (𝓤 β) :=
  rfl
#align sum.uniformity Sum.uniformity

lemma uniformContinuous_inl : UniformContinuous (Sum.inl : α → α ⊕ β) := le_sup_left
lemma uniformContinuous_inr : UniformContinuous (Sum.inr : β → α ⊕ β) := le_sup_right

instance [IsCountablyGenerated (𝓤 α)] [IsCountablyGenerated (𝓤 β)] :
    IsCountablyGenerated (𝓤 (α ⊕ β)) := by
  rw [Sum.uniformity]
  infer_instance

end Sum

end Constructions

/-!
### Compact sets in uniform spaces
-/

section Compact

open UniformSpace
variable [UniformSpace α] {K : Set α}

/-- Let `c : ι → Set α` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `c i`. -/
theorem lebesgue_number_lemma {ι : Sort*} {U : ι → Set α} (hK : IsCompact K)
    (hopen : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ i, ball x V ⊆ U i := by
  have : ∀ x ∈ K, ∃ i, ∃ V ∈ 𝓤 α, ball x (V ○ V) ⊆ U i := fun x hx ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover hx)
    rw [← (hopen i).mem_nhds_iff, nhds_eq_comap_uniformity, ← lift'_comp_uniformity] at hi
    exact ⟨i, (((basis_sets _).lift' <| monotone_id.compRel monotone_id).comap _).mem_iff.1 hi⟩
  choose ind W hW hWU using this
  rcases hK.elim_nhds_subcover' (fun x hx ↦ ball x (W x hx)) (fun x hx ↦ ball_mem_nhds _ (hW x hx))
    with ⟨t, ht⟩
  refine ⟨⋂ x ∈ t, W x x.2, (biInter_finset_mem _).2 fun x _ ↦ hW x x.2, fun x hx ↦ ?_⟩
  rcases mem_iUnion₂.1 (ht hx) with ⟨y, hyt, hxy⟩
  exact ⟨ind y y.2, fun z hz ↦ hWU _ _ ⟨x, hxy, mem_iInter₂.1 hz _ hyt⟩⟩
#align lebesgue_number_lemma lebesgue_number_lemma

/-- Let `U : ι → Set α` be an open cover of a compact set `K`.
Then there exists an entourage `V`
such that for each `x ∈ K` its `V`-neighborhood is included in some `U i`.

Moreover, one can choose an entourage from a given basis. -/
protected theorem Filter.HasBasis.lebesgue_number_lemma {ι' ι : Sort*} {p : ι' → Prop}
    {V : ι' → Set (α × α)} {U : ι → Set α} (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K)
    (hopen : ∀ j, IsOpen (U j)) (hcover : K ⊆ ⋃ j, U j) :
    ∃ i, p i ∧ ∀ x ∈ K, ∃ j, ball x (V i) ⊆ U j := by
  refine (hbasis.exists_iff ?_).1 (lebesgue_number_lemma hK hopen hcover)
  exact fun s t hst ht x hx ↦ (ht x hx).imp fun i hi ↦ Subset.trans (ball_mono hst _) hi

/-- Let `c : Set (Set α)` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `t ∈ c`. -/
theorem lebesgue_number_lemma_sUnion {S : Set (Set α)}
    (hK : IsCompact K) (hopen : ∀ s ∈ S, IsOpen s) (hcover : K ⊆ ⋃₀ S) :
    ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ s ∈ S, ball x V ⊆ s := by
  rw [sUnion_eq_iUnion] at hcover
  simpa using lebesgue_number_lemma hK (by simpa) hcover
#align lebesgue_number_lemma_sUnion lebesgue_number_lemma_sUnion

/-- If `K` is a compact set in a uniform space and `{V i | p i}` is a basis of entourages,
then `{⋃ x ∈ K, UniformSpace.ball x (V i) | p i}` is a basis of `𝓝ˢ K`.

Here "`{s i | p i}` is a basis of a filter `l`" means `Filter.HasBasis l p s`. -/
theorem IsCompact.nhdsSet_basis_uniformity {p : ι → Prop} {V : ι → Set (α × α)}
    (hbasis : (𝓤 α).HasBasis p V) (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis p fun i => ⋃ x ∈ K, ball x (V i) where
  mem_iff' U := by
    constructor
    · intro H
      have HKU : K ⊆ ⋃ _ : Unit, interior U := by
        simpa only [iUnion_const, subset_interior_iff_mem_nhdsSet] using H
      obtain ⟨i, hpi, hi⟩ : ∃ i, p i ∧ ⋃ x ∈ K, ball x (V i) ⊆ interior U := by
        simpa using hbasis.lebesgue_number_lemma hK (fun _ ↦ isOpen_interior) HKU
      exact ⟨i, hpi, hi.trans interior_subset⟩
    · rintro ⟨i, hpi, hi⟩
      refine mem_of_superset (bUnion_mem_nhdsSet fun x _ ↦ ?_) hi
      exact ball_mem_nhds _ <| hbasis.mem_of_mem hpi
#align is_compact.nhds_set_basis_uniformity IsCompact.nhdsSet_basis_uniformity

-- TODO: move to a separate file, golf using the regularity of a uniform space.
theorem Disjoint.exists_uniform_thickening {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ V ∈ 𝓤 α, Disjoint (⋃ x ∈ A, ball x V) (⋃ x ∈ B, ball x V) := by
  have : Bᶜ ∈ 𝓝ˢ A := hB.isOpen_compl.mem_nhdsSet.mpr h.le_compl_right
  rw [(hA.nhdsSet_basis_uniformity (Filter.basis_sets _)).mem_iff] at this
  rcases this with ⟨U, hU, hUAB⟩
  rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
  refine ⟨V, hV, Set.disjoint_left.mpr fun x => ?_⟩
  simp only [mem_iUnion₂]
  rintro ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩
  rw [mem_ball_symmetry hVsymm] at hxa hxb
  exact hUAB (mem_iUnion₂_of_mem ha <| hVU <| mem_comp_of_mem_ball hVsymm hxa hxb) hb
#align disjoint.exists_uniform_thickening Disjoint.exists_uniform_thickening

theorem Disjoint.exists_uniform_thickening_of_basis {p : ι → Prop} {s : ι → Set (α × α)}
    (hU : (𝓤 α).HasBasis p s) {A B : Set α} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ i, p i ∧ Disjoint (⋃ x ∈ A, ball x (s i)) (⋃ x ∈ B, ball x (s i)) := by
  rcases h.exists_uniform_thickening hA hB with ⟨V, hV, hVAB⟩
  rcases hU.mem_iff.1 hV with ⟨i, hi, hiV⟩
  exact ⟨i, hi, hVAB.mono (iUnion₂_mono fun a _ => ball_mono hiV a)
    (iUnion₂_mono fun b _ => ball_mono hiV b)⟩
#align disjoint.exists_uniform_thickening_of_basis Disjoint.exists_uniform_thickening_of_basis

/-- A useful consequence of the Lebesgue number lemma: given any compact set `K` contained in an
open set `U`, we can find an (open) entourage `V` such that the ball of size `V` about any point of
`K` is contained in `U`. -/
theorem lebesgue_number_of_compact_open {K U : Set α} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) : ∃ V ∈ 𝓤 α, IsOpen V ∧ ∀ x ∈ K, UniformSpace.ball x V ⊆ U :=
  let ⟨V, ⟨hV, hVo⟩, hVU⟩ :=
    (hK.nhdsSet_basis_uniformity uniformity_hasBasis_open).mem_iff.1 (hU.mem_nhdsSet.2 hKU)
  ⟨V, hV, hVo, iUnion₂_subset_iff.1 hVU⟩
#align lebesgue_number_of_compact_open lebesgue_number_of_compact_open

end Compact

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
#align uniform.tendsto_nhds_right Uniform.tendsto_nhds_right

theorem tendsto_nhds_left {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (u x, a)) f (𝓤 α) := by
  rw [nhds_eq_comap_uniformity', tendsto_comap_iff]; rfl
#align uniform.tendsto_nhds_left Uniform.tendsto_nhds_left

theorem continuousAt_iff'_right [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt, tendsto_nhds_right]
#align uniform.continuous_at_iff'_right Uniform.continuousAt_iff'_right

theorem continuousAt_iff'_left [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt, tendsto_nhds_left]
#align uniform.continuous_at_iff'_left Uniform.continuousAt_iff'_left

theorem continuousAt_iff_prod [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x : β × β => (f x.1, f x.2)) (𝓝 (b, b)) (𝓤 α) :=
  ⟨fun H => le_trans (H.prod_map' H) (nhds_le_uniformity _), fun H =>
    continuousAt_iff'_left.2 <| H.comp <| tendsto_id.prod_mk_nhds tendsto_const_nhds⟩
#align uniform.continuous_at_iff_prod Uniform.continuousAt_iff_prod

theorem continuousWithinAt_iff'_right [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_right]
#align uniform.continuous_within_at_iff'_right Uniform.continuousWithinAt_iff'_right

theorem continuousWithinAt_iff'_left [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_left]
#align uniform.continuous_within_at_iff'_left Uniform.continuousWithinAt_iff'_left

theorem continuousOn_iff'_right [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuousWithinAt_iff'_right]
#align uniform.continuous_on_iff'_right Uniform.continuousOn_iff'_right

theorem continuousOn_iff'_left [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuousWithinAt_iff'_left]
#align uniform.continuous_on_iff'_left Uniform.continuousOn_iff'_left

theorem continuous_iff'_right [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds_right
#align uniform.continuous_iff'_right Uniform.continuous_iff'_right

theorem continuous_iff'_left [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds_left
#align uniform.continuous_iff'_left Uniform.continuous_iff'_left

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
#align filter.tendsto.congr_uniformity Filter.Tendsto.congr_uniformity

theorem Uniform.tendsto_congr {α β} [UniformSpace β] {f g : α → β} {l : Filter α} {b : β}
    (hfg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto f l (𝓝 b) ↔ Tendsto g l (𝓝 b) :=
  ⟨fun h => h.congr_uniformity hfg, fun h => h.congr_uniformity hfg.uniformity_symm⟩
#align uniform.tendsto_congr Uniform.tendsto_congr

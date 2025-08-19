/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Monotonicity.Basic
import Mathlib.Topology.Order

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

theorem eq_singleton_left_of_prod_subset_idRel {X : Type*} {S T : Set X} (hS : S.Nonempty)
    (hT : T.Nonempty) (h_diag : S ×ˢ T ⊆ idRel) : ∃ x, S = {x} := by
  rcases hS, hT with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  refine ⟨s, eq_singleton_iff_nonempty_unique_mem.mpr ⟨⟨s, hs⟩, fun x hx ↦ ?_⟩⟩
  rw [prod_subset_iff] at h_diag
  replace hs := h_diag s hs t ht
  replace hx := h_diag x hx t ht
  simp only [idRel, mem_setOf_eq] at hx hs
  rwa [← hs] at hx

theorem eq_singleton_right_prod_subset_idRel {X : Type*} {S T : Set X} (hS : S.Nonempty)
    (hT : T.Nonempty) (h_diag : S ×ˢ T ⊆ idRel) : ∃ x, T = {x} := by
  rw [Set.prod_subset_iff] at h_diag
  replace h_diag := fun x hx y hy ↦ (h_diag y hy x hx).symm
  exact eq_singleton_left_of_prod_subset_idRel hT hS (prod_subset_iff.mpr h_diag)

theorem eq_singleton_prod_subset_idRel {X : Type*} {S T : Set X} (hS : S.Nonempty)
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
  Set.ext fun ⟨a, b⟩ ↦ by simpa [image_swap_eq_preimage_swap] using eq_comm

theorem Monotone.compRel [Preorder β] {f g : β → Set (α × α)} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x ↦ f x ○ g x := fun _ _ h _ ⟨z, h₁, h₂⟩ ↦ ⟨z, hf h h₁, hg h h₂⟩

@[mono, gcongr]
theorem compRel_mono {f g h k : Set (α × α)} (h₁ : f ⊆ h) (h₂ : g ⊆ k) : f ○ g ⊆ h ○ k :=
  fun _ ⟨z, h, h'⟩ ↦ ⟨z, h₁ h, h₂ h'⟩

theorem prodMk_mem_compRel {a b c : α} {s t : Set (α × α)} (h₁ : (a, c) ∈ s) (h₂ : (c, b) ∈ t) :
    (a, b) ∈ s ○ t :=
  ⟨c, h₁, h₂⟩

@[deprecated (since := "2025-03-10")]
alias prod_mk_mem_compRel := prodMk_mem_compRel

@[simp]
theorem id_compRel {r : Set (α × α)} : idRel ○ r = r :=
  Set.ext fun ⟨a, b⟩ ↦ by simp

theorem compRel_assoc {r s t : Set (α × α)} : r ○ s ○ t = r ○ (s ○ t) := by
  ext ⟨a, b⟩; simp only [mem_compRel]; tauto

theorem left_subset_compRel {s t : Set (α × α)} (h : idRel ⊆ t) : s ⊆ s ○ t := fun ⟨_x, y⟩ xy_in ↦
  ⟨y, xy_in, h <| rfl⟩

theorem right_subset_compRel {s t : Set (α × α)} (h : idRel ⊆ s) : t ⊆ s ○ t := fun ⟨x, _y⟩ xy_in ↦
  ⟨x, h <| rfl, xy_in⟩

theorem subset_comp_self {s : Set (α × α)} (h : idRel ⊆ s) : s ⊆ s ○ s :=
  left_subset_compRel h

theorem subset_iterate_compRel {s t : Set (α × α)} (h : idRel ⊆ s) (n : ℕ) :
    t ⊆ (s ○ ·)^[n] t := by
  induction n generalizing t with
  | zero => exact Subset.rfl
  | succ n ihn => exact (right_subset_compRel h).trans ihn

/-- The relation is invariant under swapping factors. -/
def IsSymmetricRel (V : Set (α × α)) : Prop :=
  Prod.swap ⁻¹' V = V

@[deprecated (since := "2025-03-05")]
alias SymmetricRel := IsSymmetricRel

/-- The maximal symmetric relation contained in a given relation. -/
def symmetrizeRel (V : Set (α × α)) : Set (α × α) :=
  V ∩ Prod.swap ⁻¹' V

theorem symmetric_symmetrizeRel (V : Set (α × α)) : IsSymmetricRel (symmetrizeRel V) := by
  simp [IsSymmetricRel, symmetrizeRel, preimage_inter, inter_comm, ← preimage_comp]

theorem symmetrizeRel_subset_self (V : Set (α × α)) : symmetrizeRel V ⊆ V :=
  sep_subset _ _

@[mono]
theorem symmetrize_mono {V W : Set (α × α)} (h : V ⊆ W) : symmetrizeRel V ⊆ symmetrizeRel W :=
  inter_subset_inter h <| preimage_mono h

theorem IsSymmetricRel.mk_mem_comm {V : Set (α × α)} (hV : IsSymmetricRel V) {x y : α} :
    (x, y) ∈ V ↔ (y, x) ∈ V :=
  Set.ext_iff.1 hV (y, x)

@[deprecated (since := "2025-03-05")]
alias SymmetricRel.mk_mem_comm := IsSymmetricRel.mk_mem_comm

theorem IsSymmetricRel.eq {U : Set (α × α)} (hU : IsSymmetricRel U) : Prod.swap ⁻¹' U = U :=
  hU

@[deprecated (since := "2025-03-05")]
alias SymmetricRel.eq := IsSymmetricRel.eq

theorem IsSymmetricRel.inter {U V : Set (α × α)} (hU : IsSymmetricRel U) (hV : IsSymmetricRel V) :
    IsSymmetricRel (U ∩ V) := by rw [IsSymmetricRel, preimage_inter, hU.eq, hV.eq]

@[deprecated (since := "2025-03-05")]
alias SymmetricRel.inter := IsSymmetricRel.inter

theorem IsSymmetricRel.iInter {U : (i : ι) → Set (α × α)} (hU : ∀ i, IsSymmetricRel (U i)) :
    IsSymmetricRel (⋂ i, U i) := by
  simp_rw [IsSymmetricRel, preimage_iInter, (hU _).eq]

lemma IsSymmetricRel.sInter {s : Set (Set (α × α))} (h : ∀ i ∈ s, IsSymmetricRel i) :
    IsSymmetricRel (⋂₀ s) := by
  rw [sInter_eq_iInter]
  exact IsSymmetricRel.iInter (by simpa)

lemma isSymmetricRel_idRel : IsSymmetricRel (idRel : Set (α × α)) := by
  simp [IsSymmetricRel, idRel, eq_comm]

lemma isSymmetricRel_univ : IsSymmetricRel (Set.univ : Set (α × α)) := by
  simp [IsSymmetricRel]

lemma IsSymmetricRel.preimage_prodMap {U : Set (β × β)} (ht : IsSymmetricRel U) (f : α → β) :
    IsSymmetricRel (Prod.map f f ⁻¹' U) :=
  Set.ext fun _ ↦ ht.mk_mem_comm

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
  comp : (uniformity.lift' fun s ↦ s ○ s) ≤ uniformity

protected theorem UniformSpace.Core.comp_mem_uniformity_sets {c : Core α} {s : Set (α × α)}
    (hs : s ∈ c.uniformity) : ∃ t ∈ c.uniformity, t ○ t ⊆ s :=
  (mem_lift'_sets <| monotone_id.compRel monotone_id).mp <| c.comp hs

/-- An alternative constructor for `UniformSpace.Core`. This version unfolds various
`Filter`-related definitions. -/
def UniformSpace.Core.mk' {α : Type u} (U : Filter (α × α)) (refl : ∀ r ∈ U, ∀ (x), (x, x) ∈ r)
    (symm : ∀ r ∈ U, Prod.swap ⁻¹' r ∈ U) (comp : ∀ r ∈ U, ∃ t ∈ U, t ○ t ⊆ r) :
    UniformSpace.Core α :=
  ⟨U, fun _r ru ↦ idRel_subset.2 (refl _ ru), symm, fun _r ru ↦
    let ⟨_s, hs, hsr⟩ := comp _ ru
    mem_of_superset (mem_lift' hs) hsr⟩

/-- Defining a `UniformSpace.Core` from a filter basis satisfying some uniformity-like axioms. -/
def UniformSpace.Core.mkOfBasis {α : Type u} (B : FilterBasis (α × α))
    (refl : ∀ r ∈ B, ∀ (x), (x, x) ∈ r) (symm : ∀ r ∈ B, ∃ t ∈ B, t ⊆ Prod.swap ⁻¹' r)
    (comp : ∀ r ∈ B, ∃ t ∈ B, t ○ t ⊆ r) : UniformSpace.Core α where
  uniformity := B.filter
  refl := B.hasBasis.ge_iff.mpr fun _r ru ↦ idRel_subset.2 <| refl _ ru
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
  protected comp : (uniformity.lift' fun s ↦ s ○ s) ≤ uniformity
  /-- The uniformity agrees with the topology: the neighborhoods filter of each point `x`
  is equal to `Filter.comap (Prod.mk x) (𝓤 α)`. -/
  protected nhds_eq_comap_uniformity (x : α) : 𝓝 x = comap (Prod.mk x) uniformity

/-- The uniformity is a filter on α × α (inferred from an ambient uniform space
  structure on α). -/
def uniformity (α : Type u) [UniformSpace α] : Filter (α × α) :=
  @UniformSpace.uniformity α _

/-- Notation for the uniformity filter with respect to a non-standard `UniformSpace` instance. -/
scoped[Uniformity] notation "𝓤[" u "]" => @uniformity _ u

@[inherit_doc]
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

lemma UniformSpace.mem_uniformity_ofCore_iff {u : UniformSpace.Core α} {s : Set (α × α)} :
    s ∈ 𝓤[.ofCore u] ↔ s ∈ u.uniformity :=
  Iff.rfl

@[ext (iff := false)]
protected theorem UniformSpace.ext {u₁ u₂ : UniformSpace α} (h : 𝓤[u₁] = 𝓤[u₂]) : u₁ = u₂ := by
  have : u₁.toTopologicalSpace = u₂.toTopologicalSpace := TopologicalSpace.ext_nhds fun x ↦ by
    rw [u₁.nhds_eq_comap_uniformity, u₂.nhds_eq_comap_uniformity]
    exact congr_arg (comap _) h
  cases u₁; cases u₂; congr

protected theorem UniformSpace.ext_iff {u₁ u₂ : UniformSpace α} :
    u₁ = u₂ ↔ ∀ s, s ∈ 𝓤[u₁] ↔ s ∈ 𝓤[u₂] :=
  ⟨fun h _ ↦ h ▸ Iff.rfl, fun h ↦ by ext; exact h _⟩

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
  simp only [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap_prodMk]

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

theorem comp_le_uniformity : ((𝓤 α).lift' fun s : Set (α × α) ↦ s ○ s) ≤ 𝓤 α :=
  UniformSpace.comp

theorem lift'_comp_uniformity : ((𝓤 α).lift' fun s : Set (α × α) ↦ s ○ s) = 𝓤 α :=
  comp_le_uniformity.antisymm <| le_lift'.2 fun _s hs ↦ mem_of_superset hs <|
    subset_comp_self <| idRel_subset.2 fun _ ↦ refl_mem_uniformity hs

theorem tendsto_swap_uniformity : Tendsto (@Prod.swap α α) (𝓤 α) (𝓤 α) :=
  symm_le_uniformity

theorem comp_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ t ⊆ s :=
  (mem_lift'_sets <| monotone_id.compRel monotone_id).mp <| comp_le_uniformity hs

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is transitive. -/
theorem Filter.Tendsto.uniformity_trans {l : Filter β} {f₁ f₂ f₃ : β → α}
    (h₁₂ : Tendsto (fun x ↦ (f₁ x, f₂ x)) l (𝓤 α))
    (h₂₃ : Tendsto (fun x ↦ (f₂ x, f₃ x)) l (𝓤 α)) : Tendsto (fun x ↦ (f₁ x, f₃ x)) l (𝓤 α) := by
  refine le_trans (le_lift'.2 fun s hs ↦ mem_map.2 ?_) comp_le_uniformity
  filter_upwards [mem_map.1 (h₁₂ hs), mem_map.1 (h₂₃ hs)] with x hx₁₂ hx₂₃ using ⟨_, hx₁₂, hx₂₃⟩

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is symmetric. -/
theorem Filter.Tendsto.uniformity_symm {l : Filter β} {f : β → α × α} (h : Tendsto f l (𝓤 α)) :
    Tendsto (fun x ↦ ((f x).2, (f x).1)) l (𝓤 α) :=
  tendsto_swap_uniformity.comp h

/-- Relation `fun f g ↦ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α)` is reflexive. -/
theorem tendsto_diag_uniformity (f : β → α) (l : Filter β) :
    Tendsto (fun x ↦ (f x, f x)) l (𝓤 α) := fun _s hs ↦
  mem_map.2 <| univ_mem' fun _ ↦ refl_mem_uniformity hs

theorem tendsto_const_uniformity {a : α} {f : Filter β} : Tendsto (fun _ ↦ (a, a)) f (𝓤 α) :=
  tendsto_diag_uniformity (fun _ ↦ a) f

theorem symm_of_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, (∀ a b, (a, b) ∈ t → (b, a) ∈ t) ∧ t ⊆ s :=
  have : preimage Prod.swap s ∈ 𝓤 α := symm_le_uniformity hs
  ⟨s ∩ preimage Prod.swap s, inter_mem hs this, fun _ _ ⟨h₁, h₂⟩ ↦ ⟨h₂, h₁⟩, inter_subset_left⟩

theorem comp_symm_of_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, (∀ {a b}, (a, b) ∈ t → (b, a) ∈ t) ∧ t ○ t ⊆ s :=
  let ⟨_t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  let ⟨t', ht', ht'₁, ht'₂⟩ := symm_of_uniformity ht₁
  ⟨t', ht', ht'₁ _ _, Subset.trans (monotone_id.compRel monotone_id ht'₂) ht₂⟩

theorem uniformity_le_symm : 𝓤 α ≤ map Prod.swap (𝓤 α) := by
  rw [map_swap_eq_comap_swap]; exact tendsto_swap_uniformity.le_comap

theorem uniformity_eq_symm : 𝓤 α = map Prod.swap (𝓤 α) :=
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
    (𝓤 α).HasBasis (fun s : Set (α × α) ↦ s ∈ 𝓤 α ∧ IsSymmetricRel s) id :=
  hasBasis_self.2 fun t t_in ↦
    ⟨symmetrizeRel t, symmetrize_mem_uniformity t_in, symmetric_symmetrizeRel t,
      symmetrizeRel_subset_self t⟩

theorem uniformity_lift_le_swap {g : Set (α × α) → Filter β} {f : Filter β} (hg : Monotone g)
    (h : ((𝓤 α).lift fun s ↦ g (preimage Prod.swap s)) ≤ f) : (𝓤 α).lift g ≤ f :=
  calc
    (𝓤 α).lift g ≤ (Filter.map (@Prod.swap α α) <| 𝓤 α).lift g :=
      lift_mono uniformity_le_symm le_rfl
    _ ≤ _ := by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h

theorem uniformity_lift_le_comp {f : Set (α × α) → Filter β} (h : Monotone f) :
    ((𝓤 α).lift fun s ↦ f (s ○ s)) ≤ (𝓤 α).lift f :=
  calc
    ((𝓤 α).lift fun s ↦ f (s ○ s)) = ((𝓤 α).lift' fun s : Set (α × α) ↦ s ○ s).lift f := by
      rw [lift_lift'_assoc]
      · exact monotone_id.compRel monotone_id
      · exact h
    _ ≤ (𝓤 α).lift f := lift_mono comp_le_uniformity le_rfl

theorem comp3_mem_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ (t ○ t) ⊆ s :=
  let ⟨_t', ht', ht's⟩ := comp_mem_uniformity_sets hs
  let ⟨t, ht, htt'⟩ := comp_mem_uniformity_sets ht'
  ⟨t, ht, (compRel_mono ((subset_comp_self (refl_le_uniformity ht)).trans htt') htt').trans ht's⟩

/-- See also `comp3_mem_uniformity`. -/
theorem comp_le_uniformity3 : ((𝓤 α).lift' fun s : Set (α × α) ↦ s ○ (s ○ s)) ≤ 𝓤 α := fun _ h ↦
  let ⟨_t, htU, ht⟩ := comp3_mem_uniformity h
  mem_of_superset (mem_lift' htU) ht

/-- See also `comp_open_symm_mem_uniformity_sets`. -/
theorem comp_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, IsSymmetricRel t ∧ t ○ t ⊆ s := by
  obtain ⟨w, w_in, w_sub⟩ : ∃ w ∈ 𝓤 α, w ○ w ⊆ s := comp_mem_uniformity_sets hs
  use symmetrizeRel w, symmetrize_mem_uniformity w_in, symmetric_symmetrizeRel w
  have : symmetrizeRel w ⊆ w := symmetrizeRel_subset_self w
  calc symmetrizeRel w ○ symmetrizeRel w
    _ ⊆ w ○ w := by gcongr
    _ ⊆ s     := w_sub

theorem subset_comp_self_of_mem_uniformity {s : Set (α × α)} (h : s ∈ 𝓤 α) : s ⊆ s ○ s :=
  subset_comp_self (refl_le_uniformity h)

theorem comp_comp_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, IsSymmetricRel t ∧ t ○ t ○ t ⊆ s := by
  rcases comp_symm_mem_uniformity_sets hs with ⟨w, w_in, _, w_sub⟩
  rcases comp_symm_mem_uniformity_sets w_in with ⟨t, t_in, t_symm, t_sub⟩
  use t, t_in, t_symm
  have : t ⊆ t ○ t := subset_comp_self_of_mem_uniformity t_in
  calc
    t ○ t ○ t ⊆ w ○ (t ○ t) := by gcongr
    _ ⊆ w ○ w := by gcongr
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
  prodMk_mem_compRel h h'

theorem ball_subset_of_comp_subset {V W : Set (β × β)} {x y} (h : x ∈ ball y W) (h' : W ○ W ⊆ V) :
    ball x W ⊆ ball y V := fun _z z_in ↦ h' (mem_ball_comp h z_in)

theorem ball_mono {V W : Set (β × β)} (h : V ⊆ W) (x : β) : ball x V ⊆ ball x W :=
  preimage_mono h

theorem ball_inter (x : β) (V W : Set (β × β)) : ball x (V ∩ W) = ball x V ∩ ball x W :=
  preimage_inter

theorem ball_inter_left (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x V :=
  ball_mono inter_subset_left x

theorem ball_inter_right (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x W :=
  ball_mono inter_subset_right x

theorem ball_iInter {x : β} {V : ι → Set (β × β)} : ball x (⋂ i, V i) = ⋂ i, ball x (V i) :=
  preimage_iInter

theorem mem_ball_symmetry {V : Set (β × β)} (hV : IsSymmetricRel V) {x y} :
    x ∈ ball y V ↔ y ∈ ball x V :=
  show (x, y) ∈ Prod.swap ⁻¹' V ↔ (x, y) ∈ V by
    unfold IsSymmetricRel at hV
    rw [hV]

theorem ball_eq_of_symmetry {V : Set (β × β)} (hV : IsSymmetricRel V) {x} :
    ball x V = { y | (y, x) ∈ V } := by
  ext y
  rw [mem_ball_symmetry hV]
  exact Iff.rfl

theorem mem_comp_of_mem_ball {V W : Set (β × β)} {x y z : β} (hV : IsSymmetricRel V)
    (hx : x ∈ ball z V) (hy : y ∈ ball z W) : (x, y) ∈ V ○ W := by
  rw [mem_ball_symmetry hV] at hx
  exact ⟨z, hx, hy⟩

theorem mem_comp_comp {V W M : Set (β × β)} (hW' : IsSymmetricRel W) {p : β × β} :
    p ∈ V ○ M ○ W ↔ (ball p.1 V ×ˢ ball p.2 W ∩ M).Nonempty := by
  obtain ⟨x, y⟩ := p
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
  simp only [nhds_eq_comap_uniformity, mem_comap_prodMk]

theorem mem_nhds_uniformity_iff_left {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ { p : α × α | p.2 = x → p.1 ∈ s } ∈ 𝓤 α := by
  rw [uniformity_eq_symm, mem_nhds_uniformity_iff_right]
  simp only [mem_map, preimage_setOf_eq, Prod.snd_swap, Prod.fst_swap]

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
    {x : α} : (𝓝 x).HasBasis p fun i ↦ ball x (s i) := by
  rw [nhds_eq_comap_uniformity]
  exact h.comap (Prod.mk x)

theorem nhds_basis_uniformity {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i ↦ { y | (y, x) ∈ s i } := by
  replace h := h.comap Prod.swap
  rw [comap_swap_uniformity] at h
  exact nhds_basis_uniformity' h

theorem nhds_eq_comap_uniformity' {x : α} : 𝓝 x = (𝓤 α).comap fun y ↦ (y, x) :=
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
    s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, IsSymmetricRel V ∧ ball x V ⊆ s := by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    use symmetrizeRel V, symmetrize_mem_uniformity V_in, symmetric_symmetrizeRel V
    exact Subset.trans (ball_mono (symmetrizeRel_subset_self V) x) V_sub
  · rintro ⟨V, V_in, _, V_sub⟩
    exact ⟨V, V_in, V_sub⟩

theorem UniformSpace.hasBasis_nhds (x : α) :
    HasBasis (𝓝 x) (fun s : Set (α × α) ↦ s ∈ 𝓤 α ∧ IsSymmetricRel s) fun s ↦ ball x s :=
  ⟨fun t ↦ by simp [UniformSpace.mem_nhds_iff_symm, and_assoc]⟩

open UniformSpace

theorem UniformSpace.mem_closure_iff_symm_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → IsSymmetricRel V → (s ∩ ball x V).Nonempty := by
  simp [mem_closure_iff_nhds_basis (hasBasis_nhds x), Set.Nonempty]

theorem UniformSpace.mem_closure_iff_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → (ball x V ∩ s).Nonempty := by
  simp [mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (𝓤 α).basis_sets)]

theorem nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball x) :=
  (nhds_basis_uniformity' (𝓤 α).basis_sets).eq_biInf

theorem nhds_eq_uniformity' {x : α} : 𝓝 x = (𝓤 α).lift' fun s ↦ { y | (y, x) ∈ s } :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_biInf

theorem mem_nhds_left (x : α) {s : Set (α × α)} (h : s ∈ 𝓤 α) : { y : α | (x, y) ∈ s } ∈ 𝓝 x :=
  ball_mem_nhds x h

theorem mem_nhds_right (y : α) {s : Set (α × α)} (h : s ∈ 𝓤 α) : { x : α | (x, y) ∈ s } ∈ 𝓝 y :=
  mem_nhds_left _ (symm_le_uniformity h)

theorem exists_mem_nhds_ball_subset_of_mem_nhds {a : α} {U : Set α} (h : U ∈ 𝓝 a) :
    ∃ V ∈ 𝓝 a, ∃ t ∈ 𝓤 α, ∀ a' ∈ V, UniformSpace.ball a' t ⊆ U :=
  let ⟨t, ht, htU⟩ := comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 h)
  ⟨_, mem_nhds_left a ht, t, ht, fun a₁ h₁ a₂ h₂ ↦ @htU (a, a₂) ⟨a₁, h₁, h₂⟩ rfl⟩

theorem tendsto_right_nhds_uniformity {a : α} : Tendsto (fun a' ↦ (a', a)) (𝓝 a) (𝓤 α) := fun _ ↦
  mem_nhds_right a

theorem tendsto_left_nhds_uniformity {a : α} : Tendsto (fun a' ↦ (a, a')) (𝓝 a) (𝓤 α) := fun _ ↦
  mem_nhds_left a

theorem lift_nhds_left {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : Set (α × α) ↦ g (ball x s) := by
  rw [nhds_eq_comap_uniformity, comap_lift_eq2 hg]
  simp_rw [ball, Function.comp_def]

theorem lift_nhds_right {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : Set (α × α) ↦ g { y | (y, x) ∈ s } := by
  rw [nhds_eq_comap_uniformity', comap_lift_eq2 hg]
  simp_rw [Function.comp_def, preimage]

theorem nhds_nhds_eq_uniformity_uniformity_prod {a b : α} :
    𝓝 a ×ˢ 𝓝 b = (𝓤 α).lift fun s : Set (α × α) ↦
      (𝓤 α).lift' fun t ↦ { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ t } := by
  rw [nhds_eq_uniformity', nhds_eq_uniformity, prod_lift'_lift']
  exacts [rfl, monotone_preimage, monotone_preimage]

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
  Tendsto (fun x : α × α ↦ (f x.1, f x.2)) (𝓤 α) (𝓤 β)

/-- Notation for uniform continuity with respect to non-standard `UniformSpace` instances. -/
scoped[Uniformity] notation "UniformContinuous[" u₁ ", " u₂ "]" => @UniformContinuous _ _ u₁ u₂

/-- A function `f : α → β` is *uniformly continuous* on `s : Set α` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s ×ˢ s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`. -/
def UniformContinuousOn [UniformSpace β] (f : α → β) (s : Set α) : Prop :=
  Tendsto (fun x : α × α ↦ (f x.1, f x.2)) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 β)

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
  have : (fun x : α × α ↦ (c x.fst, c x.snd)) ⁻¹' idRel = univ :=
    eq_univ_iff_forall.2 fun ⟨a, b⟩ ↦ h a b
  le_trans (map_le_iff_le_comap.2 <| by simp [comap_principal, this]) refl_le_uniformity

theorem uniformContinuous_id : UniformContinuous (@id α) := tendsto_id

theorem uniformContinuous_const [UniformSpace β] {b : β} : UniformContinuous fun _ : α ↦ b :=
  uniformContinuous_of_const fun _ _ ↦ rfl

nonrec theorem UniformContinuous.comp [UniformSpace β] [UniformSpace γ] {g : β → γ} {f : α → β}
    (hg : UniformContinuous g) (hf : UniformContinuous f) : UniformContinuous (g ∘ f) :=
  hg.comp hf

/-- If a function `T` is uniformly continuous in a uniform space `β`,
then its `n`-th iterate `T^[n]` is also uniformly continuous. -/
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

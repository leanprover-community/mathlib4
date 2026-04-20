/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Data.Rel.Cover
public import Mathlib.Topology.Order

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

## Notation

Localized in `Uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`.
This file also uses a lot the notation `○` for composition of relations, seen as terms with
type `SetRel X X`. This notation (defined in the file `Mathlib/Data/Rel.lean`) is
localized in `SetRel`.

## Implementation notes

We use the theory of relations as sets developed in `Mathlib/Data/Rel.lean`.
The relevant definition is `SetRel X X := Set (X × X)`, which is the type of elements of
the uniformity filter `𝓤 X : Filter (X × X)`.

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

@[expose] public section

open Set Filter Topology

universe u v ua ub uc ud

/-!
### Relations, seen as `SetRel α α`
-/

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

/-- The identity relation, or the graph of the identity function -/
@[deprecated SetRel.id (since := "2025-10-17")]
def idRel {α : Type*} :=
  { p : α × α | p.1 = p.2 }

set_option linter.deprecated false in
@[deprecated SetRel.mem_id (since := "2025-10-17")]
theorem mem_idRel {a b : α} : (a, b) ∈ @idRel α ↔ a = b :=
  Iff.rfl

set_option linter.deprecated false in
@[deprecated SetRel.id_subset_iff (since := "2025-10-17")]
theorem idRel_subset {s : SetRel α α} : idRel ⊆ s ↔ ∀ a, (a, a) ∈ s := by
  simp [subset_def, mem_idRel]

set_option linter.deprecated false in
@[deprecated SetRel.exists_eq_singleton_of_prod_subset_id (since := "2025-10-17")]
theorem eq_singleton_left_of_prod_subset_idRel {X : Type*} {S T : Set X} (hS : S.Nonempty)
    (hT : T.Nonempty) (h_diag : S ×ˢ T ⊆ SetRel.id) : ∃ x, S = {x} := by
  obtain ⟨x, hx, -⟩ := SetRel.exists_eq_singleton_of_prod_subset_id hS hT h_diag; exact ⟨x, hx⟩

set_option linter.deprecated false in
@[deprecated SetRel.exists_eq_singleton_of_prod_subset_id (since := "2025-10-17")]
theorem eq_singleton_right_prod_subset_idRel {X : Type*} {S T : Set X} (hS : S.Nonempty)
    (hT : T.Nonempty) (h_diag : S ×ˢ T ⊆ SetRel.id) : ∃ x, T = {x} := by
  obtain ⟨x, -, hx⟩ := SetRel.exists_eq_singleton_of_prod_subset_id hS hT h_diag; exact ⟨x, hx⟩

@[deprecated (since := "2025-10-17")]
alias eq_singleton_prod_subset_idRel := SetRel.exists_eq_singleton_of_prod_subset_id

set_option linter.deprecated false in
/-- The composition of relations -/
@[deprecated SetRel.comp (since := "2025-10-17")]
def compRel (r₁ r₂ : SetRel α α) :=
  { p : α × α | ∃ z : α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂ }

open scoped SetRel

set_option linter.deprecated false in
@[deprecated SetRel.mem_comp (since := "2025-10-17")]
theorem mem_compRel {α : Type u} {r₁ r₂ : SetRel α α} {x y : α} :
    (x, y) ∈ r₁ ○ r₂ ↔ ∃ z, (x, z) ∈ r₁ ∧ (z, y) ∈ r₂ :=
  Iff.rfl

set_option linter.deprecated false in
@[deprecated SetRel.inv_id (since := "2025-10-17")]
theorem swap_idRel : Prod.swap '' idRel = @idRel α :=
  Set.ext fun ⟨a, b⟩ => by simpa [image_swap_eq_preimage_swap] using eq_comm

set_option linter.deprecated false in
@[deprecated Monotone.relComp (since := "2025-10-17")]
theorem Monotone.compRel [Preorder β] {f g : β → SetRel α α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ○ g x := fun _ _ h _ ⟨z, h₁, h₂⟩ => ⟨z, hf h h₁, hg h h₂⟩

@[deprecated (since := "2025-10-17")] alias compRel_mono := SetRel.comp_subset_comp
@[deprecated (since := "2025-10-17")] alias compRel_left_mono := SetRel.comp_subset_comp_left
@[deprecated (since := "2025-10-17")] alias compRel_right_mono := SetRel.comp_subset_comp_right
@[deprecated (since := "2025-10-17")] alias prodMk_mem_compRel := SetRel.prodMk_mem_comp
set_option linter.deprecated false in
@[deprecated SetRel.id_comp (since := "2025-10-17")]
theorem id_compRel {r : SetRel α α} : idRel ○ r = r :=
  SetRel.id_comp _

@[deprecated SetRel.comp_assoc (since := "2025-10-17")]
theorem compRel_assoc {r s t : SetRel α α} : r ○ s ○ t = r ○ (s ○ t) := by
  apply SetRel.comp_assoc

set_option linter.deprecated false in
@[deprecated SetRel.left_subset_comp (since := "2025-10-17")]
theorem left_subset_compRel {s t : SetRel α α} (h : idRel ⊆ t) : s ⊆ s ○ t := fun ⟨_x, y⟩ xy_in =>
  ⟨y, xy_in, h <| rfl⟩

set_option linter.deprecated false in
@[deprecated SetRel.right_subset_comp (since := "2025-10-17")]
theorem right_subset_compRel {s t : SetRel α α} (h : idRel ⊆ s) : t ⊆ s ○ t := fun ⟨x, _y⟩ xy_in =>
  ⟨x, h <| rfl, xy_in⟩

set_option linter.deprecated false in
@[deprecated SetRel.left_subset_comp (since := "2025-10-17")]
theorem subset_comp_self {s : SetRel α α} (h : idRel ⊆ s) : s ⊆ s ○ s :=
  left_subset_compRel h

set_option linter.deprecated false in
@[deprecated SetRel.subset_iterate_comp (since := "2025-10-17")]
theorem subset_iterate_compRel {s t : SetRel α α} (h : idRel ⊆ s) (n : ℕ) :
    t ⊆ (s ○ ·)^[n] t := by
  induction n generalizing t with
  | zero => exact Subset.rfl
  | succ n ihn => exact (right_subset_compRel h).trans ihn

/-- The relation is invariant under swapping factors. -/
@[deprecated SetRel.IsSymm (since := "2025-10-17")]
def IsSymmetricRel (V : SetRel α α) : Prop :=
  Prod.swap ⁻¹' V = V

/-- The maximal symmetric relation contained in a given relation. -/
@[deprecated SetRel.symmetrize (since := "2025-10-17")]
def symmetrizeRel (V : SetRel α α) : SetRel α α :=
  V ∩ Prod.swap ⁻¹' V

set_option linter.deprecated false in
@[deprecated SetRel.isSymm_symmetrize (since := "2025-10-17")]
theorem symmetric_symmetrizeRel (V : SetRel α α) : IsSymmetricRel (symmetrizeRel V) := by
  simp [IsSymmetricRel, symmetrizeRel, preimage_inter, inter_comm, ← preimage_comp]

set_option linter.deprecated false in
@[deprecated SetRel.symmetrize_subset_self (since := "2025-10-17")]
theorem symmetrizeRel_subset_self (V : SetRel α α) : symmetrizeRel V ⊆ V :=
  sep_subset _ _

set_option linter.deprecated false in
@[deprecated SetRel.symmetrize_mono (since := "2025-10-17")]
theorem symmetrize_mono {V W : SetRel α α} (h : V ⊆ W) : symmetrizeRel V ⊆ symmetrizeRel W :=
  inter_subset_inter h <| preimage_mono h

set_option linter.deprecated false in
@[deprecated SetRel.comm (since := "2025-10-17")]
theorem IsSymmetricRel.mk_mem_comm {V : SetRel α α} (hV : IsSymmetricRel V) {x y : α} :
    (x, y) ∈ V ↔ (y, x) ∈ V :=
  Set.ext_iff.1 hV (y, x)

set_option linter.deprecated false in
@[deprecated SetRel.inv_eq_self (since := "2025-10-17")]
theorem IsSymmetricRel.eq {U : SetRel α α} (hU : IsSymmetricRel U) : Prod.swap ⁻¹' U = U :=
  hU

set_option linter.deprecated false in
@[deprecated SetRel.isSymm_inter (since := "2025-10-17")]
theorem IsSymmetricRel.inter {U V : SetRel α α} (hU : IsSymmetricRel U) (hV : IsSymmetricRel V) :
    IsSymmetricRel (U ∩ V) := by rw [IsSymmetricRel, preimage_inter, hU.eq, hV.eq]

set_option linter.deprecated false in
@[deprecated SetRel.isSymm_iInter (since := "2025-10-17")]
theorem IsSymmetricRel.iInter {U : (i : ι) → SetRel α α} (hU : ∀ i, IsSymmetricRel (U i)) :
    IsSymmetricRel (⋂ i, U i) := by
  simp_rw [IsSymmetricRel, preimage_iInter, (hU _).eq]

set_option linter.deprecated false in
@[deprecated SetRel.IsSymm.sInter (since := "2025-10-17")]
lemma IsSymmetricRel.sInter {s : Set (SetRel α α)} (h : ∀ i ∈ s, IsSymmetricRel i) :
    IsSymmetricRel (⋂₀ s) := by
  rw [sInter_eq_iInter]
  exact IsSymmetricRel.iInter (by simpa)

set_option linter.deprecated false in
@[deprecated SetRel.isSymm_id (since := "2025-10-17")]
lemma isSymmetricRel_idRel : IsSymmetricRel (idRel : Set (α × α)) := by
  simp [IsSymmetricRel, idRel, eq_comm]

set_option linter.deprecated false in
@[deprecated SetRel.isSymm_univ (since := "2025-10-17")]
lemma isSymmetricRel_univ : IsSymmetricRel (Set.univ : Set (α × α)) := by
  simp [IsSymmetricRel]

set_option linter.deprecated false in
@[deprecated SetRel.isSymm_preimage (since := "2025-10-17")]
lemma IsSymmetricRel.preimage_prodMap {U : Set (β × β)} (ht : IsSymmetricRel U) (f : α → β) :
    IsSymmetricRel (Prod.map f f ⁻¹' U) :=
  Set.ext fun _ ↦ ht.mk_mem_comm

set_option linter.deprecated false in
@[deprecated SetRel.isSymm_image (since := "2025-10-17")]
lemma IsSymmetricRel.image_prodMap {U : Set (α × α)} (ht : IsSymmetricRel U) (f : α → β) :
    IsSymmetricRel (Prod.map f f '' U) := by
  rw [IsSymmetricRel, ← image_swap_eq_preimage_swap, ← image_comp, ← Prod.map_comp_swap, image_comp,
      image_swap_eq_preimage_swap, ht]

set_option linter.deprecated false in
@[deprecated SetRel.prod_subset_comm (since := "2025-10-17")]
lemma IsSymmetricRel.prod_subset_comm {s : Set (α × α)} {t u : Set α} (hs : IsSymmetricRel s) :
    t ×ˢ u ⊆ s ↔ u ×ˢ t ⊆ s := by
  rw [← hs.eq, ← image_subset_iff, image_swap_prod, hs.eq]

lemma SetRel.mem_filter_prod_comm (R : SetRel α α) {f g : Filter α} [R.IsSymm] :
    R ∈ f ×ˢ g ↔ R ∈ g ×ˢ f := by
  rw [← R.inv_eq_self, SetRel.inv, ← mem_map, ← prod_comm, ← SetRel.inv, R.inv_eq_self]

set_option linter.deprecated false in
@[deprecated SetRel.mem_filter_prod_comm (since := "2025-10-17")]
lemma IsSymmetricRel.mem_filter_prod_comm {s : Set (α × α)} {f g : Filter α}
    (hs : IsSymmetricRel s) :
    s ∈ f ×ˢ g ↔ s ∈ g ×ˢ f := by
  rw [← hs.eq, ← mem_map, ← prod_comm, hs.eq]

/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure UniformSpace.Core (α : Type u) where
  /-- The uniformity filter. Once `UniformSpace` is defined, `𝓤 α` (`_root_.uniformity`) becomes the
  normal form. -/
  uniformity : Filter (α × α)
  /-- Every set in the uniformity filter includes the diagonal. -/
  refl : 𝓟 SetRel.id ≤ uniformity
  /-- If `s ∈ uniformity`, then `Prod.swap ⁻¹' s ∈ uniformity`. -/
  symm : Tendsto Prod.swap uniformity uniformity
  /-- For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆ u`. -/
  comp : (uniformity.lift' fun s => s ○ s) ≤ uniformity

protected theorem UniformSpace.Core.comp_mem_uniformity_sets {c : Core α} {s : SetRel α α}
    (hs : s ∈ c.uniformity) : ∃ t ∈ c.uniformity, t ○ t ⊆ s :=
  (mem_lift'_sets <| monotone_id.relComp monotone_id).mp <| c.comp hs

/-- An alternative constructor for `UniformSpace.Core`. This version unfolds various
`Filter`-related definitions. -/
def UniformSpace.Core.mk' {α : Type u} (U : Filter (α × α)) (refl : ∀ r ∈ U, ∀ (x), (x, x) ∈ r)
    (symm : ∀ r ∈ U, Prod.swap ⁻¹' r ∈ U) (comp : ∀ r ∈ U, ∃ t ∈ U, t ○ t ⊆ r) :
    UniformSpace.Core α where
  uniformity := U
  refl _r ru := SetRel.id_subset_iff.2 ⟨refl _ ru⟩
  symm
  comp _r ru := let ⟨_s, hs, hsr⟩ := comp _ ru; mem_of_superset (mem_lift' hs) hsr

/-- Defining a `UniformSpace.Core` from a filter basis satisfying some uniformity-like axioms. -/
def UniformSpace.Core.mkOfBasis {α : Type u} (B : FilterBasis (α × α))
    (refl : ∀ r ∈ B, ∀ (x), (x, x) ∈ r) (symm : ∀ r ∈ B, ∃ t ∈ B, t ⊆ Prod.swap ⁻¹' r)
    (comp : ∀ r ∈ B, ∃ t ∈ B, t ○ t ⊆ r) : UniformSpace.Core α where
  uniformity := B.filter
  refl := B.hasBasis.ge_iff.mpr fun _r ru => SetRel.id_subset_iff.2 ⟨refl _ ru⟩
  symm := (B.hasBasis.tendsto_iff B.hasBasis).mpr symm
  comp := ((B.hasBasis.lift' (monotone_id.relComp monotone_id)).le_basis_iff B.hasBasis).2 comp

/-- A uniform space generates a topological space -/
@[implicit_reducible]
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
@[informal "uniform space"]
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

@[inherit_doc]
scoped[Uniformity] notation "𝓤" => uniformity

open scoped Uniformity

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

lemma UniformSpace.mem_uniformity_ofCore_iff {u : UniformSpace.Core α} {s : SetRel α α} :
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
  simp only [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap_prodMk]

theorem refl_le_uniformity : 𝓟 SetRel.id ≤ 𝓤 α :=
  (@UniformSpace.toCore α _).refl

instance uniformity.neBot [Nonempty α] : NeBot (𝓤 α) :=
  diagonal_nonempty.principal_neBot.mono refl_le_uniformity

theorem refl_mem_uniformity {x : α} {s : SetRel α α} (h : s ∈ 𝓤 α) : (x, x) ∈ s :=
  refl_le_uniformity h rfl

theorem isRefl_of_mem_uniformity {s : SetRel α α} (h : s ∈ 𝓤 α) : s.IsRefl :=
  ⟨fun _ => refl_mem_uniformity h⟩

theorem mem_uniformity_of_eq {x y : α} {s : SetRel α α} (h : s ∈ 𝓤 α) (hx : x = y) : (x, y) ∈ s :=
  refl_le_uniformity h hx

theorem symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) ≤ 𝓤 _ :=
  UniformSpace.symm

theorem comp_le_uniformity : ((𝓤 α).lift' fun s : SetRel α α => s ○ s) ≤ 𝓤 α :=
  UniformSpace.comp

theorem lift'_comp_uniformity : ((𝓤 α).lift' fun s : SetRel α α => s ○ s) = 𝓤 α :=
  comp_le_uniformity.antisymm <| le_lift'.2 fun _s hs ↦ mem_of_superset hs <|
    have := isRefl_of_mem_uniformity hs; SetRel.left_subset_comp

theorem tendsto_swap_uniformity : Tendsto (@Prod.swap α α) (𝓤 α) (𝓤 α) :=
  symm_le_uniformity

theorem comp_mem_uniformity_sets {s : SetRel α α} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ t ⊆ s :=
  (mem_lift'_sets <| monotone_id.relComp monotone_id).mp <| comp_le_uniformity hs

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

theorem symm_of_uniformity {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SetRel.IsSymm t ∧ t ⊆ s :=
  have : preimage Prod.swap s ∈ 𝓤 α := symm_le_uniformity hs
  ⟨s ∩ preimage Prod.swap s, inter_mem hs this, ⟨fun _ _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩, inter_subset_left⟩

theorem comp_symm_of_uniformity {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, (∀ {a b}, (a, b) ∈ t → (b, a) ∈ t) ∧ t ○ t ⊆ s :=
  let ⟨_t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  let ⟨t', ht', _, ht'₂⟩ := symm_of_uniformity ht₁
  ⟨t', ht', SetRel.symm _, Subset.trans (monotone_id.relComp monotone_id ht'₂) ht₂⟩

theorem uniformity_le_symm : 𝓤 α ≤ map Prod.swap (𝓤 α) := by
  rw [map_swap_eq_comap_swap]; exact tendsto_swap_uniformity.le_comap

theorem uniformity_eq_symm : 𝓤 α = map Prod.swap (𝓤 α) :=
  le_antisymm uniformity_le_symm symm_le_uniformity

@[simp]
theorem comap_swap_uniformity : comap (@Prod.swap α α) (𝓤 α) = 𝓤 α :=
  (congr_arg _ uniformity_eq_symm).trans <| comap_map Prod.swap_injective

theorem symmetrize_mem_uniformity {V : SetRel α α} (h : V ∈ 𝓤 α) : SetRel.symmetrize V ∈ 𝓤 α := by
  apply (𝓤 α).inter_sets h
  rw [← comap_swap_uniformity]
  exact preimage_mem_comap h

/-- Symmetric entourages form a basis of `𝓤 α` -/
theorem UniformSpace.hasBasis_symmetric :
    (𝓤 α).HasBasis (fun s : SetRel α α => s ∈ 𝓤 α ∧ SetRel.IsSymm s) id :=
  hasBasis_self.2 fun t t_in =>
    ⟨SetRel.symmetrize t, symmetrize_mem_uniformity t_in, inferInstance,
      SetRel.symmetrize_subset_self⟩

theorem uniformity_lift_le_swap {g : SetRel α α → Filter β} {f : Filter β} (hg : Monotone g)
    (h : ((𝓤 α).lift fun s => g (preimage Prod.swap s)) ≤ f) : (𝓤 α).lift g ≤ f :=
  calc
    (𝓤 α).lift g ≤ (Filter.map (@Prod.swap α α) <| 𝓤 α).lift g :=
      lift_mono uniformity_le_symm le_rfl
    _ ≤ _ := by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h

theorem uniformity_lift_le_comp {f : SetRel α α → Filter β} (h : Monotone f) :
    ((𝓤 α).lift fun s => f (s ○ s)) ≤ (𝓤 α).lift f :=
  calc
    ((𝓤 α).lift fun s => f (s ○ s)) = ((𝓤 α).lift' fun s : SetRel α α => s ○ s).lift f := by
      rw [lift_lift'_assoc]
      · exact monotone_id.relComp monotone_id
      · exact h
    _ ≤ (𝓤 α).lift f := lift_mono comp_le_uniformity le_rfl

theorem comp3_mem_uniformity {s : SetRel α α} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ (t ○ t) ⊆ s :=
  let ⟨_t', ht', ht's⟩ := comp_mem_uniformity_sets hs
  let ⟨t, ht, htt'⟩ := comp_mem_uniformity_sets ht'
  have := isRefl_of_mem_uniformity ht
  ⟨t, ht, (SetRel.comp_subset_comp (SetRel.left_subset_comp.trans htt') htt').trans ht's⟩

/-- See also `comp3_mem_uniformity`. -/
theorem comp_le_uniformity3 : ((𝓤 α).lift' fun s : SetRel α α => s ○ (s ○ s)) ≤ 𝓤 α := fun _ h =>
  let ⟨_t, htU, ht⟩ := comp3_mem_uniformity h
  mem_of_superset (mem_lift' htU) ht

/-- See also `comp_open_symm_mem_uniformity_sets`. -/
theorem comp_symm_mem_uniformity_sets {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SetRel.IsSymm t ∧ t ○ t ⊆ s := by
  obtain ⟨w, w_in, w_sub⟩ : ∃ w ∈ 𝓤 α, w ○ w ⊆ s := comp_mem_uniformity_sets hs
  use SetRel.symmetrize w, symmetrize_mem_uniformity w_in, inferInstance
  have : SetRel.symmetrize w ⊆ w := SetRel.symmetrize_subset_self
  calc SetRel.symmetrize w ○ SetRel.symmetrize w
    _ ⊆ w ○ w := by gcongr
    _ ⊆ s := w_sub

theorem subset_comp_self_of_mem_uniformity {s : SetRel α α} (h : s ∈ 𝓤 α) : s ⊆ s ○ s :=
  have := isRefl_of_mem_uniformity h; SetRel.left_subset_comp

theorem comp_comp_symm_mem_uniformity_sets {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SetRel.IsSymm t ∧ t ○ t ○ t ⊆ s := by
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

lemma mem_ball_self (x : α) {V : SetRel α α} : V ∈ 𝓤 α → x ∈ ball x V := refl_mem_uniformity

/-- The triangle inequality for `UniformSpace.ball` -/
theorem mem_ball_comp {V W : Set (β × β)} {x y z} (h : y ∈ ball x V) (h' : z ∈ ball y W) :
    z ∈ ball x (V ○ W) :=
  SetRel.prodMk_mem_comp h h'

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

theorem ball_iInter {x : β} {V : ι → Set (β × β)} : ball x (⋂ i, V i) = ⋂ i, ball x (V i) :=
  preimage_iInter

theorem mem_ball_symmetry {V : SetRel β β} [V.IsSymm] {x y} : x ∈ ball y V ↔ y ∈ ball x V := V.comm

theorem ball_eq_of_symmetry {V : SetRel β β} [V.IsSymm] {x} : ball x V = { y | (y, x) ∈ V } := by
  ext y
  rw [mem_ball_symmetry]
  exact Iff.rfl

theorem mem_comp_of_mem_ball {V W : SetRel β β} {x y z : β} [V.IsSymm] (hx : x ∈ ball z V)
    (hy : y ∈ ball z W) : (x, y) ∈ V ○ W := by
  rw [mem_ball_symmetry] at hx
  exact ⟨z, hx, hy⟩

theorem mem_comp_comp {V W M : SetRel β β} [W.IsSymm] {p : β × β} :
    p ∈ V ○ M ○ W ↔ (ball p.1 V ×ˢ ball p.2 W ∩ M).Nonempty := by
  obtain ⟨x, y⟩ := p
  constructor
  · rintro ⟨z, ⟨w, hpw, hwz⟩, hzy⟩
    exact ⟨(w, z), ⟨hpw, by rwa [mem_ball_symmetry]⟩, hwz⟩
  · rintro ⟨⟨w, z⟩, ⟨w_in, z_in⟩, hwz⟩
    rw [mem_ball_symmetry] at z_in
    exact ⟨z, ⟨w, w_in, hwz⟩, z_in⟩

lemma isCover_iff_subset_iUnion_ball {U : SetRel β β} [U.IsSymm] {s N : Set β} :
    U.IsCover s N ↔ s ⊆ ⋃ y ∈ N, ball y U := by
  simp [SetRel.IsCover, subset_def, ball, U.comm]

alias ⟨_root_.SetRel.IsCover.subset_iUnion_ball, _root_.SetRel.IsCover.of_subset_iUnion_ball⟩ :=
  isCover_iff_subset_iUnion_ball

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

theorem nhds_basis_uniformity' {p : ι → Prop} {s : ι → SetRel α α} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => ball x (s i) := by
  rw [nhds_eq_comap_uniformity]
  exact h.comap (Prod.mk x)

theorem nhds_basis_uniformity {p : ι → Prop} {s : ι → SetRel α α} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => { y | (y, x) ∈ s i } := by
  replace h := h.comap Prod.swap
  rw [comap_swap_uniformity] at h
  exact nhds_basis_uniformity' h

theorem nhds_eq_comap_uniformity' {x : α} : 𝓝 x = (𝓤 α).comap fun y => (y, x) :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_of_same_basis <| (𝓤 α).basis_sets.comap _

theorem UniformSpace.mem_nhds_iff {x : α} {s : Set α} : s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, ball x V ⊆ s := by
  rw [nhds_eq_comap_uniformity, mem_comap]
  simp_rw [ball]

theorem UniformSpace.ball_mem_nhds (x : α) ⦃V : SetRel α α⦄ (V_in : V ∈ 𝓤 α) : ball x V ∈ 𝓝 x := by
  rw [UniformSpace.mem_nhds_iff]
  exact ⟨V, V_in, Subset.rfl⟩

theorem UniformSpace.ball_mem_nhdsWithin {x : α} {S : Set α} ⦃V : SetRel α α⦄ (x_in : x ∈ S)
    (V_in : V ∈ 𝓤 α ⊓ 𝓟 (S ×ˢ S)) : ball x V ∈ 𝓝[S] x := by
  rw [nhdsWithin_eq_comap_uniformity_of_mem x_in, mem_comap]
  exact ⟨V, V_in, Subset.rfl⟩

theorem UniformSpace.mem_nhds_iff_symm {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, SetRel.IsSymm V ∧ ball x V ⊆ s := by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    use SetRel.symmetrize V, symmetrize_mem_uniformity V_in, inferInstance
    exact Subset.trans (ball_mono SetRel.symmetrize_subset_self x) V_sub
  · rintro ⟨V, V_in, _, V_sub⟩
    exact ⟨V, V_in, V_sub⟩

theorem UniformSpace.hasBasis_nhds (x : α) :
    HasBasis (𝓝 x) (fun s : SetRel α α => s ∈ 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s :=
  ⟨fun t => by simp [UniformSpace.mem_nhds_iff_symm, and_assoc]⟩

open UniformSpace

theorem UniformSpace.mem_closure_iff_symm_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → SetRel.IsSymm V → (s ∩ ball x V).Nonempty := by
  simp [mem_closure_iff_nhds_basis (hasBasis_nhds x), Set.Nonempty]

theorem UniformSpace.mem_closure_iff_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → (ball x V ∩ s).Nonempty := by
  simp [mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (𝓤 α).basis_sets)]

theorem UniformSpace.closure_subset_preimage
    {U : SetRel α α} (hU : U ∈ 𝓤 α) (s : Set α) : closure s ⊆ U.preimage s := by
  intro x hx
  obtain ⟨y, hxy, hy⟩ := mem_closure_iff_ball.mp hx hU
  exact ⟨y, hy, hxy⟩

theorem UniformSpace.closure_subset_image
    {U : SetRel α α} (hU : U ∈ 𝓤 α) (s : Set α) : closure s ⊆ U.image s :=
  closure_subset_preimage (symm_le_uniformity hU) s

theorem nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball x) :=
  (nhds_basis_uniformity' (𝓤 α).basis_sets).eq_biInf

theorem nhds_eq_uniformity' {x : α} : 𝓝 x = (𝓤 α).lift' fun s => { y | (y, x) ∈ s } :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_biInf

theorem mem_nhds_left (x : α) {s : SetRel α α} (h : s ∈ 𝓤 α) : { y : α | (x, y) ∈ s } ∈ 𝓝 x :=
  ball_mem_nhds x h

theorem mem_nhds_right (y : α) {s : SetRel α α} (h : s ∈ 𝓤 α) : { x : α | (x, y) ∈ s } ∈ 𝓝 y :=
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
    (𝓝 x).lift g = (𝓤 α).lift fun s : SetRel α α => g (ball x s) := by
  rw [nhds_eq_comap_uniformity, comap_lift_eq2 hg]
  simp_rw [ball, Function.comp_def]

theorem lift_nhds_right {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : SetRel α α => g { y | (y, x) ∈ s } := by
  rw [nhds_eq_comap_uniformity', comap_lift_eq2 hg]
  simp_rw [Function.comp_def, preimage]

theorem nhds_nhds_eq_uniformity_uniformity_prod {a b : α} :
    𝓝 a ×ˢ 𝓝 b = (𝓤 α).lift fun s : SetRel α α =>
      (𝓤 α).lift' fun t => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ t } := by
  rw [nhds_eq_uniformity', nhds_eq_uniformity, prod_lift'_lift']
  exacts [rfl, monotone_preimage, monotone_preimage]

theorem Filter.HasBasis.biInter_biUnion_ball {p : ι → Prop} {U : ι → SetRel α α}
    (h : HasBasis (𝓤 α) p U) (s : Set α) :
    (⋂ (i) (_ : p i), ⋃ x ∈ s, ball x (U i)) = closure s := by
  ext x
  simp [mem_closure_iff_nhds_basis (nhds_basis_uniformity h), ball]

/-! ### Uniform continuity -/

variable [UniformSpace β]

/-- A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `α`. -/
def UniformContinuous (f : α → β) :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α) (𝓤 β)

/-- Notation for uniform continuity with respect to non-standard `UniformSpace` instances. -/
scoped[Uniformity] notation "UniformContinuous[" u₁ ", " u₂ "]" => @UniformContinuous _ _ u₁ u₂

/-- A function `f : α → β` is *uniformly continuous* on `s : Set α` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s ×ˢ s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`. -/
def UniformContinuousOn (f : α → β) (s : Set α) : Prop :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 β)

theorem uniformContinuous_def {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, { x : α × α | (f x.1, f x.2) ∈ r } ∈ 𝓤 α :=
  Iff.rfl

theorem uniformContinuous_iff_eventually {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, ∀ᶠ x : α × α in 𝓤 α, (f x.1, f x.2) ∈ r :=
  Iff.rfl

theorem uniformContinuousOn_univ {f : α → β} :
    UniformContinuousOn f univ ↔ UniformContinuous f := by
  rw [UniformContinuousOn, UniformContinuous, univ_prod_univ, principal_univ, inf_top_eq]

theorem uniformContinuous_of_const {c : α → β} (h : ∀ a b, c a = c b) :
    UniformContinuous c :=
  have : (fun x : α × α => (c x.fst, c x.snd)) ⁻¹' SetRel.id = univ :=
    eq_univ_iff_forall.2 fun ⟨a, b⟩ => h a b
  le_trans (map_le_iff_le_comap.2 <| by simp [comap_principal, this]) refl_le_uniformity

theorem uniformContinuous_id : UniformContinuous (@id α) := tendsto_id

theorem uniformContinuous_const {b : β} : UniformContinuous fun _ : α => b :=
  uniformContinuous_of_const fun _ _ => rfl

nonrec theorem UniformContinuous.comp [UniformSpace γ] {g : β → γ} {f : α → β}
    (hg : UniformContinuous g) (hf : UniformContinuous f) : UniformContinuous (g ∘ f) :=
  hg.comp hf

/-- If a function `T` is uniformly continuous in a uniform space `β`,
then its `n`-th iterate `T^[n]` is also uniformly continuous. -/
theorem UniformContinuous.iterate (T : β → β) (n : ℕ) (h : UniformContinuous T) :
    UniformContinuous T^[n] := by
  induction n with
  | zero => exact uniformContinuous_id
  | succ n hn => exact Function.iterate_succ _ _ ▸ UniformContinuous.comp hn h

theorem Filter.HasBasis.uniformContinuous_iff {ι'} {p : ι → Prop}
    {s : ι → SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι' → Prop} {t : ι' → Set (β × β)}
    (hb : (𝓤 β).HasBasis q t) {f : α → β} :
    UniformContinuous f ↔ ∀ i, q i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ t i :=
  (ha.tendsto_iff hb).trans <| by simp only [Prod.forall]

theorem Filter.HasBasis.uniformContinuousOn_iff {ι'} {p : ι → Prop}
    {s : ι → SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι' → Prop} {t : ι' → Set (β × β)}
    (hb : (𝓤 β).HasBasis q t) {f : α → β} {S : Set α} :
    UniformContinuousOn f S ↔
      ∀ i, q i → ∃ j, p j ∧ ∀ x, x ∈ S → ∀ y, y ∈ S → (x, y) ∈ s j → (f x, f y) ∈ t i :=
  ((ha.inf_principal (S ×ˢ S)).tendsto_iff hb).trans <| by
    simp_rw [Prod.forall, Set.inter_comm (s _), forall_mem_comm, mem_inter_iff, mem_prod, and_imp]

/-- A map `f : α → β` between uniform spaces is called *uniform inducing* if the uniformity filter
on `α` is the pullback of the uniformity filter on `β` under `Prod.map f f`. If `α` is a separated
space, then this implies that `f` is injective, hence it is a `IsUniformEmbedding`. -/
@[mk_iff]
structure IsUniformInducing (f : α → β) : Prop where
  /-- The uniformity filter on the domain is the pullback of the uniformity filter on the codomain
  under `Prod.map f f`. -/
  comap_uniformity : comap (fun x : α × α ↦ (f x.1, f x.2)) (𝓤 β) = 𝓤 α

/-- A map `f : α → β` between uniform spaces is a *uniform embedding* if it is uniform inducing and
injective. If `α` is a separated space, then the latter assumption follows from the former. -/
@[mk_iff]
structure IsUniformEmbedding (f : α → β) : Prop extends IsUniformInducing f where
  /-- A uniform embedding is injective. -/
  injective : Function.Injective f

lemma IsUniformEmbedding.isUniformInducing {f : α → β} (hf : IsUniformEmbedding f) :
    IsUniformInducing f :=
  hf.toIsUniformInducing

end UniformSpace

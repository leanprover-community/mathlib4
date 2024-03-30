/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Topology.Bases
import Mathlib.Order.Filter.CardinalInter
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Metrizable.Basic
/-!
# K-Lindelöf sets and k-Lindelöf spaces

## Main definitions

We define the following properties for sets in a topological space:

* `IsKLindelof k s`: Two definitions are possible here. The more standard definition is that
every open cover that contains `s` contains a subcover of cardinality less than `k`.
We choose for the equivalent definition where we require that every nontrivial CardinalInterFilter
with cardinality `k` has a clusterpoint.
Equivalence is established in `isKLindelof_iff_cardinal_subcover`.
* `KLindelofSpace X`: `X` is k-Lindelöf if it is k-Lindelöf as a set.
* `NonKLindelofSpace`: a space that is not a k-Lindëlof space, e.g. the Long Line.

## Main results

* `isKLindelof_iff_cardinal_subcover`: A set is Lindelöf iff every open cover has a
  countable subcover.

## Implementation details

* This API is mainly based on the API for IsCompact and IsLindelöf and follows notation and style as
 much as possible.
-/
open Set Filter Topology TopologicalSpace Cardinal


universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}
variable {k : Cardinal}

section KLindelof

/-- A set `s` is k-Lindelöf if every nontrivial `CardinalInterFilter f k` that contains `s`,
  has a clusterpoint in `s`. The filter-free definition is given by
  `isKLindelof_iff_cardinal_subcover`. -/
def IsKLindelof (k : Cardinal) (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f] [CardinalInterFilter f k], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f

/-- The complement to a k-Lindelöf set belongs to a `CardinalInterFilter f k` if it belongs to each
filter `𝓝 x ⊓ f`, `x ∈ s`. -/
theorem IsKLindelof.compl_mem_sets (hs : IsKLindelof k s) {f : Filter X}
    [CardinalInterFilter f k] (hf : ∀ x ∈ s, sᶜ ∈ 𝓝 x ⊓ f) : sᶜ ∈ f := by
  contrapose! hf
  simp only [not_mem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact hs inf_le_right

/-- The complement to a k-Lindelöf set belongs to a `CardinalInterFilter f k` if each `x ∈ s` has a
neighborhood `t` within `s` such that `tᶜ` belongs to `f`. -/
theorem IsKLindelof.compl_mem_sets_of_nhdsWithin (hs : IsKLindelof k s)
    {f : Filter X} [CardinalInterFilter f k] (hf : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, tᶜ ∈ f) : sᶜ ∈ f := by
  refine hs.compl_mem_sets fun x hx ↦ ?_
  rw [← disjoint_principal_right, disjoint_right_comm, (basis_sets _).disjoint_iff_left]
  exact hf x hx

/-- If `p : Set X → Prop` is stable under restriction and union, and each point `x`
  of a k-Lindelöf set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_elim]
theorem IsKLindelof.induction_on {hk : 2 < k} (hs : IsKLindelof k s) {p : Set X → Prop}
    (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s)
    (hcardinal_union : ∀ (S : Set (Set X)), (#S < k) → (∀ s ∈ S, p s) → p (⋃₀ S))
    (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) : p s := by
  let f : Filter X := ofCardinalUnion p hk hcardinal_union (fun t ht _ hsub ↦ hmono hsub ht)
  have : sᶜ ∈ f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using hnhds)
  rwa [← compl_compl s]

/-- The intersection of a k-Lindelöf set and a closed set is a k-Lindelöf set. -/
theorem IsKLindelof.inter_right (hs : IsKLindelof k s) (ht : IsClosed t) :
    IsKLindelof k (s ∩ t) := by
  intro f hnf _ hstf
  rw [← inf_principal, le_inf_iff] at hstf
  obtain ⟨x, hsx, hx⟩ : ∃ x ∈ s, ClusterPt x f := hs hstf.1
  have hxt : x ∈ t := ht.mem_of_nhdsWithin_neBot <| hx.mono hstf.2
  exact ⟨x, ⟨hsx, hxt⟩, hx⟩

  /-- The intersection of a closed set and a k-Lindelöf set is a k-Lindelöf set. -/
theorem IsKLindelof.inter_left (ht : IsKLindelof k t) (hs : IsClosed s) : IsKLindelof k (s ∩ t) :=
  inter_comm t s ▸ ht.inter_right hs

  /-- The set difference of a k-Lindelöf set and an open set is a k-Lindelöf set. -/
theorem IsLindelof.diff (hs : IsKLindelof k s) (ht : IsOpen t) : IsKLindelof k (s \ t) :=
  hs.inter_right (isClosed_compl_iff.mpr ht)

/-- A closed subset of a k-Lindelöf set is a k-Lindelöf set. -/
theorem IsLindelof.of_isClosed_subset (hs : IsKLindelof k s) (ht : IsClosed t) (h : t ⊆ s) :
    IsKLindelof k t := inter_eq_self_of_subset_right h ▸ hs.inter_right ht

/-- Commented sections have a universe problem.
A continuous image of a k-Lindelöf set is a k-Lindelöf set.
theorem IsKLindelof.image_of_continuousOn {f : X → Y} (hs : IsKLindelof k s)
    (hf : ContinuousOn f s) : IsKLindelof (X := Y) k (f '' s) := by
  intro l lne _ ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this _ inf_le_right
  haveI := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot

-- A continuous image of a k-Lindelöf set is a k-Lindelöf set within the codomain.
theorem IsKLindelof.image {f : X → Y} (hs : IsKLindelof k s) (hf : Continuous f) :
    IsKLindelof (X := Y) k (f '' s) := hs.image_of_continuousOn hf.continuousOn -/

-- A filter with the countable intersection property that is finer than the principal filter on
-- a k-Lindelöf set `s` contains any open set that contains all clusterpoints of `s`.
theorem IsKLindelof.adherence_nhdset {f : Filter X} [CardinalInterFilter f k] (hs : IsKLindelof k s)
    (hf₂ : f ≤ 𝓟 s) (ht₁ : IsOpen t) (ht₂ : ∀ x ∈ s, ClusterPt x f → x ∈ t) : t ∈ f :=
  (eq_or_neBot _).casesOn mem_of_eq_bot fun _ ↦
    let ⟨x, hx, hfx⟩ := @hs (f ⊓ 𝓟 tᶜ) _ _ <| inf_le_of_left_le hf₂
    have : x ∈ t := ht₂ x hx hfx.of_inf_left
    have : tᶜ ∩ t ∈ 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (ht₁.mem_nhds this)
    have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 <| compl_inter_self t ▸ this
    have : 𝓝[tᶜ] x ≠ ⊥ := hfx.of_inf_right.ne
    absurd A this

/--
Universe Problem!
For every open cover of a k-Lindelöf set, there exists a subcover with cardinality less
than `k`.
theorem IsKLindelof.elim_cardinal_subcover {ι : Type u} (hreg : Cardinal.IsRegular k) {hk : 2 < k}
    (hs : IsKLindelof k s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) :
    ∃ r : Set ι, (#r < k) ∧ (s ⊆ ⋃ i ∈ r, U i) := by
  have hmono : ∀ ⦃s t : Set X⦄, s ⊆ t → (∃ r : Set ι, (#r < k) ∧ t ⊆ ⋃ i ∈ r, U i)
      → (∃ r : Set ι, (#r < k) ∧ s ⊆ ⋃ i ∈ r, U i) := by
    intro s t hst ⟨r, ⟨hrcardinal, hsub⟩⟩
    exact ⟨r, hrcardinal, Subset.trans hst hsub⟩
  have hcardinal_union : ∀ (S : Set (Set X)), (#S < k)
      → (∀ s ∈ S, ∃ r : Set ι, (#r < k) ∧ (s ⊆ ⋃ i ∈ r, U i))
      → ∃ r : Set ι, (#r < k) ∧ (⋃₀ S ⊆ ⋃ i ∈ r, U i) := by
    intro S hS hsr
    choose! r hr using hsr
    refine ⟨⋃ s ∈ S, r s, ?_, ?_⟩
    · rw [Cardinal.biUnion_iff hreg]
      exact fun a ha ↦ (hr a ha).1
      exact hS
    refine sUnion_subset ?h.right.h
    simp only [mem_iUnion, exists_prop, iUnion_exists, biUnion_and']
    exact fun i is x hx ↦ mem_biUnion is ((hr i is).2 hx)
  have h_nhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∃ r : Set ι, (#r < k) ∧ (t ⊆ ⋃ i ∈ r, U i) := by
    intro x hx
    let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
    have : 1 < k := IsRegular.nat_lt hreg 1
    refine ⟨U i, mem_nhdsWithin_of_mem_nhds ((hUo i).mem_nhds hi), {i}, by simp [this], ?_⟩
    simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
    exact subset_rfl
  exact hs.induction_on hmono hcardinal_union h_nhds -/

/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-! # Linear topologies on rings

Following Bourbaki, *Algebra II*, chapter 4, §2, n° 3, a topology on a ring `R` is *linear* if
it is invariant by translation and there admits a basis of neighborhoods of 0 consisting of
two-sided ideals.

Reflecting the discrepancy between `Filter.IsBasis` and `RingFilterBasis`, there are two ways to get
this basis of neighborhoods, either via a `Set (Ideal R)`, or via a function `ι → Ideal R`.

- `IdealBasis R` is a structure that records a `Set (Ideal R)` and asserts that
it defines a basis of neighborhoods of `0` for *some* topology.

- `Ideal.IsBasis B`, for `B : ι → Ideal R`, is the structure that records
that the range of `B` defines a basis of neighborhoods of `0` for *some* topology on `R`.

- `Ideal.IsBasis.toRingFilterBasis` converts an `Ideal.IsBasis` to a `RingFilterBasis`.

- `Ideal.IsBasis.topology` defines the associated topology.

- `Ideal.IsBasis.topologicalRing`: an `Ideal.IsBasis` defines a topological ring.

- `Ideal.IsBasis.toIdealBasis` and `IdealBasis.toIsBasis` convert one structure to another.

- `IdealBasis.toIsBasis.IdealBasis.toIsBasis.toIdealBasis_eq` proves the identity
`B.toIsBasis.toIdealBasis = B`.

- `Ideal.IsBasis.ofIdealBasis_topology_eq` proves that the topologies coincide.

- For `Ring R` and `TopologicalSpace R`, the type class `LinearTopology R` asserts that the
topology on `R` is linear.

- `LinearTopology.topologicalRing`: instance showing that then the ring is a topological ring.

- `LinearTopology.tendsto_zero_mul`: for `f, g : ι → R` such that `f i` converges to `0`,
`f i * g i` converges to `0`.

-/

section Definitions

variable (α : Type*) [Ring α]

/-- `IdealBasis α` is a structure that furnishes a filter basis of left- and right-ideals -/
structure IdealBasis where
  /-- Ideals of a filter basis. -/
  sets : Set (Ideal α)
  /-- The set of filter basis ideals is nonempty. -/
  nonempty : sets.Nonempty
  /-- The set of filter basis ideals is directed downwards. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ≤ x ⊓ y
  /-- Ideals in sets are right ideals. -/
  mul_right {x} {a b : α} : x ∈ sets → a ∈ x → a * b ∈ x

instance IdealBasis.setLike : SetLike (IdealBasis α) (Ideal α) where
  coe := fun B ↦ B.sets
  coe_injective' := fun B B' h ↦ by cases B; cases B'; congr

/-- Define an `IdealBasis` on a `CommRing`-/
def IdealBasis.ofComm {α : Type*} [CommRing α] (B : Set (Ideal α)) (nonempty : Set.Nonempty B)
    (inter : ∀ {i j}, i ∈ B → j ∈ B → ∃ k ∈ B, k ≤ i ⊓ j) : IdealBasis α where
  sets := B
  inter_sets := inter
  nonempty := nonempty
  mul_right {i a b} _ ha := mul_comm a b ▸ Ideal.mul_mem_left i b ha

variable {α}

variable {ι : Sort*} (B : ι → Ideal α)

/-- `Ideal.IsBasis B` means that the image of `B` is a filter basis consisting
of left- and right-ideals. -/
structure Ideal.IsBasis  : Prop where
  /-- There is an `i : ι`. -/
  nonempty : Nonempty ι
  /-- Every intersection of ideals in `B` contains an ideal in `B`. -/
  inter : ∀ (i j : ι), ∃ (k : ι), B k ≤ B i ⊓ B j
  /-- Every ideal in `B` is a right ideal. -/
  mul_right : ∀ i {a} r, a ∈ B i → a * r ∈ B i

/-- Define an `Ideal.IsBasis` on a `CommRing`. -/
lemma Ideal.IsBasis.ofComm {α : Type*} [CommRing α] {ι : Type*} [Nonempty ι] {B : ι → Ideal α}
    (inter : ∀ (i j), ∃ k, B k ≤ B i ⊓ B j) : Ideal.IsBasis B :=
  { inter
    nonempty := inferInstance
    mul_right := fun i a r h => mul_comm a r ▸ Ideal.mul_mem_left (B i) r h }

variable {B} in
/-- The `IdealBasis` associated with an `Ideal.IsBasis` -/
def Ideal.IsBasis.toIdealBasis (hB : Ideal.IsBasis B) : IdealBasis α where
  sets := Set.range B
  nonempty := Set.range_nonempty (h := hB.nonempty) _
  inter_sets {x y} := by
    rintro ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    exact ⟨B k,  Exists.intro k rfl, hk⟩
  mul_right {x a b} hx ha := by
    obtain ⟨i, rfl⟩ := hx
    exact hB.mul_right i b ha

/-- An `Ideal.IsBasis` associated with an `IdealBasis` -/
theorem IdealBasis.toIsBasis (B : IdealBasis α) :
    Ideal.IsBasis (ι := B.sets) (fun x => (x : Ideal α)) where
  nonempty := Set.nonempty_coe_sort.mpr B.nonempty
  inter := fun s t ↦ by
    obtain ⟨u, hu, hu'⟩ := B.inter_sets s.prop t.prop
    use ⟨u, hu⟩
  mul_right := fun s {a} r has ↦ B.mul_right (Subtype.coe_prop s) has

theorem IdealBasis.toIsBasis.toIdealBasis_eq (B : IdealBasis α) :
    B.toIsBasis.toIdealBasis = B := by
  unfold IdealBasis.toIsBasis Ideal.IsBasis.toIdealBasis
  simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq]

end Definitions
namespace Ideal.IsBasis

variable {α : Type*} [Ring α] {ι : Type*} {B : ι → Ideal α}

/-- An `Ideal.IsBasis` is a `RingSubgroupsBasis`. -/
lemma toRingSubgroupsBasis (hB : Ideal.IsBasis B) :
    RingSubgroupsBasis fun i => (B i).toAddSubgroup where
  inter := hB.inter
  mul i := ⟨i, fun u => by
    rintro ⟨x, _, _, hy, rfl⟩
    exact Ideal.mul_mem_left _ _ hy⟩
  leftMul a i := ⟨i, fun x hx => Ideal.mul_mem_left _ _ hx⟩
  rightMul a i := ⟨i, fun y hy =>  hB.mul_right _ _ hy⟩

/-- An `Ideal.IsBasis` is a `RingFilterBasis`. -/
def toRingFilterBasis (hB : Ideal.IsBasis B) :=
  let _: Nonempty ι := hB.nonempty
  hB.toRingSubgroupsBasis.toRingFilterBasis

/-- The topology generated by an `Ideal.IsBasis`. -/
def topology (hB : Ideal.IsBasis B) :
    TopologicalSpace α :=
  (toRingFilterBasis hB).topology

theorem mem_nhds_zero_iff (hB : Ideal.IsBasis B) (s : Set α) :
    (s ∈ @nhds _ hB.topology 0) ↔
    (∃ i, ((B i : Set α) ∈ @nhds _ hB.topology 0) ∧ (B i : Set α) ⊆ s) := by
  simp only [AddGroupFilterBasis.nhds_eq, AddGroupFilterBasis.N_zero,
    Filter.IsBasis.mem_filter_iff, FilterBasis.mem_filter_iff]
  constructor
  · rintro ⟨t, ⟨i, rfl⟩, hts⟩
    simp only [Submodule.coe_toAddSubgroup] at hts
    exact ⟨i, ⟨B i, ⟨i, rfl⟩, subset_of_eq rfl⟩, hts⟩
  · rintro ⟨i, _, his⟩
    use B i, ⟨i, rfl⟩, his

/-- A ring `α` with the topology generated by an `Ideal.IsBasis` is a topological ring. -/
theorem topologicalRing (hB : Ideal.IsBasis B) :
    @TopologicalRing α hB.topology _ :=
  hB.toRingFilterBasis.isTopologicalRing

theorem ofIdealBasis_topology_eq (hB : Ideal.IsBasis B) :
    (hB.toIdealBasis.toIsBasis).topology = hB.topology := by
  rw [TopologicalSpace.ext_iff_nhds]
  intro a
  simp only [AddGroupFilterBasis.nhds_eq, AddGroupFilterBasis.N]
  apply congr_arg₂ _ rfl
  -- Now we have to prove that both filter bases (sets vs families) coincide
  ext s
  simp only [FilterBasis.mem_filter_iff]
  constructor
  · rintro ⟨u, ⟨⟨v, ⟨i, rfl⟩⟩, rfl⟩, hus⟩
    simp only [Submodule.coe_toAddSubgroup] at hus
    exact ⟨B i, ⟨i, rfl⟩, hus⟩
  · rintro ⟨u, ⟨i, rfl⟩, hus⟩
    simp only [Submodule.coe_toAddSubgroup] at hus
    refine ⟨B i, ⟨⟨B i, ⟨i, rfl⟩⟩, rfl⟩, hus⟩

end Ideal.IsBasis

namespace IdealBasis

variable {α : Type*} [Ring α]

theorem mem_nhds_zero_iff (B : IdealBasis α) (s : Set α) :
    (s ∈ @nhds _ B.toIsBasis.topology 0) ↔
    ∃ i ∈ B.sets, (i : Set α) ∈ @nhds _ B.toIsBasis.topology 0 ∧ i ≤ s := by
  rw [Ideal.IsBasis.mem_nhds_zero_iff]
  simp only [Subtype.exists, exists_and_left, exists_prop, Set.le_eq_subset]
  constructor
  · rintro ⟨a, mem_nhds, mem_sets, subset_s⟩
    exact ⟨a, mem_sets, mem_nhds, subset_s⟩
  · rintro ⟨i, hi, mem_nhds, subset_s⟩
    exact ⟨i, mem_nhds, hi, subset_s⟩

end IdealBasis

universe u

section LinearTopology

variable (α : Type u) [Ring α]

/-- A topology on a ring is linear if its topology is defined by a family of ideals. -/
class LinearTopology [τ : TopologicalSpace α]
    extends IdealBasis α where
  isTopology :  τ = toIdealBasis.toIsBasis.topology

/-- If the topology of a ring is linear, then it makes the ring a topological ring. -/
instance [TopologicalSpace α] [hLT : LinearTopology α] :
  TopologicalRing α  :=
  hLT.isTopology ▸ (Ideal.IsBasis.topologicalRing hLT.toIdealBasis.toIsBasis)

namespace LinearTopology

theorem mem_nhds_zero_iff [TopologicalSpace α] [hL : LinearTopology α] (s : Set α) :
    (s ∈ nhds 0) ↔ ∃ i ∈ hL.sets, (i : Set α) ∈ nhds 0 ∧ i ≤ s := by
  rw [TopologicalSpace.ext_iff_nhds.mp hL.isTopology, hL.toIdealBasis.mem_nhds_zero_iff]

theorem tendsto_zero_mul [TopologicalSpace α] [LinearTopology α] {ι : Type*} {f : Filter ι}
    (a b : ι → α) (hb : Filter.Tendsto b f (nhds 0)) :
    Filter.Tendsto (a * b) f (nhds 0) := by
  intro v hv
  obtain ⟨I, _, I_mem, I_le⟩ := (LinearTopology.mem_nhds_zero_iff _ _).mp hv
  apply Filter.sets_of_superset _ _ I_le
  simp only [Filter.mem_sets, Filter.mem_map]
  rw [Filter.tendsto_def] at hb
  exact Filter.sets_of_superset _ (hb _ I_mem) (fun x hx ↦ Ideal.mul_mem_left _ _ hx)

end LinearTopology

end LinearTopology

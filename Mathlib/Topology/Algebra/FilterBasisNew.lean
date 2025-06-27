/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker
-/
import Mathlib.Order.Filter.Bases.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
**WARNING** : This is a new version of `Topology.Algebra.FilterBasis`, which is still used
by the library at this point in time. The library will be gradually modified to use this file
instead. See `https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Refactoring.20algebraic.20filter.20bases/near/479437345`
for more details.

# Algebraic filter bases

We know that the topology of a topological group (or ring, or module) is invariant by
translations, hence it is completely described by its filter of neighborhoods at the
neutral element (`1` for groups, `0` for additive groups, rings and modules).
In this file, we completely characterize the filter bases which can be obtained as bases of
neighborhoods of the neutral element for some group (or ring, or module) topology.

More precisely, for `X` in `{Group, AddGroup, Ring, Module}`, we provide :
* `Filter.IsXBasis p s`: a strenghtening of `Filter.IsBasis` with compatibility conditions with the
  algebraic structure.
* `Filter.IsXBasis.mk_of_comm`: simpler contructors in the commutative setting.
* `Filter.HasBasis.isXBasis`: in a topological `X`, *any* basis of neighborhoods
  of the neutral element satisfies `Filter.IsXBasis`.
* `Filter.IsXBasis.topologicalX_of_hasBasis`: if some `X` comes *equipped* with a topology and
  a basis of neighborhoods of the neutral element satisfies `Filter.IsXBasis`, then that topology is
  a `X` topology. This requires the topology to be invariant by translation.
* `Filter.IsXBasis.topology`: the topological structure associated to some `X` filter basis.
* `Filter.IsXBasis.topologicalX`: the topology associated to some `X` filter basis is indeed
  an `X` topology.

Note the subtlety between `IsXBasis.topologicalX_of_hasBasis`, useful for *proving* that some
topology is compatible with the algebraic structure, and `IsXBasis.topologicalX` which shows
that *the* topology associated to some basis is compatible with the algebraic structure.
Mathematically this is the same thing, but having these variations is convenient.

Remark: for `X = Module`, we use `continuousSMul` instead of `topologicalModule` in the names.

## Usage indications

The results in this file are meant to be used for either
**proving some compatibility between topological and algebraic structures**
or **constructing some topology compatible with an algebraic structure**.

Thus, once you have all the relevant instances on your favorite type, you probably
don't want to use this file anymore.

## Implementation Notes

For a long time, the definitions in this file were built on top of `FilterBasis`.
We switched to `Filter.IsBasis` instead, because its API is much closer to
that of `Filter.HasBasis`, which is what we use most of the time (when we already
know the generated filter).

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]
-/

open Filter Set TopologicalSpace Function

open Topology Filter Pointwise

universe u

namespace Filter

/-!
## Filter bases for group topologies
-/

/-- Given a group `G`, `s : ι → Set G` and `p : ι → Prop`, `Filter.IsGroupBasis p s` is a
strengthening of `Filter.IsBasis p s` with extra compatibility axioms ensuring that the generated
filter is the filter of neighborhoods of one for some group topology on `G`
(`Filter.IsGroupBasis.topologicalGroup`). Conversely, *any* basis of neighborhoods of one
in a topological group satisfies these conditions (`Filter.HasBasis.isGroupBasis`). -/
structure IsGroupBasis {G : Type*} {ι : Sort*} [Group G] (p : ι → Prop) (s : ι → Set G) : Prop
    extends IsBasis p s where
  one : ∀ {i}, p i → (1 : G) ∈ s i
  mul : ∀ {i}, p i → ∃ j, p j ∧ s j * s j ⊆ s i
  inv : ∀ {i}, p i → ∃ j, p j ∧ s j ⊆ (s i)⁻¹
  conj : ∀ x₀, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (x₀ * · * x₀⁻¹) (s j) (s i)

/-- Given an additive group `G`, `s : ι → Set G` and `p : ι → Prop`, `Filter.IsAddGroupBasis p s`
is a strengthening of `Filter.IsBasis p s` with extra compatibility axioms ensuring that the
generated filter is the filter of neighborhoods of zero for some group topology on `G`
(`Filter.IsAddGroupBasis.topologicalAddGroup`). Conversely, *any* basis of neighborhoods of
zero in an additive topological group satisfies these conditions
(`Filter.HasBasis.isAddGroupBasis`). -/
structure IsAddGroupBasis {G : Type*} {ι : Sort*} [AddGroup G] (p : ι → Prop) (s : ι → Set G) : Prop
    extends IsBasis p s where
  zero : ∀ {i}, p i → (0 : G) ∈ s i
  add : ∀ {i}, p i → ∃ j, p j ∧ s j + s j ⊆ s i
  neg : ∀ {i}, p i → ∃ j, p j ∧ s j ⊆ -(s i)
  conj : ∀ x₀, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (x₀ + · + -x₀) (s j) (s i)

attribute [to_additive existing] IsGroupBasis

/-- A constructor for `IsGroupBasis` in the commutative case. -/
@[to_additive "A constructor for `IsAddGroupBasis` in the commutative case."]
theorem IsGroupBasis.mk_of_comm {G : Type*} {ι : Sort*} [CommGroup G] (p : ι → Prop) (s : ι → Set G)
    (toIsBasis : IsBasis p s) (one : ∀ {i}, p i → (1 : G) ∈ s i)
    (mul : ∀ {i}, p i → ∃ j, p j ∧ s j * s j ⊆ s i)
    (inv : ∀ {i}, p i → ∃ j, p j ∧ s j ⊆ (s i)⁻¹) :
    IsGroupBasis p s where
  toIsBasis := toIsBasis
  one := one
  mul := mul
  inv := inv
  conj x i hi := ⟨i, hi, by simpa only [mul_inv_cancel_comm, preimage_id'] using mapsTo_id _⟩

/-- In a topological group, *any* basis of neighborhoods of one is a group filter
basis. -/
@[to_additive "In an additive topological group, *any* basis of neighborhoods of zero is a group
filter basis."]
theorem HasBasis.isGroupBasis {G : Type*} {ι : Sort*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {p : ι → Prop} {s : ι → Set G} (h : (𝓝 1).HasBasis p s) :
    IsGroupBasis p s where
  toIsBasis := h.isBasis
  one hi := mem_of_mem_nhds (h.mem_of_mem hi)
  mul := by
    have : Tendsto (fun p : G × G ↦ p.1 * p.2) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1) := by
      simpa only [nhds_prod_eq, one_mul] using (tendsto_mul (M := G) (a := 1) (b := 1))
    simpa [h.prod_self.tendsto_iff h, mul_subset_iff, forall_mem_comm] using this
  inv := by
    have : Tendsto (·⁻¹ : G → G) (𝓝 1) (𝓝 1) := by simpa using tendsto_inv (1 : G)
    rwa [h.tendsto_iff h] at this
  conj x₀ := by
    have : Tendsto (x₀ * · * x₀⁻¹ : G → G) (𝓝 1) (𝓝 1) := by simpa using
      (tendsto_id (x := 𝓝 1) |>.const_mul x₀ |>.mul_const x₀⁻¹)
    rwa [h.tendsto_iff h] at this

/-- The trivial group filter basis, inducing the discrete topology. -/
example {G : Type*} [Group G] :
    IsGroupBasis (fun _ ↦ True) (fun _ ↦ {1} : Unit → Set G) :=
  letI : TopologicalSpace G := ⊥
  haveI : DiscreteTopology G := ⟨rfl⟩
  -- TODO: this should be inferred
  haveI : IsTopologicalGroup G := ⟨⟩
  (nhds_discrete G ▸ hasBasis_pure 1).isGroupBasis

namespace IsGroupBasis

variable {G : Type*} {ι : Sort*} [Group G] {p : ι → Prop} {s : ι → Set G} (hB : IsGroupBasis p s)
include hB

/-!
### Proving `IsTopologicalGroup` from `Filter.IsGroupBasis`
-/

/-- Assume the group `G` is given a topology which is invariant by translations,
which we express as `ContinuousConstSMul G G`.
To show that it is a group topology, it suffices so exhibit a basis of neighborhoods of
one satisfying `Filter.IsGroupBasis`. -/
@[to_additive "Assume the group `G` is given a topology which is invariant by translations,
which we express as `ContinuousConstVAdd G G`.
To show that it is a group topology, it suffices so exhibit a basis of neighborhoods of
zero satisfying `Filter.IsAddGroupBasis`."]
lemma topologicalGroup_of_hasBasis [TopologicalSpace G] [ContinuousConstSMul G G]
    (hB' : (𝓝 1).HasBasis p s) : IsTopologicalGroup G := by
  apply IsTopologicalGroup.of_nhds_one
  · refine hB'.prod_self.tendsto_iff hB' |>.mpr fun i hi ↦ (hB.mul hi).imp
      fun j ⟨hj, hji⟩ ↦ ⟨hj, ?_⟩
    simpa [← image2_mul, forall_mem_comm] using hji
  · exact hB'.tendsto_iff hB' |>.mpr fun i hi ↦ (hB.inv hi).imp fun j ↦ id
  · intro x₀
    simp_rw [← smul_eq_mul, ← Homeomorph.smul_apply x₀, (Homeomorph.smul x₀).map_nhds_eq,
      Homeomorph.smul_apply x₀, smul_eq_mul, mul_one]
  · exact fun x₀ ↦ hB'.tendsto_iff hB' |>.mpr fun i hi ↦ (hB.conj x₀ hi).imp fun j ↦ id

/-!
### Constructing a group topology from `Filter.IsGroupBasis`
-/

/-- The topological space structure coming from a group filter basis. -/
@[to_additive "The topological space structure coming from an additive group filter basis."]
def topology : TopologicalSpace G :=
  TopologicalSpace.mkOfNhds (· • hB.filter)

@[to_additive]
theorem nhds_eq {x₀ : G} : @nhds G hB.topology x₀ = x₀ • hB.filter := by
  apply TopologicalSpace.nhds_mkOfNhds_of_hasBasis (fun x ↦ hB.hasBasis.map (x * ·))
  · intro a i hi
    exact ⟨1, hB.one hi, mul_one a⟩
  · intro a i hi
    rcases hB.mul hi with ⟨j, hj, hji⟩
    filter_upwards [hB.hasBasis.map _ |>.mem_of_mem hj]
    rintro _ ⟨x, hx, rfl⟩
    calc
      (a * x) • (s j) ∈ (a * x) • hB.filter := smul_set_mem_smul_filter (hB.hasBasis.mem_of_mem hj)
      _ = a • x • (s j) := smul_smul .. |>.symm
      _ ⊆ a • (s j * s j) := smul_set_mono <| smul_set_subset_smul hx
      _ ⊆ a • (s i) := smul_set_mono hji

@[to_additive]
theorem nhds_one_eq :
    @nhds G hB.topology (1 : G) = hB.filter := by
  rw [hB.nhds_eq, one_smul]

@[to_additive]
theorem nhds_hasBasis (x₀ : G) :
    HasBasis (@nhds G hB.topology x₀) p (fun i ↦ x₀ • (s i)) := by
  rw [hB.nhds_eq]
  apply hB.hasBasis.map _

@[to_additive]
theorem nhds_one_hasBasis :
    HasBasis (@nhds G hB.topology 1) p s := by
  rw [hB.nhds_one_eq]
  exact hB.hasBasis

@[to_additive]
theorem mem_nhds_one {i} (hi : p i) :
    s i ∈ @nhds G hB.topology 1 :=
  hB.nhds_one_hasBasis.mem_of_mem hi

-- See note [lower instance priority]
/-- If a group is endowed with the topological structure coming from a group filter basis, then
(by definition) this topology is invariant by translations. -/
@[to_additive "If a group is endowed with the topological structure coming from a group filter
basis, then (by definition) this topology is invariant by translations."]
instance (priority := 100) continuousConstSMul :
    @ContinuousConstSMul G G hB.topology _ := by
  letI := hB.topology
  refine ⟨?_⟩
  simp_rw [continuous_iff_continuousAt, ContinuousAt, Tendsto, nhds_eq, ← Filter.map_smul,
    smul_eq_mul, map_map, comp_mul_left, le_refl, implies_true]

-- See note [lower instance priority]
/-- If a group is endowed with the topological structure coming from a group filter basis, then
it's a topological group. -/
@[to_additive "If a group is endowed with the topological structure coming from a group filter basis
then it's a topological group."]
instance (priority := 100) topologicalGroup :
    @IsTopologicalGroup G hB.topology _ := by
  letI := hB.topology
  exact hB.topologicalGroup_of_hasBasis hB.nhds_one_hasBasis

end IsGroupBasis

/-!
## Filter bases for ring topologies
-/

/-- Given a ring `R`, `s : ι → Set R` and `p : ι → Prop`, `Filter.IsRingBasis p s` is a
strengthening of `Filter.IsBasis p s` with extra compatibility axioms ensuring that the generated
filter is the filter of neighborhoods of zero for some ring topology on `R`
(`Filter.IsRingBasis.topologicalRing`). Conversely, *any* basis of neighborhoods of zero in a
topological ring satisfies these conditions (`Filter.HasBasis.isRingBasis`). -/
structure IsRingBasis {R : Type*} {ι : Sort*} [Ring R] (p : ι → Prop) (s : ι → Set R) : Prop
    extends IsAddGroupBasis p s where
  mul : ∀ {i}, p i → ∃ j, p j ∧ s j * s j ⊆ s i
  mul_left : ∀ (x₀ : R) {i}, p i → ∃ j, p j ∧ MapsTo (x₀ * ·) (s j) (s i)
  mul_right : ∀ (x₀ : R) {i}, p i → ∃ j, p j ∧ MapsTo (· * x₀) (s j) (s i)

/-- A constructor for `IsRingBasis` in the commutative case. -/
theorem IsRingBasis.mk_of_comm {R : Type*} {ι : Sort*} [CommRing R] (p : ι → Prop) (s : ι → Set R)
    (toIsAddGroupBasis : IsAddGroupBasis p s) (mul : ∀ {i}, p i → ∃ j, p j ∧ s j * s j ⊆ s i)
    (mul_left : ∀ (x₀ : R) {i}, p i → ∃ j, p j ∧ MapsTo (x₀ * ·) (s j) (s i)) :
    IsRingBasis p s where
  toIsAddGroupBasis := toIsAddGroupBasis
  mul := mul
  mul_left := mul_left
  mul_right := by simpa only [mul_comm] using mul_left

/-- In a topological ring, *any* basis of neighborhoods of zero is a ring filter
basis. -/
theorem HasBasis.isRingBasis {R : Type*} {ι : Sort*} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] {p : ι → Prop} {s : ι → Set R} (h : (𝓝 0).HasBasis p s) :
    IsRingBasis p s where
  toIsAddGroupBasis := h.isAddGroupBasis
  mul := by
    have : Tendsto (fun p : R × R ↦ p.1 * p.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
      simpa only [nhds_prod_eq, zero_mul] using (tendsto_mul (M := R) (a := 0) (b := 0))
    simpa [h.prod_self.tendsto_iff h, mul_subset_iff, forall_mem_comm] using this
  mul_left x₀ := by
    have : Tendsto (x₀ * ·) (𝓝 0) (𝓝 0) := by simpa using (tendsto_id (x := 𝓝 0) |>.const_mul x₀)
    rwa [h.tendsto_iff h] at this
  mul_right x₀ := by
    have : Tendsto (· * x₀) (𝓝 0) (𝓝 0) := by simpa using (tendsto_id (x := 𝓝 0) |>.mul_const x₀)
    rwa [h.tendsto_iff h] at this

/-- The trivial ring filter basis, inducing the discrete topology. -/
example {R : Type*} [Ring R] :
    IsRingBasis (fun _ ↦ True) (fun _ ↦ {0} : Unit → Set R) :=
  letI : TopologicalSpace R := ⊥
  haveI : DiscreteTopology R := ⟨rfl⟩
  (nhds_discrete R ▸ hasBasis_pure 0).isRingBasis

namespace IsRingBasis

variable {R : Type*} {ι : Sort*} [Ring R] {p : ι → Prop} {s : ι → Set R} (hB : IsRingBasis p s)
include hB

/-!
### Proving `IsTopologicalRing` from `Filter.IsRingBasis`
-/

/-- Assume the ring `R` is given a topology which is invariant by translations,
which we express as `ContinuousConstVAdd R R`.
To show that it is a ring topology, it suffices so exhibit a basis of neighborhoods of
zero satisfying `Filter.IsRingBasis`. -/
lemma topologicalRing_of_hasBasis [TopologicalSpace R] [ContinuousConstVAdd R R]
    (hB' : (𝓝 0).HasBasis p s) : IsTopologicalRing R := by
  haveI := hB.topologicalAddGroup_of_hasBasis hB'
  apply IsTopologicalRing.of_addGroup_of_nhds_zero
  · refine hB'.prod_self.tendsto_iff hB' |>.mpr fun i hi ↦ (hB.mul hi).imp
      fun j ⟨hj, hji⟩ ↦ ⟨hj, ?_⟩
    simpa [← image2_mul, forall_mem_comm] using hji
  · exact fun x₀ ↦ hB'.tendsto_iff hB' |>.mpr fun i hi ↦ (hB.mul_left x₀ hi).imp fun j ↦ id
  · exact fun x₀ ↦ hB'.tendsto_iff hB' |>.mpr fun i hi ↦ (hB.mul_right x₀ hi).imp fun j ↦ id

/-!
### Constructing a ring topology from `Filter.IsRingBasis`
-/

/-- The topological space structure coming from a ring filter basis.
It has the given basis as a basis of neighborhoods of zero. -/
nonrec abbrev topology : TopologicalSpace R := hB.topology

/-- If a ring is endowed with the topological structure coming from
a ring filter basis, then it's a topological ring. -/
instance (priority := 100) topologicalRing :
    @IsTopologicalRing R hB.topology _ := by
  letI := hB.topology
  haveI := hB.continuousConstVAdd
  exact hB.topologicalRing_of_hasBasis hB.nhds_zero_hasBasis

end IsRingBasis

/-!
## Filter bases for module topologies
-/

/-- Consider a topological ring `R`, a `R`-module `M`, `s : ι → Set M` and `p : ι → Prop`.
`Filter.IsModuleBasis R p s` is a strengthening of `Filter.IsBasis p s` with extra compatibility
axioms ensuring that the generated filter is the filter of neighborhoods of zero for some
`R`-module topology on `R` (`Filter.IsModuleBasis.continuousSMul`). Conversely, *any* basis of
neighborhoods of zero in a topological `R`-module satisfies these conditions
(`Filter.HasBasis.isModuleBasis`). -/
structure IsModuleBasis (R : Type*) {M : Type*} {ι : Sort*} [Ring R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] (p : ι → Prop) (s : ι → Set M) : Prop
    extends IsAddGroupBasis p s where
  smul : ∀ {i}, p i → ∃ V ∈ 𝓝 (0 : R), ∃ j, p j ∧ V • (s j) ⊆ s i
  smul_left : ∀ (x₀ : R) {i}, p i → ∃ j, p j ∧ MapsTo (x₀ • ·) (s j) (s i)
  smul_right : ∀ (m₀ : M) {i}, p i → ∀ᶠ x in 𝓝 (0 : R), x • m₀ ∈ s i

/-- A constructor for `IsModuleBasis` if we have a preferred basis of neighborhoods of zero
in the base ring. In particular, this applies when the ring topology comes from
`Filter.IsRingBasis`. -/
theorem IsModuleBasis.mk_of_hasBasis {R M : Type*} {ιR ιM : Sort*} [Ring R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] {pR : ιR → Prop} {sR : ιR → Set R} (hR : (𝓝 0).HasBasis pR sR)
    (pM : ιM → Prop) (sM : ιM → Set M) (toIsAddGroupBasis : IsAddGroupBasis pM sM)
    (smul : ∀ {i}, pM i → ∃ j, pR j ∧ ∃ k, pM k ∧ (sR j) • (sM k) ⊆ sM i)
    (smul_left : ∀ (x₀ : R) {i}, pM i → ∃ j, pM j ∧ MapsTo (x₀ • ·) (sM j) (sM i))
    (smul_right : ∀ (m₀ : M) {i}, pM i → ∃ j, pR j ∧ MapsTo (· • m₀) (sR j) (sM i)) :
    IsModuleBasis R pM sM where
  toIsAddGroupBasis := toIsAddGroupBasis
  smul hi := smul hi |>.imp' sR fun _ ↦ And.imp_left <| hR.mem_of_mem
  smul_left := smul_left
  smul_right m₀ _ hi := hR.eventually_iff.mpr <| smul_right m₀ hi

/-- In a topological `R`-module, *any* basis of neighborhoods of zero is a module filter basis. -/
theorem HasBasis.isModuleBasis (R : Type*) {M : Type*} {ι : Sort*} [Ring R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul R M]
    {p : ι → Prop} {s : ι → Set M} (h : (𝓝 0).HasBasis p s) :
    IsModuleBasis R p s where
  toIsAddGroupBasis := h.isAddGroupBasis
  smul := by
    have : Tendsto (fun p ↦ p.1 • p.2 : R × M → M) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0 : Filter M) := by
      simpa only [nhds_prod_eq, smul_zero] using
        (tendsto_fst (α := R) (β := M) (f := 𝓝 0) (g := 𝓝 0)).smul tendsto_snd
    simpa [(basis_sets _ |>.prod_pprod h).tendsto_iff h, and_assoc, exists_and_left,
      smul_subset_iff, forall_comm (α := _ ∈ _) (β := M)] using this
  smul_left x₀ := by
    have : Tendsto (x₀ • · : M → M) (𝓝 0) (𝓝 0) := by
      simpa [smul_zero] using (tendsto_id (α := M) (x := 𝓝 0) |>.const_smul x₀)
    rwa [h.tendsto_iff h] at this
  smul_right m₀ := by
    have : Tendsto (· • m₀ : R → M) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (α := R) (x := 𝓝 0) |>.smul_const m₀)
    rwa [h.tendsto_right_iff] at this

namespace IsModuleBasis

variable {R M : Type*} {ι : Sort*} [Ring R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] {p : ι → Prop} {s : ι → Set M} (hB : IsModuleBasis R p s)
include hB

/-- If `R` is discrete then the trivial additive group filter basis on any `R`-module is a
module filter basis. -/
example [DiscreteTopology R] : IsModuleBasis R (fun _ ↦ True) (fun _ ↦ {0} : Unit → Set M) :=
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  -- TODO: these should be inferred
  haveI : IsTopologicalAddGroup M := ⟨⟩
  haveI : ContinuousSMul R M := ⟨continuous_of_discreteTopology⟩
  (nhds_discrete M ▸ hasBasis_pure 0).isModuleBasis R

/-!
### Proving `ContinuousSMul` from `Filter.IsModuleBasis`
-/

/-- Assume the `R`-module `M` is given a topology which is invariant by translations,
which we express as `ContinuousConstVAdd M M`.
To show that it is a `R`-module topology, it suffices so exhibit a basis of neighborhoods of
zero satisfying `Filter.IsModuleBasis R`. -/
theorem continuousSMul_of_hasBasis [IsTopologicalRing R] [TopologicalSpace M]
    [ContinuousConstVAdd M M] (hB' : (𝓝 0).HasBasis p s) : ContinuousSMul R M := by
  haveI := hB.topologicalAddGroup_of_hasBasis hB'
  apply ContinuousSMul.of_nhds_zero
  · refine basis_sets _ |>.prod_pprod hB' |>.tendsto_iff hB' |>.mpr fun i hi ↦
      let ⟨V, hV, j, hj, hVj⟩ := (hB.smul hi); ⟨⟨V, j⟩, ⟨hV, hj⟩, ?_⟩
    simpa [forall_swap (α := M), ← image2_smul] using hVj
  · exact fun m₀ ↦ hB'.tendsto_right_iff.mpr fun i hi ↦ hB.smul_right m₀ hi
  · exact fun x₀ ↦ hB'.tendsto_iff hB' |>.mpr fun i hi ↦ (hB.smul_left x₀ hi).imp fun j ↦ id

/-!
### Constructing a module topology from `Filter.IsModuleBasis`
-/

/-- The topology associated to a module filter basis on a module over a topological ring.
It has the given basis as a basis of neighborhoods of zero. -/
nonrec abbrev topology : TopologicalSpace M := hB.topology

/-- The topology associated to a module filter basis on a module over a topological ring.
It has the given basis as a basis of neighborhoods of zero. This version gets the ring
topology by unification instead of type class inference. -/
abbrev topology' {R M : Type*} {ι : Sort*} [CommRing R] {_ : TopologicalSpace R}
    [AddCommGroup M] [Module R M] {p : ι → Prop} {s : ι → Set M} (hB : IsModuleBasis R p s) :
    TopologicalSpace M :=
  hB.topology

/-- If a module is endowed with the topological structure coming from
a module filter basis then it's a topological module. -/
instance (priority := 100) continuousSMul [IsTopologicalRing R] :
    @ContinuousSMul R M _ _ hB.topology := by
  letI := hB.topology
  haveI := hB.continuousConstVAdd
  exact hB.continuousSMul_of_hasBasis hB.nhds_zero_hasBasis

end IsModuleBasis

end Filter

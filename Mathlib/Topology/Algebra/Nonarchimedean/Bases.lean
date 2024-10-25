/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker
-/
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.FilterBasis

/-!
# Neighborhood bases for non-archimedean rings and modules

This files contains special families of filter bases on rings and modules that give rise to
non-archimedean topologies.

The main definition is `RingSubgroupsBasis` which is a predicate on a family of
additive subgroups of a ring. The predicate ensures there is a topology
`RingSubgroupsBasis.topology` which is compatible with a ring structure and admits the given
family as a basis of neighborhoods of zero. In particular the given subgroups become open subgroups
(bundled in `RingSubgroupsBasis.openAddSubgroup`) and we get a non-archimedean topological ring
(`RingSubgroupsBasis.nonarchimedean`).

A special case of this construction is given by `SubmodulesBasis` where the subgroups are
sub-modules in a commutative algebra. This important example gives rise to the adic topology
(studied in its own file).
-/

open Set Filter Function Lattice

open Topology Filter Pointwise

namespace Filter

namespace IsGroupBasis

@[to_additive]
theorem mk_of_subgroups {G S : Type*} {ι : Sort*} [Group G] [SetLike S G] [SubgroupClass S G]
    {p : ι → Prop} {B : ι → S} (isBasis : IsBasis p (fun i ↦ B i : ι → Set G))
    (conj : ∀ x₀, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (x₀ * · * x₀⁻¹) (B j) (B i : Set G)) :
    IsGroupBasis p (fun i ↦ B i : ι → Set G) where
  toIsBasis := isBasis
  one _ := one_mem _
  mul {i} hi := ⟨i, hi, mul_subset_iff.mpr fun _ ha _ hb ↦ mul_mem ha hb⟩
  inv {i} hi := ⟨i, hi, fun _ ha ↦ inv_mem ha⟩
  conj := conj

@[to_additive]
theorem mk_of_subgroups_of_comm {G S : Type*} {ι : Sort*} [CommGroup G]
    [SetLike S G] [SubgroupClass S G] {p : ι → Prop} {B : ι → S}
    (isBasis : IsBasis p (fun i ↦ B i : ι → Set G)) :
    IsGroupBasis p (fun i ↦ B i : ι → Set G) :=
  .mk_of_comm _ _ isBasis (fun _ ↦ one_mem _)
    (fun {i} hi ↦ ⟨i, hi, mul_subset_iff.mpr fun _ ha _ hb ↦ mul_mem ha hb⟩)
    (fun {i} hi ↦ ⟨i, hi, fun _ ha ↦ inv_mem ha⟩)

variable {G S : Type*} {ι : Sort*} [Group G] [SetLike S G] [SubgroupClass S G]
  {p : ι → Prop} {B : ι → S} (hB : IsGroupBasis p (fun i ↦ B i : ι → Set G))
include hB

/-
TODO(Anatole) : these two things should be lemmas about `NonarchimedeanGroup` topologies, not
specifically those of the form `hB.topology`.
-/

/-- Given a subgroups basis, the basis elements as open additive subgroups in the associated
topology. -/
@[to_additive]
def openSubgroup_of_subgroups {i : ι} (hi : p i) :
    @OpenSubgroup G _ hB.topology :=
  -- Porting note: failed to synthesize instance `TopologicalSpace G`
  letI := hB.topology
  { carrier := B i
    mul_mem' := mul_mem
    one_mem' := one_mem _
    inv_mem' := inv_mem
    isOpen' := Subgroup.isOpen_of_mem_nhds _ <| hB.nhds_one_hasBasis.mem_of_mem hi }

-- see Note [nonarchimedean non instances]
@[to_additive]
theorem nonarchimedean_of_subgroups : @NonarchimedeanGroup G _ hB.topology := by
  letI := hB.topology
  constructor
  intro U hU
  obtain ⟨i, hi, hiU : (B i : Set G) ⊆ U⟩ := hB.nhds_one_hasBasis.mem_iff.mp hU
  exact ⟨hB.openSubgroup_of_subgroups hi, hiU⟩

end IsGroupBasis

namespace IsRingBasis

theorem mk_of_subgroups {A S : Type*} {ι : Sort*} [Ring A] [SetLike S A] [AddSubgroupClass S A]
    {p : ι → Prop} {B : ι → S} (isBasis : IsBasis p (fun i ↦ B i : ι → Set A))
    (mul : ∀ {i}, p i → ∃ j, p j ∧ (B j : Set A) * B j ⊆ B i)
    (mul_left : ∀ x : A, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (x * ·) (B j) (B i))
    (mul_right : ∀ x : A, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (· * x) (B j) (B i)) :
    IsRingBasis p (fun i ↦ B i : ι → Set A) where
  toIsAddGroupBasis := .mk_of_subgroups_of_comm isBasis
  mul := mul
  mul_left := mul_left
  mul_right := mul_right

theorem mk_of_subgroups_of_comm {A S : Type*} {ι : Sort*} [CommRing A]
    [SetLike S A] [AddSubgroupClass S A] {p : ι → Prop} {B : ι → S}
    (isBasis : IsBasis p (fun i ↦ B i : ι → Set A))
    (mul : ∀ {i}, p i → ∃ j, p j ∧ (B j : Set A) * B j ⊆ B i)
    (mul_left : ∀ x : A, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (x * ·) (B j) (B i)) :
    IsRingBasis p (fun i ↦ B i : ι → Set A) :=
  .mk_of_comm _ _ (.mk_of_subgroups_of_comm isBasis) mul mul_left

theorem mk_of_ideals_of_comm {A S : Type*} {ι : Sort*} [CommRing A]
    [SetLike S A] [AddSubgroupClass S A] [SMulMemClass S A A] {p : ι → Prop} {B : ι → S}
    (isBasis : IsBasis p (fun i ↦ B i : ι → Set A))
    (mul : ∀ {i}, p i → ∃ j, p j ∧ (B j : Set A) * B j ⊆ B i) :
    IsRingBasis p (fun i ↦ B i : ι → Set A) :=
  .mk_of_subgroups_of_comm isBasis mul fun a {i} hi ↦ ⟨i, hi, fun _ hx ↦ SMulMemClass.smul_mem a hx⟩

variable {A S : Type*} {ι : Sort*} [Ring A] [SetLike S A] [AddSubgroupClass S A]
    {p : ι → Prop} {B : ι → S} (hB : IsRingBasis p (fun i ↦ B i : ι → Set A))

-- see Note [nonarchimedean non instances]
nonrec theorem nonarchimedean_of_subgroups : @NonarchimedeanRing A _ hB.topology := by
  letI := hB.topology
  constructor
  exact hB.nonarchimedean_of_subgroups.is_nonarchimedean

end IsRingBasis

namespace IsModuleBasis

theorem mk_of_submodules {R M S : Type*} {ι : Sort*} [Ring R]
    [TopologicalSpace R] [AddCommGroup M] [Module R M]
    [SetLike S M] [AddSubgroupClass S M] [SMulMemClass S R M]
    {p : ι → Prop} {B : ι → S}
    (isBasis : IsBasis p (fun i ↦ B i : ι → Set M))
    (smul : ∀ (m : M) {i : ι}, p i → ∀ᶠ a in 𝓝 (0 : R), a • m ∈ B i) :
    IsModuleBasis R p (fun i ↦ B i : ι → Set M) where
  toIsAddGroupBasis := .mk_of_subgroups_of_comm isBasis
  smul {i} hi := ⟨univ, univ_mem, i, hi, smul_subset_iff.mpr
    fun _ _ _ hb ↦ SMulMemClass.smul_mem _ hb⟩
  smul_left _ {i} hi := ⟨i, hi, fun _ hb ↦ SMulMemClass.smul_mem _ hb⟩
  smul_right := smul

set_option linter.unusedVariables.funArgs false
theorem mk_of_submodules_of_hasBasis {R M S : Type*} {ιR ιM : Sort*} [CommRing R]
    [tR : TopologicalSpace R] [AddCommGroup M] [Module R M]
    [SetLike S M] [AddSubgroupClass S M] [SMulMemClass S R M]
    {pR : ιR → Prop} {sR : ιR → Set R} (hR : (𝓝 0).HasBasis pR sR)
    {pM : ιM → Prop} {sM : ιM → S} (isBasis : IsBasis pM (fun i ↦ sM i : ιM → Set M))
    (smul : ∀ (m : M) {i}, pM i → ∃ j, pR j ∧ MapsTo (· • m) (sR j) (sM i)) :
    IsModuleBasis R pM (fun i ↦ sM i : ιM → Set M) :=
  .mk_of_submodules isBasis (fun m₀ _ hi ↦ hR.eventually_iff.mpr <| smul m₀ hi)

end IsModuleBasis

end Filter

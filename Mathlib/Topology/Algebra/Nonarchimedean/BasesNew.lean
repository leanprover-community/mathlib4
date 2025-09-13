/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker
-/
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.FilterBasisNew

/-!
**WARNING** : This is a new version of `Topology.Algebra.Nonarchimedean.Bases`, which is still used
by the library at this point in time. The library will be gradually modified to use this file
instead. See `https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Refactoring.20algebraic.20filter.20bases/near/479437345`
for more details.

# Neighborhood bases for non-archimedean groups, rings and modules

This file specializes the theory of algebraic filter bases (see
the docstring of `Topology.Algebra.FilterBasis`) to filter bases whose elements are
algebraic subobjects.

More specifically, we provide multiple alternative constructors for `Filter.IsXBasis`,
where `X ∈ {Group, AddGroup, Ring, Module}`, in the case where the basis elements
have some extra algebraic structure. For example, `Filter.IsAddGroupBasis.mk_of_subgroups_of_comm`
shows that, in a commutative additive group, any filter basis made of subgroups is automatically
a group filter basis.

We also prove some extra results about the topological objects obtained in this setting
(that is, nonarchimedean objects), but these should probably be tweaked to *not* mention
`IsGroupBasis` (and friends) and moved elsewhere. More details in comments around the file.

## Implementation note

* We use subobject classes, so for example `Filter.IsAddGroupBasis.mk_of_subgroups` will
  also apply if your basis is valued in `Submodule`, `Ideal`, ...

* For a long time, each additional constructor in this file was its own predicate (e.g
  there was a definition for "ring filter bases made of subgroups", another one for
  "ring filter bases made of submodules", and so on...). Furthermore, these did not take any
  predicate bounding the filter basis, making them inconsistent with both `Filter.IsBasis`
  and `FilterBasis` (recall that the general setup used to rely on `FilterBasis`).
  This led to a lot of (inconsistent) code duplication, which doesn't exist anymore.

-/

open Set Filter Function Lattice

open Topology Filter Pointwise

namespace Filter

namespace IsGroupBasis

/-- A simpler constructor for `Filter.IsGroupBasis` for bases valued in
`Subgroup` (or any `S` satisfying `SubgroupClass S G`). -/
@[to_additive "A simpler constructor for `Filter.IsAddGroupBasis` for bases valued in
`AddSubgroup` (or any `S` satisfying `AddSubgroupClass S G`)."]
theorem mk_of_subgroups {G S : Type*} {ι : Sort*} [Group G] [SetLike S G] [SubgroupClass S G]
    {p : ι → Prop} {B : ι → S} (isBasis : IsBasis p (fun i ↦ B i : ι → Set G))
    (conj : ∀ x₀, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (x₀ * · * x₀⁻¹) (B j) (B i : Set G)) :
    IsGroupBasis p (fun i ↦ B i : ι → Set G) where
  toIsBasis := isBasis
  one _ := one_mem _
  mul {i} hi := ⟨i, hi, mul_subset_iff.mpr fun _ ha _ hb ↦ mul_mem ha hb⟩
  inv {i} hi := ⟨i, hi, fun _ ha ↦ inv_mem ha⟩
  conj := conj

/-- A version of `Filter.IsGroupBasis.mk_of_subgroups` for commutative groups. -/
@[to_additive "A version of `Filter.IsAddGroupBasis.mk_of_subgroups` for commutative groups."]
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

-- TODO(Anatole) : this should be a general lemma assuming `(𝓝 1).HasBasis p s`
-- with `s` valued in subgroups.
/-- If a group filter basis is made of subgroups, these are open for the associated topology. -/
@[to_additive "If a group filter basis is made of subgroups, these are open for the associated
topology."]
def openSubgroup_of_subgroups {i : ι} (hi : p i) :
    @OpenSubgroup G _ hB.topology :=
  -- Porting note: failed to synthesize instance `TopologicalSpace G`
  letI := hB.topology
  { carrier := B i
    mul_mem' := mul_mem
    one_mem' := one_mem _
    inv_mem' := inv_mem
    isOpen' := Subgroup.isOpen_of_mem_nhds (.ofClass (B i)) (hB.nhds_one_hasBasis.mem_of_mem hi) }

-- TODO(Anatole) : this should be a general lemma assuming `(𝓝 1).HasBasis p s`
-- with `s` valued in subgroups.
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

/-- A simpler constructor for `Filter.IsRingBasis` for bases valued in
`AddSubgroup` (or any `S` satisfying `AddSubgroupClass S A`). -/
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

/-- A version of `Filter.IsRingBasis.mk_of_subgroups` in the commutative case. -/
theorem mk_of_subgroups_of_comm {A S : Type*} {ι : Sort*} [CommRing A]
    [SetLike S A] [AddSubgroupClass S A] {p : ι → Prop} {B : ι → S}
    (isBasis : IsBasis p (fun i ↦ B i : ι → Set A))
    (mul : ∀ {i}, p i → ∃ j, p j ∧ (B j : Set A) * B j ⊆ B i)
    (mul_left : ∀ x : A, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (x * ·) (B j) (B i)) :
    IsRingBasis p (fun i ↦ B i : ι → Set A) :=
  .mk_of_comm _ _ (.mk_of_subgroups_of_comm isBasis) mul mul_left

/-- A simpler constructor for `Filter.IsRingBasis` for bases valued in
`Ideal` (or any `S` satisfying `AddSubgroupClass S A` and `SMulMemClass S A A`). -/
theorem mk_of_ideals_of_comm {A S : Type*} {ι : Sort*} [CommRing A]
    [SetLike S A] [AddSubgroupClass S A] [SMulMemClass S A A] {p : ι → Prop} {B : ι → S}
    (isBasis : IsBasis p (fun i ↦ B i : ι → Set A)) :
    IsRingBasis p (fun i ↦ B i : ι → Set A) :=
  .mk_of_subgroups_of_comm isBasis
    (fun {i} hi ↦ ⟨i, hi, mul_subset_iff.mpr fun a _ _ hb ↦ SMulMemClass.smul_mem a hb⟩)
    (fun a {i} hi ↦ ⟨i, hi, fun _ hx ↦ SMulMemClass.smul_mem a hx⟩)

variable {A S : Type*} {ι : Sort*} [Ring A] [SetLike S A] [AddSubgroupClass S A]
    {p : ι → Prop} {B : ι → S} (hB : IsRingBasis p (fun i ↦ B i : ι → Set A))

-- TODO(Anatole) : this should be a general lemma assuming `(𝓝 0).HasBasis p s`
-- with `s` valued in subgroups.
-- see Note [nonarchimedean non instances]
nonrec theorem nonarchimedean_of_subgroups : @NonarchimedeanRing A _ hB.topology := by
  letI := hB.topology
  constructor
  exact hB.nonarchimedean_of_subgroups.is_nonarchimedean

end IsRingBasis

namespace IsModuleBasis

/-- A simpler constructor for `Filter.IsModuleBasis` for bases valued in
`Submodule` (or any `S` satisfying `AddSubgroupClass S M` and `SMulMemClass S R M`). -/
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
/-- A version of `IsModuleBasis.mk_of_submodules` given a preferred basis of neighborhoods of zero
in the base ring. In particular, this applies when the ring topology comes from
`Filter.IsRingBasis`. -/
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

/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker
-/
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Algebra.Module.Submodule.Pointwise

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

structure IsAddGroupBasisOfSubgroups {G : Type*} {ι : Sort*} [AddGroup G]
    (p : ι → Prop) (B : ι → AddSubgroup G) : Prop where
  nonempty : ∃ i, p i
  /-- Condition for `B` to be a filter basis on `G`. -/
  inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ B k ≤ B i ⊓ B j
  conj : ∀ x₀, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (x₀ + · + -x₀) (B j) (B i : Set G)

@[to_additive]
structure IsGroupBasisOfSubgroups {G : Type*} {ι : Sort*} [Group G]
    (p : ι → Prop) (B : ι → Subgroup G) : Prop where
  nonempty : ∃ i, p i
  /-- Condition for `B` to be a filter basis on `G`. -/
  inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ B k ≤ B i ⊓ B j
  conj : ∀ x₀, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (x₀ * · * x₀⁻¹) (B j) (B i : Set G)

namespace IsGroupBasisOfSubgroups

variable {G : Type*} {ι : Sort*} [Group G]

@[to_additive]
theorem mk_of_comm {G : Type*} {ι : Sort*} [CommGroup G] (p : ι → Prop) (B : ι → Subgroup G)
    (nonempty : ∃ i, p i)
    (inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ B k ≤ B i ⊓ B j) :
    IsGroupBasisOfSubgroups p B where
  nonempty := nonempty
  inter := inter
  conj x₀ {i} hi := ⟨i, hi, by simpa only [mul_inv_cancel_comm, preimage_id'] using mapsTo_id _⟩

variable {p : ι → Prop} {B : ι → Subgroup G} (hB : IsGroupBasisOfSubgroups p B)
include hB

@[to_additive]
theorem isGroupBasis :
    IsGroupBasis p ((↑) ∘ B : ι → Set G) where
  nonempty := hB.nonempty
  inter := hB.inter
  one' _ := one_mem _
  mul' {i} hi := ⟨i, hi, mul_subset_iff.mpr fun _ ha _ hb ↦ mul_mem ha hb⟩
  inv' {i} hi := ⟨i, hi, fun _ ha ↦ inv_mem ha⟩
  conj' := hB.conj

/-- The topology defined from a subgroups basis, admitting the given subgroups as a basis
of neighborhoods of zero. -/
@[to_additive]
abbrev topology : TopologicalSpace G :=
  hB.isGroupBasis.topology

@[to_additive]
theorem hasBasis_nhds_one : HasBasis (@nhds G hB.topology 1) p ((↑) ∘ B) :=
  hB.isGroupBasis.nhds_one_hasBasis

@[to_additive]
theorem hasBasis_nhds (g : G) :
    HasBasis (@nhds G hB.topology g) p (fun i => {x | g⁻¹ * x ∈ B i}) := by
  simpa [← Set.preimage_smul_inv, ← div_eq_mul_inv] using hB.isGroupBasis.nhds_hasBasis g

/-- Given a subgroups basis, the basis elements as open additive subgroups in the associated
topology. -/
@[to_additive]
def openSubgroup {i : ι} (hi : p i) : @OpenSubgroup G _ hB.topology :=
  -- Porting note: failed to synthesize instance `TopologicalSpace A`
  let _ := hB.topology
  { B i with
    isOpen' := (B i).isOpen_of_mem_nhds <| hB.hasBasis_nhds_one.mem_of_mem hi }

-- see Note [nonarchimedean non instances]
@[to_additive]
theorem nonarchimedean : @NonarchimedeanGroup G _ hB.topology := by
  letI := hB.topology
  constructor
  intro U hU
  obtain ⟨i, hi, hiU : (B i : Set G) ⊆ U⟩ := hB.hasBasis_nhds_one.mem_iff.mp hU
  exact ⟨hB.openSubgroup hi, hiU⟩


end IsGroupBasisOfSubgroups

/-- A family of additive subgroups on a ring `A` is a subgroups basis if it satisfies some
axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure IsRingBasisOfSubgroups {A : Type*} {ι : Sort*} [Ring A]
    (p : ι → Prop) (B : ι → AddSubgroup A) extends IsAddGroupBasisOfSubgroups p B : Prop where
  mul : ∀ {i}, p i → ∃ j, p j ∧ (B j : Set A) * B j ⊆ B i
  /-- For any element `x : A` and any set `B` in the submodule basis on `A`,
    there is another basis element `B'` such that `B' * x` is in `B`. -/
  mul_left : ∀ x : A, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (x * ·) (B j) (B i)
  /-- For any element `x : A` and any set `B` in the submodule basis on `A`,
    there is another basis element `B'` such that `x * B'` is in `B`. -/
  mul_right : ∀ x : A, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (· * x) (B j) (B i)

namespace IsRingBasisOfSubgroups

variable {A : Type*} {ι : Sort*} [Ring A]

theorem mk_of_comm {A : Type*} {ι : Sort*} [CommRing A] (p : ι → Prop) (B : ι → AddSubgroup A)
    (nonempty : ∃ i, p i)
    (inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ B k ≤ B i ⊓ B j)
    (mul : ∀ {i}, p i → ∃ j, p j ∧ (B j : Set A) * B j ⊆ B i)
    (mul_left : ∀ x : A, ∀ {i}, p i → ∃ j, p j ∧ MapsTo (x * ·) (B j) (B i)) :
    IsRingBasisOfSubgroups p B where
  toIsAddGroupBasisOfSubgroups := .mk_of_comm p B nonempty inter
  mul := mul
  mul_left := mul_left
  mul_right := fun x i hi ↦ (mul_left x hi).imp fun j hj ↦ by simpa only [mul_comm] using hj

variable {p : ι → Prop} {B : ι → AddSubgroup A} (hB : IsRingBasisOfSubgroups p B)
include hB

theorem isRingBasis :
    IsRingBasis p ((↑) ∘ B : ι → Set A) where
  toIsAddGroupBasis := hB.isAddGroupBasis
  mul' := hB.mul
  mul_left' := hB.mul_left
  mul_right' := hB.mul_right

/-- The topology defined from a subgroups basis, admitting the given subgroups as a basis
of neighborhoods of zero. -/
abbrev topology : TopologicalSpace A :=
  hB.isRingBasis.topology

theorem hasBasis_nhds_zero : HasBasis (@nhds A hB.topology 0) p ((↑) ∘ B) :=
  hB.isRingBasis.nhds_zero_hasBasis

theorem hasBasis_nhds (a : A) :
    HasBasis (@nhds A hB.topology a) p (fun i => {b | b - a ∈ B i}) := by
  simpa [add_comm, ← sub_eq_add_neg] using hB.toIsAddGroupBasisOfSubgroups.hasBasis_nhds a

/-- Given a subgroups basis, the basis elements as open additive subgroups in the associated
topology. -/
nonrec abbrev openAddSubgroup {i : ι} (hi : p i) : @OpenAddSubgroup A _ hB.topology :=
  hB.openAddSubgroup hi

-- see Note [nonarchimedean non instances]
theorem nonarchimedean : @NonarchimedeanRing A _ hB.topology := by
  letI := hB.topology
  constructor
  exact hB.toIsAddGroupBasisOfSubgroups.nonarchimedean.is_nonarchimedean

end IsRingBasisOfSubgroups

variable {R A : Type*} {ι : Sort*} [CommRing R] [CommRing A] [Algebra R A]

/-- A family of submodules in a commutative `R`-algebra `A` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure IsRingBasisOfSubmodules (p : ι → Prop) (B : ι → Submodule R A) : Prop where
  nonempty : ∃ i, p i
  /-- Condition for `B` to be a filter basis on `A`. -/
  inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ B k ≤ B i ⊓ B j
  /-- For any element `a : A` and any set `B` in the submodule basis on `A`,
    there is another basis element `B'` such that `a • B'` is in `B`. -/
  mul_left : ∀ (a : A) {i}, p i → ∃ j, p j ∧ MapsTo (a • ·) (B j : Set A) (B i)
  /-- For each set `B` in the submodule basis on `A`, there is another basis element `B'` such
    that the set-theoretic product `B' * B'` is in `B`. -/
  mul : ∀ {i}, p i → ∃ j, p j ∧ (B j : Set A) * B j ⊆ B i

namespace IsRingBasisOfSubmodules

variable {p : ι → Prop} {B : ι → Submodule R A} (hB : IsRingBasisOfSubmodules p B)
include hB

theorem isRingBasisOfSubgroups :
    IsRingBasisOfSubgroups p fun i ↦ (B i).toAddSubgroup :=
  .mk_of_comm p _ hB.nonempty hB.inter hB.mul hB.mul_left

/-- The topology associated to a basis of submodules in an algebra. -/
abbrev topology : TopologicalSpace A :=
  hB.isRingBasisOfSubgroups.topology

end IsRingBasisOfSubmodules

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A family of submodules in an `R`-module `M` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `M` which is compatible with the module structure and
admits this family as a basis of neighborhoods of zero. -/
structure IsModuleBasisOfSubmodules [TopologicalSpace R]
    (p : ι → Prop) (B : ι → Submodule R M) : Prop where
  nonempty : ∃ i, p i
  /-- Condition for `B` to be a filter basis on `M`. -/
  inter : ∀ {i j}, p i → p j → ∃ k, p k ∧ B k ≤ B i ⊓ B j
  /-- For any element `m : M` and any set `B` in the basis, `a • m` lies in `B` for all
    `a` sufficiently close to `0`. -/
  smul : ∀ (m : M) {i : ι}, p i → ∀ᶠ a in 𝓝 (0 : R), a • m ∈ B i

namespace IsModuleBasisOfSubmodules

variable [TopologicalSpace R] {p : ι → Prop} {B : ι → Submodule R M}
  (hB : IsModuleBasisOfSubmodules p B)
include hB

theorem isModuleBasis : IsModuleBasis R p ((↑) ∘ B : ι → Set M) where
  nonempty := hB.nonempty
  inter := hB.inter
  zero' _ := zero_mem _
  add' {i} hi := ⟨i, hi, add_subset_iff.mpr fun _ ha _ hb ↦ add_mem ha hb⟩
  neg' {i} hi := ⟨i, hi, fun _ ha ↦ neg_mem ha⟩
  conj' a {i} hi := ⟨i, hi, fun _ hb ↦ by simpa [SetLike.mem_coe] using hb⟩
  smul' {i} hi := ⟨univ, univ_mem, i, hi, smul_subset_iff.mpr
    fun _ _ _ hb ↦ Submodule.smul_mem _ _ hb⟩
  smul_left' x₀ {i} hi := ⟨i, hi, fun _ hb ↦ Submodule.smul_mem _ _ hb⟩
  smul_right' := hB.smul

/-- The topology associated to a basis of submodules in a module. -/
abbrev topology : TopologicalSpace M :=
  hB.isModuleBasis.topology

/-- Given a submodules basis, the basis elements as open additive subgroups in the associated
topology. -/
def openAddSubgroup (i : ι) : @OpenAddSubgroup M _ hB.topology :=
  let _ := hB.topology -- Porting note: failed to synthesize instance `TopologicalSpace A`
  { (B i).toAddSubgroup with
    isOpen' := by
      letI := hB.topology
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
      use B i
      constructor
      · use i
      · rintro - ⟨b, b_in, rfl⟩
        exact (B i).add_mem a_in b_in }

-- see Note [nonarchimedean non instances]
theorem nonarchimedean (hB : SubmodulesBasis B) : @NonarchimedeanAddGroup M _ hB.topology := by
  letI := hB.topology
  constructor
  intro U hU
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : Set M) ⊆ U⟩ :=
    hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩

library_note "nonarchimedean non instances"/--
The non archimedean subgroup basis lemmas cannot be instances because some instances
(such as `MeasureTheory.AEEqFun.instAddMonoid` or `TopologicalAddGroup.toContinuousAdd`)
cause the search for `@TopologicalAddGroup β ?m1 ?m2`, i.e. a search for a topological group where
the topology/group structure are unknown. -/


end SubmodulesBasis

section

/-
In this section, we check that in an `R`-algebra `A` over a ring equipped with a topology,
a basis of `R`-submodules which is compatible with the topology on `R` is also a submodule basis
in the sense of `R`-modules (forgetting about the ring structure on `A`) and those two points of
view definitionaly gives the same topology on `A`.
-/
variable [TopologicalSpace R] {B : ι → Submodule R A} (hB : SubmodulesRingBasis B)
  (hsmul : ∀ (m : A) (i : ι), ∀ᶠ a : R in 𝓝 0, a • m ∈ B i)
include hB hsmul

theorem SubmodulesRingBasis.toSubmodulesBasis : SubmodulesBasis B :=
  { inter := hB.inter
    smul := hsmul }

example [Nonempty ι] : hB.topology = (hB.toSubmodulesBasis hsmul).topology :=
  rfl

end

/-- Given a ring filter basis on a commutative ring `R`, define a compatibility condition
on a family of submodules of an `R`-module `M`. This compatibility condition allows to get
a topological module structure. -/
structure RingFilterBasis.SubmodulesBasis (BR : RingFilterBasis R) (B : ι → Submodule R M) :
    Prop where
  /-- Condition for `B` to be a filter basis on `M`. -/
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  /-- For any element `m : M` and any set `B i` in the submodule basis on `M`,
    there is a `U` in the ring filter basis on `R` such that `U * m` is in `B i`. -/
  smul : ∀ (m : M) (i : ι), ∃ U ∈ BR, U ⊆ (· • m) ⁻¹' B i

theorem RingFilterBasis.submodulesBasisIsBasis (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @_root_.SubmodulesBasis ι R _ M _ _ BR.topology B :=
  let _ := BR.topology -- Porting note: failed to synthesize instance `TopologicalSpace R`
  { inter := hB.inter
    smul := by
      letI := BR.topology
      intro m i
      rcases hB.smul m i with ⟨V, V_in, hV⟩
      exact mem_of_superset (BR.toAddGroupFilterBasis.mem_nhds_zero V_in) hV }

/-- The module filter basis associated to a ring filter basis and a compatible submodule basis.
This allows to build a topological module structure compatible with the given module structure
and the topology associated to the given ring filter basis. -/
def RingFilterBasis.moduleFilterBasis [Nonempty ι] (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @ModuleFilterBasis R M _ BR.topology _ _ :=
  @SubmodulesBasis.toModuleFilterBasis ι R _ M _ _ BR.topology _ _ (BR.submodulesBasisIsBasis hB)

/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.nonarchimedean.bases
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Nonarchimedean.Basic
import Mathbin.Topology.Algebra.FilterBasis
import Mathbin.Algebra.Module.Submodule.Pointwise

/-!
# Neighborhood bases for non-archimedean rings and modules

This files contains special families of filter bases on rings and modules that give rise to
non-archimedean topologies.

The main definition is `ring_subgroups_basis` which is a predicate on a family of
additive subgroups of a ring. The predicate ensures there is a topology
`ring_subgroups_basis.topology` which is compatible with a ring structure and admits the given
family as a basis of neighborhoods of zero. In particular the given subgroups become open subgroups
(bundled in `ring_subgroups_basis.open_add_subgroup`) and we get a non-archimedean topological ring
(`ring_subgroups_basis.nonarchimedean`).

A special case of this construction is given by `submodules_basis` where the subgroups are
sub-modules in a commutative algebra. This important example gives rises to the adic topology
(studied in its own file).

-/


open Set Filter Function Lattice AddGroupWithZeroNhd

open Topology Filter Pointwise

/-- A family of additive subgroups on a ring `A` is a subgroups basis if it satisfies some
axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure RingSubgroupsBasis {A ι : Type _} [Ring A] (B : ι → AddSubgroup A) : Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i
  leftMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (fun y : A => x * y) ⁻¹' B i
  rightMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (fun y : A => y * x) ⁻¹' B i
#align ring_subgroups_basis RingSubgroupsBasis

namespace RingSubgroupsBasis

variable {A ι : Type _} [Ring A]

theorem of_comm {A ι : Type _} [CommRing A] (B : ι → AddSubgroup A)
    (inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j) (mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i)
    (left_mul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (fun y : A => x * y) ⁻¹' B i) :
    RingSubgroupsBasis B :=
  { inter
    mul
    leftMul
    rightMul := by
      intro x i
      cases' leftMul x i with j hj
      use j
      simpa [mul_comm] using hj }
#align ring_subgroups_basis.of_comm RingSubgroupsBasis.of_comm

/-- Every subgroups basis on a ring leads to a ring filter basis. -/
def toRingFilterBasis [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B) :
    RingFilterBasis A where
  sets := { U | ∃ i, U = B i }
  Nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    cases' hB.inter i j with k hk
    use B k, k, rfl, hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i, i, rfl
    rintro x ⟨y, z, y_in, z_in, rfl⟩
    exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i, i, rfl
    intro x x_in
    exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i, i, rfl
    simp
  mul' := by
    rintro _ ⟨i, rfl⟩
    cases' hB.mul i with k hk
    use B k, k, rfl, hk
  mul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    cases' hB.left_mul x₀ i with k hk
    use B k, k, rfl, hk
  mul_right' := by
    rintro x₀ _ ⟨i, rfl⟩
    cases' hB.right_mul x₀ i with k hk
    use B k, k, rfl, hk
#align ring_subgroups_basis.to_ring_filter_basis RingSubgroupsBasis.toRingFilterBasis

variable [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B)

theorem mem_addGroupFilterBasis_iff {V : Set A} :
    V ∈ hB.toRingFilterBasis.toAddGroupFilterBasis ↔ ∃ i, V = B i :=
  Iff.rfl
#align ring_subgroups_basis.mem_add_group_filter_basis_iff RingSubgroupsBasis.mem_addGroupFilterBasis_iff

theorem mem_addGroupFilterBasis (i) : (B i : Set A) ∈ hB.toRingFilterBasis.toAddGroupFilterBasis :=
  ⟨i, rfl⟩
#align ring_subgroups_basis.mem_add_group_filter_basis RingSubgroupsBasis.mem_addGroupFilterBasis

/-- The topology defined from a subgroups basis, admitting the given subgroups as a basis
of neighborhoods of zero. -/
def topology : TopologicalSpace A :=
  hB.toRingFilterBasis.toAddGroupFilterBasis.topology
#align ring_subgroups_basis.topology RingSubgroupsBasis.topology

theorem hasBasis_nhds_zero : HasBasis (@nhds A hB.topology 0) (fun _ => True) fun i => B i :=
  ⟨by
    intro s
    rw [hB.to_ring_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact ⟨i, trivial, hi⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨B i, ⟨i, rfl⟩, hi⟩⟩
#align ring_subgroups_basis.has_basis_nhds_zero RingSubgroupsBasis.hasBasis_nhds_zero

theorem hasBasis_nhds (a : A) :
    HasBasis (@nhds A hB.topology a) (fun _ => True) fun i => { b | b - a ∈ B i } :=
  ⟨by
    intro s
    rw [(hB.to_ring_filter_basis.to_add_group_filter_basis.nhds_has_basis a).mem_iff]
    simp only [exists_prop, exists_true_left]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      use i
      convert hi
      ext b
      constructor
      · intro h
        use b - a, h
        abel
      · rintro ⟨c, hc, rfl⟩
        simpa using hc
    · rintro ⟨i, hi⟩
      use B i, i, rfl
      rw [image_subset_iff]
      rintro b b_in
      apply hi
      simpa using b_in⟩
#align ring_subgroups_basis.has_basis_nhds RingSubgroupsBasis.hasBasis_nhds

/-- Given a subgroups basis, the basis elements as open additive subgroups in the associated
topology. -/
def openAddSubgroup (i : ι) : @OpenAddSubgroup A _ hB.topology :=
  { B i with
    is_open' := by
      letI := hB.topology
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.has_basis_nhds a).mem_iff]
      use i, trivial
      rintro b b_in
      simpa using (B i).add_mem a_in b_in }
#align ring_subgroups_basis.open_add_subgroup RingSubgroupsBasis.openAddSubgroup

-- see Note [nonarchimedean non instances]
theorem nonarchimedean : @NonarchimedeanRing A _ hB.topology :=
  by
  letI := hB.topology
  constructor
  intro U hU
  obtain ⟨i, -, hi : (B i : Set A) ⊆ U⟩ := hB.has_basis_nhds_zero.mem_iff.mp hU
  exact ⟨hB.open_add_subgroup i, hi⟩
#align ring_subgroups_basis.nonarchimedean RingSubgroupsBasis.nonarchimedean

end RingSubgroupsBasis

variable {ι R A : Type _} [CommRing R] [CommRing A] [Algebra R A]

/-- A family of submodules in a commutative `R`-algebra `A` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure SubmodulesRingBasis (B : ι → Submodule R A) : Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  leftMul : ∀ (a : A) (i), ∃ j, a • B j ≤ B i
  mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i
#align submodules_ring_basis SubmodulesRingBasis

namespace SubmodulesRingBasis

variable {B : ι → Submodule R A} (hB : SubmodulesRingBasis B)

theorem toRing_subgroups_basis (hB : SubmodulesRingBasis B) :
    RingSubgroupsBasis fun i => (B i).toAddSubgroup :=
  by
  apply RingSubgroupsBasis.of_comm (fun i => (B i).toAddSubgroup) hB.inter hB.mul
  intro a i
  rcases hB.left_mul a i with ⟨j, hj⟩
  use j
  rintro b (b_in : b ∈ B j)
  exact hj ⟨b, b_in, rfl⟩
#align submodules_ring_basis.to_ring_subgroups_basis SubmodulesRingBasis.toRing_subgroups_basis

/-- The topology associated to a basis of submodules in an algebra. -/
def topology [Nonempty ι] (hB : SubmodulesRingBasis B) : TopologicalSpace A :=
  hB.toRing_subgroups_basis.topology
#align submodules_ring_basis.topology SubmodulesRingBasis.topology

end SubmodulesRingBasis

variable {M : Type _} [AddCommGroup M] [Module R M]

/-- A family of submodules in an `R`-module `M` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `M` which is compatible with the module structure and
admits this family as a basis of neighborhoods of zero. -/
structure SubmodulesBasis [TopologicalSpace R] (B : ι → Submodule R M) : Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  smul : ∀ (m : M) (i : ι), ∀ᶠ a in 𝓝 (0 : R), a • m ∈ B i
#align submodules_basis SubmodulesBasis

namespace SubmodulesBasis

variable [TopologicalSpace R] [Nonempty ι] {B : ι → Submodule R M} (hB : SubmodulesBasis B)

include hB

/-- The image of a submodules basis is a module filter basis. -/
def toModuleFilterBasis : ModuleFilterBasis R M
    where
  sets := { U | ∃ i, U = B i }
  Nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    cases' hB.inter i j with k hk
    use B k, k, rfl, hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i, i, rfl
    rintro x ⟨y, z, y_in, z_in, rfl⟩
    exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i, i, rfl
    intro x x_in
    exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i, i, rfl
    simp
  smul' := by
    rintro _ ⟨i, rfl⟩
    use univ, univ_mem, B i, i, rfl
    rintro _ ⟨a, m, -, hm, rfl⟩
    exact (B i).smul_mem _ hm
  smul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i, i, rfl
    intro m
    exact (B i).smul_mem _
  smul_right' := by
    rintro m₀ _ ⟨i, rfl⟩
    exact hB.smul m₀ i
#align submodules_basis.to_module_filter_basis SubmodulesBasis.toModuleFilterBasis

/-- The topology associated to a basis of submodules in a module. -/
def topology : TopologicalSpace M :=
  hB.toModuleFilterBasis.toAddGroupFilterBasis.topology
#align submodules_basis.topology SubmodulesBasis.topology

/-- Given a submodules basis, the basis elements as open additive subgroups in the associated
topology. -/
def openAddSubgroup (i : ι) : @OpenAddSubgroup M _ hB.topology :=
  { (B i).toAddSubgroup with
    is_open' := by
      letI := hB.topology
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.to_module_filter_basis.to_add_group_filter_basis.nhds_has_basis a).mem_iff]
      use B i, i, rfl
      rintro - ⟨b, b_in, rfl⟩
      exact (B i).add_mem a_in b_in }
#align submodules_basis.open_add_subgroup SubmodulesBasis.openAddSubgroup

-- see Note [nonarchimedean non instances]
theorem nonarchimedean (hB : SubmodulesBasis B) : @NonarchimedeanAddGroup M _ hB.topology :=
  by
  letI := hB.topology
  constructor
  intro U hU
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : Set M) ⊆ U⟩ :=
    hB.to_module_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff.mp hU
  exact ⟨hB.open_add_subgroup i, hi⟩
#align submodules_basis.nonarchimedean SubmodulesBasis.nonarchimedean

library_note "nonarchimedean non instances"/--
The non archimedean subgroup basis lemmas cannot be instances because some instances
(such as `measure_theory.ae_eq_fun.add_monoid ` or `topological_add_group.to_has_continuous_add`)
cause the search for `@topological_add_group β ?m1 ?m2`, i.e. a search for a topological group where
the topology/group structure are unknown. -/


end SubmodulesBasis

section

/-
In this section, we check that, in a `R`-algebra `A` over a ring equipped with a topology,
a basis of `R`-submodules which is compatible with the topology on `R` is also a submodule basis
in the sense of `R`-modules (forgetting about the ring structure on `A`) and those two points of
view definitionaly gives the same topology on `A`.
-/
variable [TopologicalSpace R] {B : ι → Submodule R A} (hB : SubmodulesRingBasis B)
  (hsmul : ∀ (m : A) (i : ι), ∀ᶠ a : R in 𝓝 0, a • m ∈ B i)

theorem SubmodulesRingBasis.toSubmodulesBasis : SubmodulesBasis B :=
  { inter := hB.inter
    smul := hsmul }
#align submodules_ring_basis.to_submodules_basis SubmodulesRingBasis.toSubmodulesBasis

example [Nonempty ι] : hB.topology = (hB.toSubmodulesBasis hsmul).topology :=
  rfl

end

/-- Given a ring filter basis on a commutative ring `R`, define a compatibility condition
on a family of submodules of a `R`-module `M`. This compatibility condition allows to get
a topological module structure. -/
structure RingFilterBasis.SubmodulesBasis (BR : RingFilterBasis R) (B : ι → Submodule R M) :
  Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  smul : ∀ (m : M) (i : ι), ∃ U ∈ BR, U ⊆ (fun a => a • m) ⁻¹' B i
#align ring_filter_basis.submodules_basis RingFilterBasis.SubmodulesBasis

theorem RingFilterBasis.submodulesBasisIsBasis (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @SubmodulesBasis ι R _ M _ _ BR.topology B :=
  { inter := hB.inter
    smul := by
      letI := BR.topology
      intro m i
      rcases hB.smul m i with ⟨V, V_in, hV⟩
      exact mem_of_superset (BR.to_add_group_filter_basis.mem_nhds_zero V_in) hV }
#align ring_filter_basis.submodules_basis_is_basis RingFilterBasis.submodulesBasisIsBasis

/-- The module filter basis associated to a ring filter basis and a compatible submodule basis.
This allows to build a topological module structure compatible with the given module structure
and the topology associated to the given ring filter basis. -/
def RingFilterBasis.moduleFilterBasis [Nonempty ι] (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @ModuleFilterBasis R M _ BR.topology _ _ :=
  @SubmodulesBasis.toModuleFilterBasis ι R _ M _ _ BR.topology _ _ (BR.submodulesBasisIsBasis hB)
#align ring_filter_basis.module_filter_basis RingFilterBasis.moduleFilterBasis


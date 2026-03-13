/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Neighborhood bases for non-archimedean rings and modules

This file contains special families of filter bases on rings and modules that give rise to
non-archimedean topologies.

The main definition is `RingSubgroupsBasis` which is a predicate on a family of
additive subgroups of a ring. The predicate ensures there is a topology
`RingSubgroupsBasis.topology` which is compatible with a ring structure and admits the given
family as a basis of neighborhoods of zero. In particular, the given subgroups become open subgroups
(bundled in `RingSubgroupsBasis.openAddSubgroup`) and we get a non-archimedean topological ring
(`RingSubgroupsBasis.nonarchimedean`).

A special case of this construction is given by `SubmodulesBasis` where the subgroups are
sub-modules in a commutative algebra. This important example gives rise to the adic topology
(studied in its own file).
-/

@[expose] public section

open Set Filter Function Lattice

open Topology Filter Pointwise

/-- A family of additive subgroups on a ring `A` is a subgroups basis if it satisfies some
axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure RingSubgroupsBasis {A ι : Type*} [Ring A] (B : ι → AddSubgroup A) : Prop where
  /-- Condition for `B` to be a filter basis on `A`. -/
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  /-- For each set `B` in the submodule basis on `A`, there is another basis element `B'` such
  that the set-theoretic product `B' * B'` is in `B`. -/
  mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i
  /-- For any element `x : A` and any set `B` in the submodule basis on `A`,
  there is another basis element `B'` such that `B' * x` is in `B`. -/
  leftMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (x * ·) ⁻¹' B i
  /-- For any element `x : A` and any set `B` in the submodule basis on `A`,
  there is another basis element `B'` such that `x * B'` is in `B`. -/
  rightMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (· * x) ⁻¹' B i

namespace RingSubgroupsBasis

variable {A ι : Type*} [Ring A]

theorem of_comm {A ι : Type*} [CommRing A] (B : ι → AddSubgroup A)
    (inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j) (mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i)
    (leftMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (fun y : A => x * y) ⁻¹' B i) :
    RingSubgroupsBasis B :=
  { inter
    mul
    leftMul
    rightMul := fun x i ↦ (leftMul x i).imp fun j hj ↦ by simpa only [mul_comm] using hj }

/-- Every subgroups basis on a ring leads to a ring filter basis. -/
@[implicit_reducible]
def toRingFilterBasis [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B) :
    RingFilterBasis A where
  sets := { U | ∃ i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · rintro x ⟨y, y_in, z, z_in, rfl⟩
      exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro x x_in
      exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · simp
  mul' := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hB.mul i
    use B k
    constructor
    · use k
    · exact hk
  mul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hB.leftMul x₀ i
    use B k
    constructor
    · use k
    · exact hk
  mul_right' := by
    rintro x₀ _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hB.rightMul x₀ i
    use B k
    constructor
    · use k
    · exact hk

variable [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B)

theorem mem_addGroupFilterBasis_iff {V : Set A} :
    V ∈ hB.toRingFilterBasis.toAddGroupFilterBasis ↔ ∃ i, V = B i :=
  Iff.rfl

theorem mem_addGroupFilterBasis (i) : (B i : Set A) ∈ hB.toRingFilterBasis.toAddGroupFilterBasis :=
  ⟨i, rfl⟩

/-- The topology defined from a subgroups basis, admitting the given subgroups as a basis
of neighborhoods of zero. -/
@[implicit_reducible]
def topology : TopologicalSpace A :=
  hB.toRingFilterBasis.toAddGroupFilterBasis.topology

set_option backward.isDefEq.respectTransparency false in
theorem hasBasis_nhds_zero : HasBasis (@nhds A hB.topology 0) (fun _ => True) fun i => B i :=
  ⟨by
    intro s
    rw [hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact ⟨i, trivial, hi⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨B i, ⟨i, rfl⟩, hi⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem hasBasis_nhds (a : A) :
    HasBasis (@nhds A hB.topology a) (fun _ => True) fun i => { b | b - a ∈ B i } :=
  ⟨by
    intro s
    rw [(hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
    simp only [true_and]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      use i
      suffices h : { b : A | b - a ∈ B i } = (fun y => a + y) '' ↑(B i) by
        rw [h]
        assumption
      simp only [image_add_left, neg_add_eq_sub]
      ext b
      simp
    · rintro ⟨i, hi⟩
      use B i
      constructor
      · use i
      · rw [image_subset_iff]
        rintro b b_in
        apply hi
        simpa using b_in⟩

/-- Given a subgroups basis, the basis elements as open additive subgroups in the associated
topology. -/
def openAddSubgroup (i : ι) : @OpenAddSubgroup A _ hB.topology :=
  let _ := hB.topology
  { B i with
    isOpen' := by
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.hasBasis_nhds a).mem_iff]
      use i, trivial
      rintro b b_in
      simpa using (B i).add_mem a_in b_in }

set_option backward.isDefEq.respectTransparency false in
-- See note [non-Archimedean non-instances]
theorem nonarchimedean : @NonarchimedeanRing A _ hB.topology := by
  letI := hB.topology
  constructor
  intro U hU
  obtain ⟨i, -, hi : (B i : Set A) ⊆ U⟩ := hB.hasBasis_nhds_zero.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩

end RingSubgroupsBasis

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A family of submodules in a commutative `R`-algebra `A` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure SubmodulesRingBasis (B : ι → Submodule R A) : Prop where
  /-- Condition for `B` to be a filter basis on `A`. -/
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  /-- For any element `a : A` and any set `B` in the submodule basis on `A`,
  there is another basis element `B'` such that `a • B'` is in `B`. -/
  leftMul : ∀ (a : A) (i), ∃ j, a • B j ≤ B i
  /-- For each set `B` in the submodule basis on `A`, there is another basis element `B'` such
  that the set-theoretic product `B' * B'` is in `B`. -/
  mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i

namespace SubmodulesRingBasis

variable {B : ι → Submodule R A} (hB : SubmodulesRingBasis B)

theorem toRing_subgroups_basis (hB : SubmodulesRingBasis B) :
    RingSubgroupsBasis fun i => (B i).toAddSubgroup := by
  apply RingSubgroupsBasis.of_comm (fun i => (B i).toAddSubgroup) hB.inter hB.mul
  intro a i
  rcases hB.leftMul a i with ⟨j, hj⟩
  use j
  rintro b (b_in : b ∈ B j)
  exact hj ⟨b, b_in, rfl⟩

/-- The topology associated to a basis of submodules in an algebra. -/
@[implicit_reducible]
def topology [Nonempty ι] (hB : SubmodulesRingBasis B) : TopologicalSpace A :=
  hB.toRing_subgroups_basis.topology

end SubmodulesRingBasis

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A family of submodules in an `R`-module `M` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `M` which is compatible with the module structure and
admits this family as a basis of neighborhoods of zero. -/
structure SubmodulesBasis [TopologicalSpace R] (B : ι → Submodule R M) : Prop where
  /-- Condition for `B` to be a filter basis on `M`. -/
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  /-- For any element `m : M` and any set `B` in the basis, `a • m` lies in `B` for all
  `a` sufficiently close to `0`. -/
  smul : ∀ (m : M) (i : ι), ∀ᶠ a in 𝓝 (0 : R), a • m ∈ B i

namespace SubmodulesBasis

variable [TopologicalSpace R] [Nonempty ι] {B : ι → Submodule R M} (hB : SubmodulesBasis B)

/-- The image of a submodules basis is a module filter basis. -/
def toModuleFilterBasis : ModuleFilterBasis R M where
  sets := { U | ∃ i, U = B i }
  nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    use B k
    constructor
    · use k
    · exact hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · rintro x ⟨y, y_in, z, z_in, rfl⟩
      exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro x x_in
      exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · simp
  smul' := by
    rintro _ ⟨i, rfl⟩
    use univ
    constructor
    · exact univ_mem
    · use B i
      constructor
      · use i
      · rintro _ ⟨a, -, m, hm, rfl⟩
        exact (B i).smul_mem _ hm
  smul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i
    constructor
    · use i
    · intro m
      exact (B i).smul_mem _
  smul_right' := by
    rintro m₀ _ ⟨i, rfl⟩
    exact hB.smul m₀ i

/-- The topology associated to a basis of submodules in a module. -/
@[implicit_reducible]
def topology : TopologicalSpace M :=
  hB.toModuleFilterBasis.toAddGroupFilterBasis.topology

set_option backward.isDefEq.respectTransparency false in
/-- Given a submodules basis, the basis elements as open additive subgroups in the associated
topology. -/
def openAddSubgroup (i : ι) : @OpenAddSubgroup M _ hB.topology :=
  let _ := hB.topology
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

set_option backward.isDefEq.respectTransparency false in
-- See note [non-Archimedean non-instances]
theorem nonarchimedean (hB : SubmodulesBasis B) : @NonarchimedeanAddGroup M _ hB.topology := by
  letI := hB.topology
  constructor
  intro U hU
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : Set M) ⊆ U⟩ :=
    hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩

library_note «non-Archimedean non-instances» /--
The non-Archimedean subgroup basis lemmas cannot be instances because some instances
(such as `MeasureTheory.AEEqFun.instAddMonoid` or `IsTopologicalAddGroup.toContinuousAdd`)
cause the search for `@IsTopologicalAddGroup β ?m1 ?m2`, i.e. a search for a topological group where
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
  let _ := BR.topology
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

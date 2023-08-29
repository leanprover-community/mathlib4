/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Algebra.Module.Submodule.Pointwise

#align_import topology.algebra.nonarchimedean.bases from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

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
#align ring_subgroups_basis RingSubgroupsBasis

namespace RingSubgroupsBasis

variable {A ι : Type*} [Ring A]

theorem of_comm {A ι : Type*} [CommRing A] (B : ι → AddSubgroup A)
    (inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j) (mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i)
    (leftMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (fun y : A => x * y) ⁻¹' B i) :
    RingSubgroupsBasis B :=
  { inter
    mul
    leftMul
    rightMul := by
      intro x i
      -- ⊢ ∃ j, ↑(B j) ⊆ (fun x_1 => x_1 * x) ⁻¹' ↑(B i)
      cases' leftMul x i with j hj
      -- ⊢ ∃ j, ↑(B j) ⊆ (fun x_1 => x_1 * x) ⁻¹' ↑(B i)
      use j
      -- ⊢ ↑(B j) ⊆ (fun x_1 => x_1 * x) ⁻¹' ↑(B i)
      simpa [mul_comm] using hj }
      -- 🎉 no goals
#align ring_subgroups_basis.of_comm RingSubgroupsBasis.of_comm

/-- Every subgroups basis on a ring leads to a ring filter basis. -/
def toRingFilterBasis [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B) :
    RingFilterBasis A where
  sets := { U | ∃ i, U = B i }
  nonempty := by
    inhabit ι
    -- ⊢ Set.Nonempty {U | ∃ i, U = ↑(B i)}
    exact ⟨B default, default, rfl⟩
    -- 🎉 no goals
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    -- ⊢ ∃ z, z ∈ {U | ∃ i, U = ↑(B i)} ∧ z ⊆ ↑(B i) ∩ ↑(B j)
    cases' hB.inter i j with k hk
    -- ⊢ ∃ z, z ∈ {U | ∃ i, U = ↑(B i)} ∧ z ⊆ ↑(B i) ∩ ↑(B j)
    use B k
    -- ⊢ ↑(B k) ∈ {U | ∃ i, U = ↑(B i)} ∧ ↑(B k) ⊆ ↑(B i) ∩ ↑(B j)
    constructor
    -- ⊢ ↑(B k) ∈ {U | ∃ i, U = ↑(B i)}
    · use k
      -- 🎉 no goals
    · exact hk
      -- 🎉 no goals
  zero' := by
    rintro _ ⟨i, rfl⟩
    -- ⊢ 0 ∈ ↑(B i)
    exact (B i).zero_mem
    -- 🎉 no goals
  add' := by
    rintro _ ⟨i, rfl⟩
    -- ⊢ ∃ V, V ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    use B i
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    constructor
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    · use i
      -- 🎉 no goals
    · rintro x ⟨y, z, y_in, z_in, rfl⟩
      -- ⊢ (fun x x_1 => x + x_1) y z ∈ ↑(B i)
      exact (B i).add_mem y_in z_in
      -- 🎉 no goals
  neg' := by
    rintro _ ⟨i, rfl⟩
    -- ⊢ ∃ V, V ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    use B i
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    constructor
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    · use i
      -- 🎉 no goals
    · intro x x_in
      -- ⊢ x ∈ (fun x => -x) ⁻¹' ↑(B i)
      exact (B i).neg_mem x_in
      -- 🎉 no goals
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    -- ⊢ ∃ V, V ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    use B i
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    constructor
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    · use i
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
  mul' := by
    rintro _ ⟨i, rfl⟩
    -- ⊢ ∃ V, V ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V * V ⊆ ↑(B i)
    cases' hB.mul i with k hk
    -- ⊢ ∃ V, V ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V * V ⊆ ↑(B i)
    use B k
    -- ⊢ ↑(B k) ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ ↑(B k) * ↑(B k) ⊆ ↑(B i)
    constructor
    -- ⊢ ↑(B k) ∈ AddGroupFilterBasis.toFilterBasis.sets
    · use k
      -- 🎉 no goals
    · exact hk
      -- 🎉 no goals
  mul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    -- ⊢ ∃ V, V ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V ⊆ (fun x => x₀ * x) ⁻¹'  …
    cases' hB.leftMul x₀ i with k hk
    -- ⊢ ∃ V, V ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V ⊆ (fun x => x₀ * x) ⁻¹'  …
    use B k
    -- ⊢ ↑(B k) ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ ↑(B k) ⊆ (fun x => x₀ * x) …
    constructor
    -- ⊢ ↑(B k) ∈ AddGroupFilterBasis.toFilterBasis.sets
    · use k
      -- 🎉 no goals
    · exact hk
      -- 🎉 no goals
  mul_right' := by
    rintro x₀ _ ⟨i, rfl⟩
    -- ⊢ ∃ V, V ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V ⊆ (fun x => x * x₀) ⁻¹'  …
    cases' hB.rightMul x₀ i with k hk
    -- ⊢ ∃ V, V ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V ⊆ (fun x => x * x₀) ⁻¹'  …
    use B k
    -- ⊢ ↑(B k) ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ ↑(B k) ⊆ (fun x => x * x₀) …
    constructor
    -- ⊢ ↑(B k) ∈ AddGroupFilterBasis.toFilterBasis.sets
    · use k
      -- 🎉 no goals
    · exact hk
      -- 🎉 no goals
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
    -- ⊢ s ∈ 𝓝 0 ↔ ∃ i, True ∧ ↑(B i) ⊆ s
    rw [hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    -- ⊢ (∃ i, i ∈ RingFilterBasis.toAddGroupFilterBasis ∧ id i ⊆ s) ↔ ∃ i, True ∧ ↑( …
    constructor
    -- ⊢ (∃ i, i ∈ RingFilterBasis.toAddGroupFilterBasis ∧ id i ⊆ s) → ∃ i, True ∧ ↑( …
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      -- ⊢ ∃ i, True ∧ ↑(B i) ⊆ s
      exact ⟨i, trivial, hi⟩
      -- 🎉 no goals
    · rintro ⟨i, -, hi⟩
      -- ⊢ ∃ i, i ∈ RingFilterBasis.toAddGroupFilterBasis ∧ id i ⊆ s
      exact ⟨B i, ⟨i, rfl⟩, hi⟩⟩
      -- 🎉 no goals
#align ring_subgroups_basis.has_basis_nhds_zero RingSubgroupsBasis.hasBasis_nhds_zero

theorem hasBasis_nhds (a : A) :
    HasBasis (@nhds A hB.topology a) (fun _ => True) fun i => { b | b - a ∈ B i } :=
  ⟨by
    intro s
    -- ⊢ s ∈ 𝓝 a ↔ ∃ i, True ∧ {b | b - a ∈ B i} ⊆ s
    rw [(hB.toRingFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
    -- ⊢ (∃ i, i ∈ RingFilterBasis.toAddGroupFilterBasis ∧ (fun y => a + y) '' i ⊆ s) …
    simp only [true_and]
    -- ⊢ (∃ i, i ∈ RingFilterBasis.toAddGroupFilterBasis ∧ (fun y => a + y) '' i ⊆ s) …
    constructor
    -- ⊢ (∃ i, i ∈ RingFilterBasis.toAddGroupFilterBasis ∧ (fun y => a + y) '' i ⊆ s) …
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      -- ⊢ ∃ i, {b | b - a ∈ B i} ⊆ s
      use i
      -- ⊢ {b | b - a ∈ B i} ⊆ s
      suffices h : { b : A | b - a ∈ B i } = (fun y => a + y) '' ↑(B i)
      -- ⊢ {b | b - a ∈ B i} ⊆ s
      · rw [h]
        -- ⊢ (fun y => a + y) '' ↑(B i) ⊆ s
        assumption
        -- 🎉 no goals
      simp only [image_add_left, neg_add_eq_sub]
      -- ⊢ {b | b - a ∈ B i} = (fun x => x - a) ⁻¹' ↑(B i)
      ext b
      -- ⊢ b ∈ {b | b - a ∈ B i} ↔ b ∈ (fun x => x - a) ⁻¹' ↑(B i)
      simp
      -- 🎉 no goals
    · rintro ⟨i, hi⟩
      -- ⊢ ∃ i, i ∈ RingFilterBasis.toAddGroupFilterBasis ∧ (fun y => a + y) '' i ⊆ s
      use B i
      -- ⊢ ↑(B i) ∈ RingFilterBasis.toAddGroupFilterBasis ∧ (fun y => a + y) '' ↑(B i)  …
      constructor
      -- ⊢ ↑(B i) ∈ RingFilterBasis.toAddGroupFilterBasis
      · use i
        -- 🎉 no goals
      · rw [image_subset_iff]
        -- ⊢ ↑(B i) ⊆ (fun y => a + y) ⁻¹' s
        rintro b b_in
        -- ⊢ b ∈ (fun y => a + y) ⁻¹' s
        apply hi
        -- ⊢ (fun y => a + y) b ∈ {b | b - a ∈ B i}
        simpa using b_in⟩
        -- 🎉 no goals
#align ring_subgroups_basis.has_basis_nhds RingSubgroupsBasis.hasBasis_nhds

/-- Given a subgroups basis, the basis elements as open additive subgroups in the associated
topology. -/
def openAddSubgroup (i : ι) : @OpenAddSubgroup A _ hB.topology :=
  -- Porting note: failed to synthesize instance `TopologicalSpace A`
  let _ := hB.topology
  { B i with
    isOpen' := by
      rw [isOpen_iff_mem_nhds]
      -- ⊢ ∀ (a : A), a ∈ { toAddSubmonoid := src✝.toAddSubmonoid, neg_mem' := (_ : ∀ { …
      intro a a_in
      -- ⊢ { toAddSubmonoid := src✝.toAddSubmonoid, neg_mem' := (_ : ∀ {x : A}, x ∈ src …
      rw [(hB.hasBasis_nhds a).mem_iff]
      -- ⊢ ∃ i, True ∧ {b | b - a ∈ B i} ⊆ { toAddSubmonoid := src✝.toAddSubmonoid, neg …
      use i, trivial
      -- ⊢ {b | b - a ∈ B i} ⊆ { toAddSubmonoid := src✝.toAddSubmonoid, neg_mem' := (_  …
      rintro b b_in
      -- ⊢ b ∈ { toAddSubmonoid := src✝.toAddSubmonoid, neg_mem' := (_ : ∀ {x : A}, x ∈ …
      simpa using (B i).add_mem a_in b_in }
      -- 🎉 no goals
#align ring_subgroups_basis.open_add_subgroup RingSubgroupsBasis.openAddSubgroup

-- see Note [nonarchimedean non instances]
theorem nonarchimedean : @NonarchimedeanRing A _ hB.topology := by
  letI := hB.topology
  -- ⊢ NonarchimedeanRing A
  constructor
  -- ⊢ ∀ (U : Set A), U ∈ 𝓝 0 → ∃ V, ↑V ⊆ U
  intro U hU
  -- ⊢ ∃ V, ↑V ⊆ U
  obtain ⟨i, -, hi : (B i : Set A) ⊆ U⟩ := hB.hasBasis_nhds_zero.mem_iff.mp hU
  -- ⊢ ∃ V, ↑V ⊆ U
  exact ⟨hB.openAddSubgroup i, hi⟩
  -- 🎉 no goals
#align ring_subgroups_basis.nonarchimedean RingSubgroupsBasis.nonarchimedean

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
#align submodules_ring_basis SubmodulesRingBasis

namespace SubmodulesRingBasis

variable {B : ι → Submodule R A} (hB : SubmodulesRingBasis B)

theorem toRing_subgroups_basis (hB : SubmodulesRingBasis B) :
    RingSubgroupsBasis fun i => (B i).toAddSubgroup := by
  apply RingSubgroupsBasis.of_comm (fun i => (B i).toAddSubgroup) hB.inter hB.mul
  -- ⊢ ∀ (x : A) (i : ι), ∃ j, ↑(Submodule.toAddSubgroup (B j)) ⊆ (fun y => x * y)  …
  intro a i
  -- ⊢ ∃ j, ↑(Submodule.toAddSubgroup (B j)) ⊆ (fun y => a * y) ⁻¹' ↑(Submodule.toA …
  rcases hB.leftMul a i with ⟨j, hj⟩
  -- ⊢ ∃ j, ↑(Submodule.toAddSubgroup (B j)) ⊆ (fun y => a * y) ⁻¹' ↑(Submodule.toA …
  use j
  -- ⊢ ↑(Submodule.toAddSubgroup (B j)) ⊆ (fun y => a * y) ⁻¹' ↑(Submodule.toAddSub …
  rintro b (b_in : b ∈ B j)
  -- ⊢ b ∈ (fun y => a * y) ⁻¹' ↑(Submodule.toAddSubgroup (B i))
  exact hj ⟨b, b_in, rfl⟩
  -- 🎉 no goals
#align submodules_ring_basis.to_ring_subgroups_basis SubmodulesRingBasis.toRing_subgroups_basis

/-- The topology associated to a basis of submodules in an algebra. -/
def topology [Nonempty ι] (hB : SubmodulesRingBasis B) : TopologicalSpace A :=
  hB.toRing_subgroups_basis.topology
#align submodules_ring_basis.topology SubmodulesRingBasis.topology

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
#align submodules_basis SubmodulesBasis

namespace SubmodulesBasis

variable [TopologicalSpace R] [Nonempty ι] {B : ι → Submodule R M} (hB : SubmodulesBasis B)

/-- The image of a submodules basis is a module filter basis. -/
def toModuleFilterBasis : ModuleFilterBasis R M where
  sets := { U | ∃ i, U = B i }
  nonempty := by
    inhabit ι
    -- ⊢ Set.Nonempty {U | ∃ i, U = ↑(B i)}
    exact ⟨B default, default, rfl⟩
    -- 🎉 no goals
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    -- ⊢ ∃ z, z ∈ {U | ∃ i, U = ↑(B i)} ∧ z ⊆ ↑(B i) ∩ ↑(B j)
    cases' hB.inter i j with k hk
    -- ⊢ ∃ z, z ∈ {U | ∃ i, U = ↑(B i)} ∧ z ⊆ ↑(B i) ∩ ↑(B j)
    use B k
    -- ⊢ ↑(B k) ∈ {U | ∃ i, U = ↑(B i)} ∧ ↑(B k) ⊆ ↑(B i) ∩ ↑(B j)
    constructor
    -- ⊢ ↑(B k) ∈ {U | ∃ i, U = ↑(B i)}
    · use k
      -- 🎉 no goals
    · exact hk
      -- 🎉 no goals
  zero' := by
    rintro _ ⟨i, rfl⟩
    -- ⊢ 0 ∈ ↑(B i)
    exact (B i).zero_mem
    -- 🎉 no goals
  add' := by
    rintro _ ⟨i, rfl⟩
    -- ⊢ ∃ V, V ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    use B i
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    constructor
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    · use i
      -- 🎉 no goals
    · rintro x ⟨y, z, y_in, z_in, rfl⟩
      -- ⊢ (fun x x_1 => x + x_1) y z ∈ ↑(B i)
      exact (B i).add_mem y_in z_in
      -- 🎉 no goals
  neg' := by
    rintro _ ⟨i, rfl⟩
    -- ⊢ ∃ V, V ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    use B i
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    constructor
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    · use i
      -- 🎉 no goals
    · intro x x_in
      -- ⊢ x ∈ (fun x => -x) ⁻¹' ↑(B i)
      exact (B i).neg_mem x_in
      -- 🎉 no goals
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    -- ⊢ ∃ V, V ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    use B i
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    constructor
    -- ⊢ ↑(B i) ∈ { sets := {U | ∃ i, U = ↑(B i)}, nonempty := (_ : ∃ x, x ∈ {U | ∃ i …
    · use i
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
  smul' := by
    rintro _ ⟨i, rfl⟩
    -- ⊢ ∃ V, V ∈ 𝓝 0 ∧ ∃ W, W ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V • W ⊆ ↑(B …
    use univ
    -- ⊢ univ ∈ 𝓝 0 ∧ ∃ W, W ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ univ • W ⊆ ↑( …
    constructor
    -- ⊢ univ ∈ 𝓝 0
    · exact univ_mem
      -- 🎉 no goals
    · use B i
      -- ⊢ ↑(B i) ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ univ • ↑(B i) ⊆ ↑(B i)
      constructor
      -- ⊢ ↑(B i) ∈ AddGroupFilterBasis.toFilterBasis.sets
      · use i
        -- 🎉 no goals
      · rintro _ ⟨a, m, -, hm, rfl⟩
        -- ⊢ (fun x x_1 => x • x_1) a m ∈ ↑(B i)
        exact (B i).smul_mem _ hm
        -- 🎉 no goals
  smul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    -- ⊢ ∃ V, V ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ V ⊆ (fun x => x₀ • x) ⁻¹'  …
    use B i
    -- ⊢ ↑(B i) ∈ AddGroupFilterBasis.toFilterBasis.sets ∧ ↑(B i) ⊆ (fun x => x₀ • x) …
    constructor
    -- ⊢ ↑(B i) ∈ AddGroupFilterBasis.toFilterBasis.sets
    · use i
      -- 🎉 no goals
    · intro m
      -- ⊢ m ∈ ↑(B i) → m ∈ (fun x => x₀ • x) ⁻¹' ↑(B i)
      exact (B i).smul_mem _
      -- 🎉 no goals
  smul_right' := by
    rintro m₀ _ ⟨i, rfl⟩
    -- ⊢ ∀ᶠ (x : R) in 𝓝 0, x • m₀ ∈ ↑(B i)
    exact hB.smul m₀ i
    -- 🎉 no goals
#align submodules_basis.to_module_filter_basis SubmodulesBasis.toModuleFilterBasis

/-- The topology associated to a basis of submodules in a module. -/
def topology : TopologicalSpace M :=
  hB.toModuleFilterBasis.toAddGroupFilterBasis.topology
#align submodules_basis.topology SubmodulesBasis.topology

/-- Given a submodules basis, the basis elements as open additive subgroups in the associated
topology. -/
def openAddSubgroup (i : ι) : @OpenAddSubgroup M _ hB.topology :=
  let _ := hB.topology -- Porting note: failed to synthesize instance `TopologicalSpace A`
  { (B i).toAddSubgroup with
    isOpen' := by
      letI := hB.topology
      -- ⊢ IsOpen { toAddSubmonoid := src✝.toAddSubmonoid, neg_mem' := (_ : ∀ {x : M},  …
      rw [isOpen_iff_mem_nhds]
      -- ⊢ ∀ (a : M), a ∈ { toAddSubmonoid := src✝.toAddSubmonoid, neg_mem' := (_ : ∀ { …
      intro a a_in
      -- ⊢ { toAddSubmonoid := src✝.toAddSubmonoid, neg_mem' := (_ : ∀ {x : M}, x ∈ src …
      rw [(hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_hasBasis a).mem_iff]
      -- ⊢ ∃ i, i ∈ (toModuleFilterBasis hB).toAddGroupFilterBasis ∧ (fun y => a + y) ' …
      use B i
      -- ⊢ ↑(B i) ∈ (toModuleFilterBasis hB).toAddGroupFilterBasis ∧ (fun y => a + y) ' …
      constructor
      -- ⊢ ↑(B i) ∈ (toModuleFilterBasis hB).toAddGroupFilterBasis
      · use i
        -- 🎉 no goals
      · rintro - ⟨b, b_in, rfl⟩
        -- ⊢ (fun y => a + y) b ∈ { toAddSubmonoid := src✝.toAddSubmonoid, neg_mem' := (_ …
        exact (B i).add_mem a_in b_in }
        -- 🎉 no goals
#align submodules_basis.open_add_subgroup SubmodulesBasis.openAddSubgroup

-- see Note [nonarchimedean non instances]
theorem nonarchimedean (hB : SubmodulesBasis B) : @NonarchimedeanAddGroup M _ hB.topology := by
  letI := hB.topology
  -- ⊢ NonarchimedeanAddGroup M
  constructor
  -- ⊢ ∀ (U : Set M), U ∈ 𝓝 0 → ∃ V, ↑V ⊆ U
  intro U hU
  -- ⊢ ∃ V, ↑V ⊆ U
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : Set M) ⊆ U⟩ :=
    hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp hU
  exact ⟨hB.openAddSubgroup i, hi⟩
  -- 🎉 no goals
#align submodules_basis.nonarchimedean SubmodulesBasis.nonarchimedean

library_note "nonarchimedean non instances"/--
The non archimedean subgroup basis lemmas cannot be instances because some instances
(such as `MeasureTheory.AEEqFun.instAddMonoid ` or `topological_add_group.to_has_continuous_add`)
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

theorem SubmodulesRingBasis.toSubmodulesBasis : SubmodulesBasis B :=
  { inter := hB.inter
    smul := hsmul }
#align submodules_ring_basis.to_submodules_basis SubmodulesRingBasis.toSubmodulesBasis

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
#align ring_filter_basis.submodules_basis RingFilterBasis.SubmodulesBasis

theorem RingFilterBasis.submodulesBasisIsBasis (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @_root_.SubmodulesBasis ι R _ M _ _ BR.topology B :=
  let _ := BR.topology -- Porting note: failed to synthesize instance `TopologicalSpace R`
  { inter := hB.inter
    smul := by
      letI := BR.topology
      -- ⊢ ∀ (m : M) (i : ι), ∀ᶠ (a : R) in 𝓝 0, a • m ∈ B i
      intro m i
      -- ⊢ ∀ᶠ (a : R) in 𝓝 0, a • m ∈ B i
      rcases hB.smul m i with ⟨V, V_in, hV⟩
      -- ⊢ ∀ᶠ (a : R) in 𝓝 0, a • m ∈ B i
      exact mem_of_superset (BR.toAddGroupFilterBasis.mem_nhds_zero V_in) hV }
      -- 🎉 no goals
#align ring_filter_basis.submodules_basis_is_basis RingFilterBasis.submodulesBasisIsBasis

/-- The module filter basis associated to a ring filter basis and a compatible submodule basis.
This allows to build a topological module structure compatible with the given module structure
and the topology associated to the given ring filter basis. -/
def RingFilterBasis.moduleFilterBasis [Nonempty ι] (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @ModuleFilterBasis R M _ BR.topology _ _ :=
  @SubmodulesBasis.toModuleFilterBasis ι R _ M _ _ BR.topology _ _ (BR.submodulesBasisIsBasis hB)
#align ring_filter_basis.module_filter_basis RingFilterBasis.moduleFilterBasis

/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.nonarchimedean.adic_topology
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.Topology.Algebra.Nonarchimedean.Bases
import Mathbin.Topology.UniformSpace.Completion
import Mathbin.Topology.Algebra.UniformRing

/-!
# Adic topology

Given a commutative ring `R` and an ideal `I` in `R`, this file constructs the unique
topology on `R` which is compatible with the ring structure and such that a set is a neighborhood
of zero if and only if it contains a power of `I`. This topology is non-archimedean: every
neighborhood of zero contains an open subgroup, namely a power of `I`.

It also studies the predicate `is_adic` which states that a given topological ring structure is
adic, proving a characterization and showing that raising an ideal to a positive power does not
change the associated topology.

Finally, it defines `with_ideal`, a class registering an ideal in a ring and providing the
corresponding adic topology to the type class inference system.


## Main definitions and results

* `ideal.adic_basis`: the basis of submodules given by powers of an ideal.
* `ideal.adic_topology`: the adic topology associated to an ideal. It has the above basis
  for neighborhoods of zero.
* `ideal.nonarchimedean`: the adic topology is non-archimedean
* `is_ideal_adic_iff`: A topological ring is `J`-adic if and only if it admits the powers of `J` as
  a basis of open neighborhoods of zero.
* `with_ideal`: a class registering an ideal in a ring.

## Implementation notes

The `I`-adic topology on a ring `R` has a contrived definition using `I^n • ⊤` instead of `I`
to make sure it is definitionally equal to the `I`-topology on `R` seen as a `R`-module.

-/


variable {R : Type _} [CommRing R]

open Set TopologicalAddGroup Submodule Filter

open Topology Pointwise

namespace Ideal

theorem adic_basis (I : Ideal R) : SubmodulesRingBasis fun n : ℕ => (I ^ n • ⊤ : Ideal R) :=
  { inter := by
      suffices ∀ i j : ℕ, ∃ k, I ^ k ≤ I ^ i ∧ I ^ k ≤ I ^ j by simpa
      intro i j
      exact ⟨max i j, pow_le_pow (le_max_left i j), pow_le_pow (le_max_right i j)⟩
    leftMul := by
      suffices ∀ (a : R) (i : ℕ), ∃ j : ℕ, a • I ^ j ≤ I ^ i by simpa
      intro r n
      use n
      rintro a ⟨x, hx, rfl⟩
      exact (I ^ n).smul_mem r hx
    mul := by
      suffices ∀ i : ℕ, ∃ j : ℕ, ↑(I ^ j) * ↑(I ^ j) ⊆ ↑(I ^ i) by simpa
      intro n
      use n
      rintro a ⟨x, b, hx, hb, rfl⟩
      exact (I ^ n).smul_mem x hb }
#align ideal.adic_basis Ideal.adic_basis

/-- The adic ring filter basis associated to an ideal `I` is made of powers of `I`. -/
def ringFilterBasis (I : Ideal R) :=
  I.adic_basis.toRing_subgroups_basis.toRingFilterBasis
#align ideal.ring_filter_basis Ideal.ringFilterBasis

/-- The adic topology associated to an ideal `I`. This topology admits powers of `I` as a basis of
neighborhoods of zero. It is compatible with the ring structure and is non-archimedean. -/
def adicTopology (I : Ideal R) : TopologicalSpace R :=
  (adic_basis I).topology
#align ideal.adic_topology Ideal.adicTopology

theorem nonarchimedean (I : Ideal R) : @NonarchimedeanRing R _ I.adicTopology :=
  I.adic_basis.toRing_subgroups_basis.nonarchimedean
#align ideal.nonarchimedean Ideal.nonarchimedean

/-- For the `I`-adic topology, the neighborhoods of zero has basis given by the powers of `I`. -/
theorem hasBasis_nhds_zero_adic (I : Ideal R) :
    HasBasis (@nhds R I.adicTopology (0 : R)) (fun n : ℕ => True) fun n =>
      ((I ^ n : Ideal R) : Set R) :=
  ⟨by
    intro U
    rw [I.ring_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, h⟩
      replace h : ↑(I ^ i) ⊆ U := by simpa using h
      use i, trivial, h
    · rintro ⟨i, -, h⟩
      exact ⟨(I ^ i : Ideal R), ⟨i, by simp⟩, h⟩⟩
#align ideal.has_basis_nhds_zero_adic Ideal.hasBasis_nhds_zero_adic

theorem hasBasis_nhds_adic (I : Ideal R) (x : R) :
    HasBasis (@nhds R I.adicTopology x) (fun n : ℕ => True) fun n =>
      (fun y => x + y) '' (I ^ n : Ideal R) :=
  by
  letI := I.adic_topology
  have := I.has_basis_nhds_zero_adic.map fun y => x + y
  rwa [map_add_left_nhds_zero x] at this
#align ideal.has_basis_nhds_adic Ideal.hasBasis_nhds_adic

variable (I : Ideal R) (M : Type _) [AddCommGroup M] [Module R M]

theorem adic_module_basis :
    I.RingFilterBasis.SubmodulesBasis fun n : ℕ => I ^ n • (⊤ : Submodule R M) :=
  { inter := fun i j =>
      ⟨max i j,
        le_inf_iff.mpr
          ⟨smul_mono_left <| pow_le_pow (le_max_left i j),
            smul_mono_left <| pow_le_pow (le_max_right i j)⟩⟩
    smul := fun m i =>
      ⟨(I ^ i • ⊤ : Ideal R), ⟨i, rfl⟩, fun a a_in =>
        by
        replace a_in : a ∈ I ^ i := by simpa [(I ^ i).mul_top] using a_in
        exact smul_mem_smul a_in mem_top⟩ }
#align ideal.adic_module_basis Ideal.adic_module_basis

/-- The topology on a `R`-module `M` associated to an ideal `M`. Submodules $I^n M$,
written `I^n • ⊤` form a basis of neighborhoods of zero. -/
def adicModuleTopology : TopologicalSpace M :=
  @ModuleFilterBasis.topology R M _ I.adic_basis.topology _ _
    (I.RingFilterBasis.ModuleFilterBasis (I.adic_module_basis M))
#align ideal.adic_module_topology Ideal.adicModuleTopology

/-- The elements of the basis of neighborhoods of zero for the `I`-adic topology
on a `R`-module `M`, seen as open additive subgroups of `M`. -/
def openAddSubgroup (n : ℕ) : @OpenAddSubgroup R _ I.adicTopology :=
  { (I ^ n).toAddSubgroup with
    is_open' := by
      letI := I.adic_topology
      convert(I.adic_basis.to_ring_subgroups_basis.open_add_subgroup n).IsOpen
      simp }
#align ideal.open_add_subgroup Ideal.openAddSubgroup

end Ideal

section IsAdic

/-- Given a topology on a ring `R` and an ideal `J`, `is_adic J` means the topology is the
`J`-adic one. -/
def IsAdic [H : TopologicalSpace R] (J : Ideal R) : Prop :=
  H = J.adicTopology
#align is_adic IsAdic

/-- A topological ring is `J`-adic if and only if it admits the powers of `J` as a basis of
open neighborhoods of zero. -/
theorem isAdic_iff [top : TopologicalSpace R] [TopologicalRing R] {J : Ideal R} :
    IsAdic J ↔
      (∀ n : ℕ, IsOpen ((J ^ n : Ideal R) : Set R)) ∧
        ∀ s ∈ 𝓝 (0 : R), ∃ n : ℕ, ((J ^ n : Ideal R) : Set R) ⊆ s :=
  by
  constructor
  · intro H
    change _ = _ at H
    rw [H]
    letI := J.adic_topology
    constructor
    · intro n
      exact (J.open_add_subgroup n).is_open'
    · intro s hs
      simpa using J.has_basis_nhds_zero_adic.mem_iff.mp hs
  · rintro ⟨H₁, H₂⟩
    apply TopologicalAddGroup.ext
    · apply @TopologicalRing.to_topologicalAddGroup
    · apply (RingSubgroupsBasis.toRingFilterBasis _).toAddGroupFilterBasis.isTopologicalAddGroup
    · ext s
      letI := Ideal.adic_basis J
      rw [J.has_basis_nhds_zero_adic.mem_iff]
      constructor <;> intro H
      · rcases H₂ s H with ⟨n, h⟩
        use n, trivial, h
      · rcases H with ⟨n, -, hn⟩
        rw [mem_nhds_iff]
        refine' ⟨_, hn, H₁ n, (J ^ n).zero_mem⟩
#align is_adic_iff isAdic_iff

variable [TopologicalSpace R] [TopologicalRing R]

theorem is_ideal_adic_pow {J : Ideal R} (h : IsAdic J) {n : ℕ} (hn : 0 < n) : IsAdic (J ^ n) :=
  by
  rw [isAdic_iff] at h⊢
  constructor
  · intro m
    rw [← pow_mul]
    apply h.left
  · intro V hV
    cases' h.right V hV with m hm
    use m
    refine' Set.Subset.trans _ hm
    cases n
    · exfalso
      exact Nat.not_succ_le_zero 0 hn
    rw [← pow_mul, Nat.succ_mul]
    apply Ideal.pow_le_pow
    apply Nat.le_add_left
#align is_ideal_adic_pow is_ideal_adic_pow

theorem is_bot_adic_iff {A : Type _} [CommRing A] [TopologicalSpace A] [TopologicalRing A] :
    IsAdic (⊥ : Ideal A) ↔ DiscreteTopology A :=
  by
  rw [isAdic_iff]
  constructor
  · rintro ⟨h, h'⟩
    rw [discreteTopology_iff_open_singleton_zero]
    simpa using h 1
  · intros
    constructor
    · simp
    · intro U U_nhds
      use 1
      simp [mem_of_mem_nhds U_nhds]
#align is_bot_adic_iff is_bot_adic_iff

end IsAdic

/-- The ring `R` is equipped with a preferred ideal. -/
class WithIdeal (R : Type _) [CommRing R] where
  i : Ideal R
#align with_ideal WithIdeal

namespace WithIdeal

variable (R) [WithIdeal R]

instance (priority := 100) : TopologicalSpace R :=
  i.adicTopology

instance (priority := 100) : NonarchimedeanRing R :=
  RingSubgroupsBasis.nonarchimedean _

instance (priority := 100) : UniformSpace R :=
  TopologicalAddGroup.toUniformSpace R

instance (priority := 100) : UniformAddGroup R :=
  comm_topologicalAddGroup_is_uniform

/-- The adic topology on a `R` module coming from the ideal `with_ideal.I`.
This cannot be an instance because `R` cannot be inferred from `M`. -/
def topologicalSpaceModule (M : Type _) [AddCommGroup M] [Module R M] : TopologicalSpace M :=
  (i : Ideal R).adicModuleTopology M
#align with_ideal.topological_space_module WithIdeal.topologicalSpaceModule

/-
The next examples are kept to make sure potential future refactors won't break the instance
chaining.
-/
example : NonarchimedeanRing R := by infer_instance

example : TopologicalRing (UniformSpace.Completion R) := by infer_instance

example (M : Type _) [AddCommGroup M] [Module R M] :
    @TopologicalAddGroup M (WithIdeal.topologicalSpaceModule R M) _ := by infer_instance

example (M : Type _) [AddCommGroup M] [Module R M] :
    @ContinuousSMul R M _ _ (WithIdeal.topologicalSpaceModule R M) := by infer_instance

example (M : Type _) [AddCommGroup M] [Module R M] :
    @NonarchimedeanAddGroup M _ (WithIdeal.topologicalSpaceModule R M) :=
  SubmodulesBasis.nonarchimedean _

end WithIdeal


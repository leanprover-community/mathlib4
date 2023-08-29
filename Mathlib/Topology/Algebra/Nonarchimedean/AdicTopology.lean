/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.UniformRing

#align_import topology.algebra.nonarchimedean.adic_topology from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Adic topology

Given a commutative ring `R` and an ideal `I` in `R`, this file constructs the unique
topology on `R` which is compatible with the ring structure and such that a set is a neighborhood
of zero if and only if it contains a power of `I`. This topology is non-archimedean: every
neighborhood of zero contains an open subgroup, namely a power of `I`.

It also studies the predicate `IsAdic` which states that a given topological ring structure is
adic, proving a characterization and showing that raising an ideal to a positive power does not
change the associated topology.

Finally, it defines `WithIdeal`, a class registering an ideal in a ring and providing the
corresponding adic topology to the type class inference system.


## Main definitions and results

* `Ideal.adic_basis`: the basis of submodules given by powers of an ideal.
* `Ideal.adicTopology`: the adic topology associated to an ideal. It has the above basis
  for neighborhoods of zero.
* `Ideal.nonarchimedean`: the adic topology is non-archimedean
* `isAdic_iff`: A topological ring is `J`-adic if and only if it admits the powers of `J` as
  a basis of open neighborhoods of zero.
* `WithIdeal`: a class registering an ideal in a ring.

## Implementation notes

The `I`-adic topology on a ring `R` has a contrived definition using `I^n • ⊤` instead of `I`
to make sure it is definitionally equal to the `I`-topology on `R` seen as an `R`-module.

-/


variable {R : Type*} [CommRing R]

open Set TopologicalAddGroup Submodule Filter

open Topology Pointwise

namespace Ideal

theorem adic_basis (I : Ideal R) : SubmodulesRingBasis fun n : ℕ => (I ^ n • ⊤ : Ideal R) :=
  { inter := by
      suffices ∀ i j : ℕ, ∃ k, I ^ k ≤ I ^ i ∧ I ^ k ≤ I ^ j by
        simpa only [smul_eq_mul, mul_top, Algebra.id.map_eq_id, map_id, le_inf_iff] using this
      intro i j
      -- ⊢ ∃ k, I ^ k ≤ I ^ i ∧ I ^ k ≤ I ^ j
      exact ⟨max i j, pow_le_pow (le_max_left i j), pow_le_pow (le_max_right i j)⟩
      -- 🎉 no goals
    leftMul := by
      suffices ∀ (a : R) (i : ℕ), ∃ j : ℕ, a • I ^ j ≤ I ^ i by
        simpa only [smul_top_eq_map, Algebra.id.map_eq_id, map_id] using this
      intro r n
      -- ⊢ ∃ j, r • I ^ j ≤ I ^ n
      use n
      -- ⊢ r • I ^ n ≤ I ^ n
      rintro a ⟨x, hx, rfl⟩
      -- ⊢ ↑(DistribMulAction.toLinearMap R R r) x ∈ I ^ n
      exact (I ^ n).smul_mem r hx
      -- 🎉 no goals
    mul := by
      suffices ∀ i : ℕ, ∃ j : ℕ, (I ^ j: Set R) * (I ^ j : Set R) ⊆ (I ^ i : Set R) by
        simpa only [smul_top_eq_map, Algebra.id.map_eq_id, map_id] using this
      intro n
      -- ⊢ ∃ j, ↑(I ^ j) * ↑(I ^ j) ⊆ ↑(I ^ n)
      use n
      -- ⊢ ↑(I ^ n) * ↑(I ^ n) ⊆ ↑(I ^ n)
      rintro a ⟨x, b, _hx, hb, rfl⟩
      -- ⊢ (fun x x_1 => x * x_1) x b ∈ ↑(I ^ n)
      exact (I ^ n).smul_mem x hb }
      -- 🎉 no goals
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
    HasBasis (@nhds R I.adicTopology (0 : R)) (fun _n : ℕ => True) fun n =>
      ((I ^ n : Ideal R) : Set R) :=
  ⟨by
    intro U
    -- ⊢ U ∈ 𝓝 0 ↔ ∃ i, True ∧ ↑(I ^ i) ⊆ U
    rw [I.ringFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    -- ⊢ (∃ i, i ∈ RingFilterBasis.toAddGroupFilterBasis ∧ id i ⊆ U) ↔ ∃ i, True ∧ ↑( …
    constructor
    -- ⊢ (∃ i, i ∈ RingFilterBasis.toAddGroupFilterBasis ∧ id i ⊆ U) → ∃ i, True ∧ ↑( …
    · rintro ⟨-, ⟨i, rfl⟩, h⟩
      -- ⊢ ∃ i, True ∧ ↑(I ^ i) ⊆ U
      replace h : ↑(I ^ i) ⊆ U := by simpa using h
      -- ⊢ ∃ i, True ∧ ↑(I ^ i) ⊆ U
      exact ⟨i, trivial, h⟩
      -- 🎉 no goals
    · rintro ⟨i, -, h⟩
      -- ⊢ ∃ i, i ∈ RingFilterBasis.toAddGroupFilterBasis ∧ id i ⊆ U
      exact ⟨(I ^ i : Ideal R), ⟨i, by simp⟩, h⟩⟩
      -- 🎉 no goals
#align ideal.has_basis_nhds_zero_adic Ideal.hasBasis_nhds_zero_adic

theorem hasBasis_nhds_adic (I : Ideal R) (x : R) :
    HasBasis (@nhds R I.adicTopology x) (fun _n : ℕ => True) fun n =>
      (fun y => x + y) '' (I ^ n : Ideal R) := by
  letI := I.adicTopology
  -- ⊢ HasBasis (𝓝 x) (fun _n => True) fun n => (fun y => x + y) '' ↑(I ^ n)
  have := I.hasBasis_nhds_zero_adic.map fun y => x + y
  -- ⊢ HasBasis (𝓝 x) (fun _n => True) fun n => (fun y => x + y) '' ↑(I ^ n)
  rwa [map_add_left_nhds_zero x] at this
  -- 🎉 no goals
#align ideal.has_basis_nhds_adic Ideal.hasBasis_nhds_adic

variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

theorem adic_module_basis :
    I.ringFilterBasis.SubmodulesBasis fun n : ℕ => I ^ n • (⊤ : Submodule R M) :=
  { inter := fun i j =>
      ⟨max i j,
        le_inf_iff.mpr
          ⟨smul_mono_left <| pow_le_pow (le_max_left i j),
            smul_mono_left <| pow_le_pow (le_max_right i j)⟩⟩
    smul := fun m i =>
      ⟨(I ^ i • ⊤ : Ideal R), ⟨i, by simp⟩, fun a a_in => by
                                     -- 🎉 no goals
        replace a_in : a ∈ I ^ i := by simpa [(I ^ i).mul_top] using a_in
        -- ⊢ a ∈ (fun x => x • m) ⁻¹' ↑(I ^ i • ⊤)
        exact smul_mem_smul a_in mem_top⟩ }
        -- 🎉 no goals
#align ideal.adic_module_basis Ideal.adic_module_basis

/-- The topology on an `R`-module `M` associated to an ideal `M`. Submodules $I^n M$,
written `I^n • ⊤` form a basis of neighborhoods of zero. -/
def adicModuleTopology : TopologicalSpace M :=
  @ModuleFilterBasis.topology R M _ I.adic_basis.topology _ _
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M))
#align ideal.adic_module_topology Ideal.adicModuleTopology

/-- The elements of the basis of neighborhoods of zero for the `I`-adic topology
on an `R`-module `M`, seen as open additive subgroups of `M`. -/
def openAddSubgroup (n : ℕ) : @OpenAddSubgroup R _ I.adicTopology := by
  letI := I.adicTopology
  -- ⊢ OpenAddSubgroup R
  refine ⟨(I ^ n).toAddSubgroup, ?_⟩
  -- ⊢ IsOpen (toAddSubgroup (I ^ n)).toAddSubmonoid.toAddSubsemigroup.carrier
  convert (I.adic_basis.toRing_subgroups_basis.openAddSubgroup n).isOpen
  -- ⊢ (toAddSubgroup (I ^ n)).toAddSubmonoid.toAddSubsemigroup.carrier = ↑(RingSub …
  change (I ^ n : Set R) = (I ^ n • (⊤ : Ideal R) : Set R)
  -- ⊢ ↑(I ^ n) = ↑(I ^ n • ⊤)
  simp [smul_top_eq_map, Algebra.id.map_eq_id, map_id, restrictScalars_self]
  -- 🎉 no goals
#align ideal.open_add_subgroup Ideal.openAddSubgroup

end Ideal

section IsAdic

/-- Given a topology on a ring `R` and an ideal `J`, `IsAdic J` means the topology is the
`J`-adic one. -/
def IsAdic [H : TopologicalSpace R] (J : Ideal R) : Prop :=
  H = J.adicTopology
#align is_adic IsAdic

/-- A topological ring is `J`-adic if and only if it admits the powers of `J` as a basis of
open neighborhoods of zero. -/
theorem isAdic_iff [top : TopologicalSpace R] [TopologicalRing R] {J : Ideal R} :
    IsAdic J ↔
      (∀ n : ℕ, IsOpen ((J ^ n : Ideal R) : Set R)) ∧
        ∀ s ∈ 𝓝 (0 : R), ∃ n : ℕ, ((J ^ n : Ideal R) : Set R) ⊆ s := by
  constructor
  -- ⊢ IsAdic J → (∀ (n : ℕ), IsOpen ↑(J ^ n)) ∧ ∀ (s : Set R), s ∈ 𝓝 0 → ∃ n, ↑(J  …
  · intro H
    -- ⊢ (∀ (n : ℕ), IsOpen ↑(J ^ n)) ∧ ∀ (s : Set R), s ∈ 𝓝 0 → ∃ n, ↑(J ^ n) ⊆ s
    change _ = _ at H
    -- ⊢ (∀ (n : ℕ), IsOpen ↑(J ^ n)) ∧ ∀ (s : Set R), s ∈ 𝓝 0 → ∃ n, ↑(J ^ n) ⊆ s
    rw [H]
    -- ⊢ (∀ (n : ℕ), IsOpen ↑(J ^ n)) ∧ ∀ (s : Set R), s ∈ 𝓝 0 → ∃ n, ↑(J ^ n) ⊆ s
    letI := J.adicTopology
    -- ⊢ (∀ (n : ℕ), IsOpen ↑(J ^ n)) ∧ ∀ (s : Set R), s ∈ 𝓝 0 → ∃ n, ↑(J ^ n) ⊆ s
    constructor
    -- ⊢ ∀ (n : ℕ), IsOpen ↑(J ^ n)
    · intro n
      -- ⊢ IsOpen ↑(J ^ n)
      exact (J.openAddSubgroup n).isOpen'
      -- 🎉 no goals
    · intro s hs
      -- ⊢ ∃ n, ↑(J ^ n) ⊆ s
      simpa using J.hasBasis_nhds_zero_adic.mem_iff.mp hs
      -- 🎉 no goals
  · rintro ⟨H₁, H₂⟩
    -- ⊢ IsAdic J
    apply TopologicalAddGroup.ext
    · apply @TopologicalRing.to_topologicalAddGroup
      -- 🎉 no goals
    · apply (RingSubgroupsBasis.toRingFilterBasis _).toAddGroupFilterBasis.isTopologicalAddGroup
      -- 🎉 no goals
    · ext s
      -- ⊢ s ∈ 𝓝 0 ↔ s ∈ 𝓝 0
      letI := Ideal.adic_basis J
      -- ⊢ s ∈ 𝓝 0 ↔ s ∈ 𝓝 0
      rw [J.hasBasis_nhds_zero_adic.mem_iff]
      -- ⊢ s ∈ 𝓝 0 ↔ ∃ i, True ∧ ↑(J ^ i) ⊆ s
      constructor <;> intro H
      -- ⊢ s ∈ 𝓝 0 → ∃ i, True ∧ ↑(J ^ i) ⊆ s
                      -- ⊢ ∃ i, True ∧ ↑(J ^ i) ⊆ s
                      -- ⊢ s ∈ 𝓝 0
      · rcases H₂ s H with ⟨n, h⟩
        -- ⊢ ∃ i, True ∧ ↑(J ^ i) ⊆ s
        exact ⟨n, trivial, h⟩
        -- 🎉 no goals
      · rcases H with ⟨n, -, hn⟩
        -- ⊢ s ∈ 𝓝 0
        rw [mem_nhds_iff]
        -- ⊢ ∃ t, t ⊆ s ∧ IsOpen t ∧ 0 ∈ t
        refine' ⟨_, hn, H₁ n, (J ^ n).zero_mem⟩
        -- 🎉 no goals
#align is_adic_iff isAdic_iff

variable [TopologicalSpace R] [TopologicalRing R]

theorem is_ideal_adic_pow {J : Ideal R} (h : IsAdic J) {n : ℕ} (hn : 0 < n) : IsAdic (J ^ n) := by
  rw [isAdic_iff] at h ⊢
  -- ⊢ (∀ (n_1 : ℕ), IsOpen ↑((J ^ n) ^ n_1)) ∧ ∀ (s : Set R), s ∈ 𝓝 0 → ∃ n_1, ↑(( …
  constructor
  -- ⊢ ∀ (n_1 : ℕ), IsOpen ↑((J ^ n) ^ n_1)
  · intro m
    -- ⊢ IsOpen ↑((J ^ n) ^ m)
    rw [← pow_mul]
    -- ⊢ IsOpen ↑(J ^ (n * m))
    apply h.left
    -- 🎉 no goals
  · intro V hV
    -- ⊢ ∃ n_1, ↑((J ^ n) ^ n_1) ⊆ V
    cases' h.right V hV with m hm
    -- ⊢ ∃ n_1, ↑((J ^ n) ^ n_1) ⊆ V
    use m
    -- ⊢ ↑((J ^ n) ^ m) ⊆ V
    refine' Set.Subset.trans _ hm
    -- ⊢ ↑((J ^ n) ^ m) ⊆ ↑(J ^ m)
    cases n
    -- ⊢ ↑((J ^ Nat.zero) ^ m) ⊆ ↑(J ^ m)
    · exfalso
      -- ⊢ False
      exact Nat.not_succ_le_zero 0 hn
      -- 🎉 no goals
    rw [← pow_mul, Nat.succ_mul]
    -- ⊢ ↑(J ^ (n✝ * m + m)) ⊆ ↑(J ^ m)
    apply Ideal.pow_le_pow
    -- ⊢ m ≤ n✝ * m + m
    apply Nat.le_add_left
    -- 🎉 no goals
#align is_ideal_adic_pow is_ideal_adic_pow

theorem is_bot_adic_iff {A : Type*} [CommRing A] [TopologicalSpace A] [TopologicalRing A] :
    IsAdic (⊥ : Ideal A) ↔ DiscreteTopology A := by
  rw [isAdic_iff]
  -- ⊢ ((∀ (n : ℕ), IsOpen ↑(⊥ ^ n)) ∧ ∀ (s : Set A), s ∈ 𝓝 0 → ∃ n, ↑(⊥ ^ n) ⊆ s)  …
  constructor
  -- ⊢ ((∀ (n : ℕ), IsOpen ↑(⊥ ^ n)) ∧ ∀ (s : Set A), s ∈ 𝓝 0 → ∃ n, ↑(⊥ ^ n) ⊆ s)  …
  · rintro ⟨h, _h'⟩
    -- ⊢ DiscreteTopology A
    rw [discreteTopology_iff_open_singleton_zero]
    -- ⊢ IsOpen {0}
    simpa using h 1
    -- 🎉 no goals
  · intros
    -- ⊢ (∀ (n : ℕ), IsOpen ↑(⊥ ^ n)) ∧ ∀ (s : Set A), s ∈ 𝓝 0 → ∃ n, ↑(⊥ ^ n) ⊆ s
    constructor
    -- ⊢ ∀ (n : ℕ), IsOpen ↑(⊥ ^ n)
    · simp
      -- 🎉 no goals
    · intro U U_nhds
      -- ⊢ ∃ n, ↑(⊥ ^ n) ⊆ U
      use 1
      -- ⊢ ↑(⊥ ^ 1) ⊆ U
      simp [mem_of_mem_nhds U_nhds]
      -- 🎉 no goals
#align is_bot_adic_iff is_bot_adic_iff

end IsAdic

/-- The ring `R` is equipped with a preferred ideal. -/
class WithIdeal (R : Type*) [CommRing R] where
  i : Ideal R
#align with_ideal WithIdeal

namespace WithIdeal

variable (R)

variable [WithIdeal R]

instance (priority := 100) : TopologicalSpace R :=
  i.adicTopology

instance (priority := 100) : NonarchimedeanRing R :=
  RingSubgroupsBasis.nonarchimedean _

instance (priority := 100) : UniformSpace R :=
  TopologicalAddGroup.toUniformSpace R

instance (priority := 100) : UniformAddGroup R :=
  comm_topologicalAddGroup_is_uniform

/-- The adic topology on an `R` module coming from the ideal `WithIdeal.I`.
This cannot be an instance because `R` cannot be inferred from `M`. -/
def topologicalSpaceModule (M : Type*) [AddCommGroup M] [Module R M] : TopologicalSpace M :=
  (i : Ideal R).adicModuleTopology M
#align with_ideal.topological_space_module WithIdeal.topologicalSpaceModule

/-
The next examples are kept to make sure potential future refactors won't break the instance
chaining.
-/
example : NonarchimedeanRing R := by infer_instance
                                     -- 🎉 no goals

example : TopologicalRing (UniformSpace.Completion R) := by infer_instance
                                                            -- 🎉 no goals

example (M : Type*) [AddCommGroup M] [Module R M] :
    @TopologicalAddGroup M (WithIdeal.topologicalSpaceModule R M) _ := by infer_instance
                                                                          -- 🎉 no goals

example (M : Type*) [AddCommGroup M] [Module R M] :
    @ContinuousSMul R M _ _ (WithIdeal.topologicalSpaceModule R M) := by infer_instance
                                                                         -- 🎉 no goals

example (M : Type*) [AddCommGroup M] [Module R M] :
    @NonarchimedeanAddGroup M _ (WithIdeal.topologicalSpaceModule R M) :=
  SubmodulesBasis.nonarchimedean _

end WithIdeal

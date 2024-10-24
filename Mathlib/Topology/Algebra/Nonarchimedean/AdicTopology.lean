/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.UniformRing

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

abbrev adicBasis (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    Submodule R M := I ^ n • ⊤

theorem adicBasis_isAddGroupBasisOfSubgroups (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] :
    IsAddGroupBasisOfSubgroups (fun _ ↦ True) (fun n ↦ (I.adicBasis M n).toAddSubgroup) :=
  .mk_of_comm _ _ ⟨0, trivial⟩ fun {i j} _ _ ↦
    ⟨max i j, trivial, le_inf_iff.mpr
      ⟨smul_mono_left <| pow_le_pow_right (le_max_left i j),
        smul_mono_left <| pow_le_pow_right (le_max_right i j)⟩⟩

theorem adicBasis_isAddGroupBasis (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    IsAddGroupBasis (fun _ ↦ True) (fun n ↦ I.adicBasis M n : ℕ → Set M) :=
  I.adicBasis_isAddGroupBasisOfSubgroups M |>.isAddGroupBasis

/-- The topology on an `R`-module `M` associated to an ideal `M`. Submodules $I^n M$,
written `I^n • ⊤` form a basis of neighborhoods of zero. -/
def adicTopology (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] : TopologicalSpace M :=
  I.adicBasis_isAddGroupBasis M |>.topology

theorem topologicalAddGroup (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    @TopologicalAddGroup M (I.adicTopology M) _ :=
  let _ := I.adicTopology M
  I.adicBasis_isAddGroupBasis M |>.instTopologicalAddGroup

theorem nonarchimedeanAddGroup (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    @NonarchimedeanAddGroup M _ (I.adicTopology M) :=
  I.adicBasis_isAddGroupBasisOfSubgroups M |>.nonarchimedean

/-- For the `I`-adic topology, the neighborhoods of zero has basis given by the powers of `I`. -/
theorem hasBasis_nhds_zero_adicBasis (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    HasBasis (@nhds _ (I.adicTopology M) 0) (fun _ ↦ True) (fun n ↦ I.adicBasis M n) :=
  I.adicBasis_isAddGroupBasis M |>.nhds_zero_hasBasis

theorem hasBasis_nhds_adicBasis (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (m : M) :
    HasBasis (@nhds _ (I.adicTopology M) m)
      (fun _ ↦ True) (fun n ↦ m +ᵥ (I.adicBasis M n : Set M)) :=
  I.adicBasis_isAddGroupBasis M |>.nhds_hasBasis m

theorem isRingBasisOfSubmodules_adic (I : Ideal R) :
    IsRingBasisOfSubmodules (fun _ ↦ True) (I.adicBasis R) where
  nonempty := ⟨0, trivial⟩
  inter := I.adicBasis_isAddGroupBasisOfSubgroups R |>.inter
  mul_left := by
    suffices ∀ (a : R) {i : ℕ}, ∃ j : ℕ, a • I ^ j ≤ I ^ i by
      simpa only [smul_eq_mul, mul_top, mapsTo', image_subset_iff, true_and,
        true_implies, ← SetLike.coe_subset_coe, coe_pointwise_smul, ← image_smul] using this
    intro r n
    use n
    rintro a ⟨x, hx, rfl⟩
    exact (I ^ n).smul_mem r hx
  mul := by
    suffices ∀ i : ℕ, ∃ j : ℕ, (↑(I ^ j) * ↑(I ^ j) : Set R) ⊆ (↑(I ^ i) : Set R) by
      simpa only [smul_eq_mul, mul_top, true_and, true_implies] using this
    intro n
    use n
    rintro a ⟨x, _hx, b, hb, rfl⟩
    exact (I ^ n).smul_mem x hb

/-- The adic ring filter basis associated to an ideal `I` is made of powers of `I`. -/
theorem isRingBasis_adic (I : Ideal R) :
    IsRingBasis (fun _ ↦ True) (fun n : ℕ ↦ ((I ^ n • ⊤ : Ideal R) : Set R)):=
  I.isRingBasisOfSubmodules_adic.isRingBasisOfSubgroups.isRingBasis

/-- The adic topology associated to an ideal `I`. This topology admits powers of `I` as a basis of
neighborhoods of zero. It is compatible with the ring structure and is non-archimedean. -/
def adicTopology (I : Ideal R) : TopologicalSpace R :=
  I.isRingBasisOfSubmodules_adic.topology

theorem nonarchimedean (I : Ideal R) : @NonarchimedeanRing R _ I.adicTopology :=
  I.isRingBasisOfSubmodules_adic.isRingBasisOfSubgroups.nonarchimedean

/-- For the `I`-adic topology, the neighborhoods of zero has basis given by the powers of `I`. -/
theorem hasBasis_nhds_zero_adic (I : Ideal R) :
    HasBasis (@nhds R I.adicTopology (0 : R)) (fun _ ↦ True)
      (fun n : ℕ ↦ ((I ^ n : Ideal R) : Set R)) := by
  suffices HasBasis (@nhds R I.adicTopology (0 : R)) (fun _ ↦ True)
      (fun n : ℕ ↦ ((I ^ n • ⊤ : Ideal R) : Set R)) by
    simpa [coe_toAddSubgroup] using this
  exact I.isRingBasisOfSubmodules_adic.isRingBasisOfSubgroups.hasBasis_nhds_zero

theorem hasBasis_nhds_adic (I : Ideal R) (x : R) :
    HasBasis (@nhds R I.adicTopology x) (fun _n : ℕ => True) fun n =>
      (fun y => x + y) '' (I ^ n : Ideal R) := by
  suffices HasBasis (@nhds R I.adicTopology x) (fun _ ↦ True)
      (fun n : ℕ ↦ x +ᵥ ((I ^ n • ⊤ : Ideal R) : Set R)) by
    simpa [coe_toAddSubgroup, ← image_add_left] using this
  exact I.isRingBasisOfSubmodules_adic.isRingBasisOfSubgroups.isRingBasis.nhds_hasBasis x

variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

theorem isModuleBasisOfSubmodules_adic :
    IsModuleBasisOfSubmodules (tR := I.adicTopology) (fun _ ↦ True)
      (fun n : ℕ => (I ^ n • ⊤ : Submodule R M)) := by
  letI := I.adicTopology
  refine .mk_of_hasBasis I.hasBasis_nhds_zero_adic _ _ ⟨0, trivial⟩ ?_ ?_

theorem adic_module_basis :
    I.ringFilterBasis.SubmodulesBasis fun n : ℕ => I ^ n • (⊤ : Submodule R M) :=
  { inter := fun i j =>
      ⟨max i j,
        le_inf_iff.mpr
          ⟨smul_mono_left <| pow_le_pow_right (le_max_left i j),
            smul_mono_left <| pow_le_pow_right (le_max_right i j)⟩⟩
    smul := fun m i =>
      ⟨(I ^ i • ⊤ : Ideal R), ⟨i, by simp⟩, fun a a_in => by
        replace a_in : a ∈ I ^ i := by simpa [(I ^ i).mul_top] using a_in
        exact smul_mem_smul a_in mem_top⟩ }

/-- The topology on an `R`-module `M` associated to an ideal `M`. Submodules $I^n M$,
written `I^n • ⊤` form a basis of neighborhoods of zero. -/
def adicModuleTopology : TopologicalSpace M :=
  @ModuleFilterBasis.topology R M _ I.adic_basis.topology _ _
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M))

/-- The elements of the basis of neighborhoods of zero for the `I`-adic topology
on an `R`-module `M`, seen as open additive subgroups of `M`. -/
def openAddSubgroup (n : ℕ) : @OpenAddSubgroup R _ I.adicTopology := by
  letI := I.adicTopology
  refine ⟨(I ^ n).toAddSubgroup, ?_⟩
  convert (I.adic_basis.toRing_subgroups_basis.openAddSubgroup n).isOpen
  change (↑(I ^ n) : Set R) = ↑(I ^ n • (⊤ : Ideal R))
  simp [smul_top_eq_map, Algebra.id.map_eq_id, map_id, restrictScalars_self]

end Ideal

section IsAdic

/-- Given a topology on a ring `R` and an ideal `J`, `IsAdic J` means the topology is the
`J`-adic one. -/
def IsAdic [H : TopologicalSpace R] (J : Ideal R) : Prop :=
  H = J.adicTopology

/-- A topological ring is `J`-adic if and only if it admits the powers of `J` as a basis of
open neighborhoods of zero. -/
theorem isAdic_iff [top : TopologicalSpace R] [TopologicalRing R] {J : Ideal R} :
    IsAdic J ↔
      (∀ n : ℕ, IsOpen ((J ^ n : Ideal R) : Set R)) ∧
        ∀ s ∈ 𝓝 (0 : R), ∃ n : ℕ, ((J ^ n : Ideal R) : Set R) ⊆ s := by
  constructor
  · intro H
    change _ = _ at H
    rw [H]
    letI := J.adicTopology
    constructor
    · intro n
      exact (J.openAddSubgroup n).isOpen'
    · intro s hs
      simpa using J.hasBasis_nhds_zero_adic.mem_iff.mp hs
  · rintro ⟨H₁, H₂⟩
    apply TopologicalAddGroup.ext
    · apply @TopologicalRing.to_topologicalAddGroup
    · apply (RingSubgroupsBasis.toRingFilterBasis _).toAddGroupFilterBasis.isTopologicalAddGroup
    · ext s
      letI := Ideal.adic_basis J
      rw [J.hasBasis_nhds_zero_adic.mem_iff]
      constructor <;> intro H
      · rcases H₂ s H with ⟨n, h⟩
        exact ⟨n, trivial, h⟩
      · rcases H with ⟨n, -, hn⟩
        rw [mem_nhds_iff]
        exact ⟨_, hn, H₁ n, (J ^ n).zero_mem⟩

variable [TopologicalSpace R] [TopologicalRing R]

theorem is_ideal_adic_pow {J : Ideal R} (h : IsAdic J) {n : ℕ} (hn : 0 < n) : IsAdic (J ^ n) := by
  rw [isAdic_iff] at h ⊢
  constructor
  · intro m
    rw [← pow_mul]
    apply h.left
  · intro V hV
    cases' h.right V hV with m hm
    use m
    refine Set.Subset.trans ?_ hm
    cases n
    · exfalso
      exact Nat.not_succ_le_zero 0 hn
    rw [← pow_mul, Nat.succ_mul]
    apply Ideal.pow_le_pow_right
    apply Nat.le_add_left

theorem is_bot_adic_iff {A : Type*} [CommRing A] [TopologicalSpace A] [TopologicalRing A] :
    IsAdic (⊥ : Ideal A) ↔ DiscreteTopology A := by
  rw [isAdic_iff]
  constructor
  · rintro ⟨h, _h'⟩
    rw [discreteTopology_iff_isOpen_singleton_zero]
    simpa using h 1
  · intros
    constructor
    · simp
    · intro U U_nhds
      use 1
      simp [mem_of_mem_nhds U_nhds]

end IsAdic

/-- The ring `R` is equipped with a preferred ideal. -/
class WithIdeal (R : Type*) [CommRing R] where
  i : Ideal R

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

/-
The next examples are kept to make sure potential future refactors won't break the instance
chaining.
-/
example : NonarchimedeanRing R := by infer_instance

example : TopologicalRing (UniformSpace.Completion R) := by infer_instance

example (M : Type*) [AddCommGroup M] [Module R M] :
    @TopologicalAddGroup M (WithIdeal.topologicalSpaceModule R M) _ := by infer_instance

example (M : Type*) [AddCommGroup M] [Module R M] :
    @ContinuousSMul R M _ _ (WithIdeal.topologicalSpaceModule R M) := by infer_instance

example (M : Type*) [AddCommGroup M] [Module R M] :
    @NonarchimedeanAddGroup M _ (WithIdeal.topologicalSpaceModule R M) :=
  SubmodulesBasis.nonarchimedean _

end WithIdeal

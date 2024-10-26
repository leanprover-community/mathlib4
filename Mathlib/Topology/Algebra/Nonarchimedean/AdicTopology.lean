/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.RingTheory.Ideal.Operations
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

* `Ideal.adicBasis`: the basis of submodules given by powers of an ideal.
* `Ideal.adicBasis_isBasis`: `Ideal.adicBasis` is indeed a filter basis.
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

-- Common facts about the two cases (ring or module)
section Common

namespace Ideal

variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

abbrev adicBasis (n : ℕ) : Set M := (I ^ n • ⊤ : Submodule R M)

@[simp]
theorem adicBasis_def :
  I.adicBasis M = (fun n ↦ (I ^ n • ⊤ : Submodule R M) : ℕ → Set M) :=
rfl

theorem adicBasis_isBasis :
    IsBasis (fun _ ↦ True) (I.adicBasis M) where
  nonempty := ⟨0, trivial⟩
  inter := fun {i j} _ _ ↦
    ⟨max i j, trivial, le_inf_iff.mpr
      ⟨smul_mono_left <| pow_le_pow_right (le_max_left i j),
        smul_mono_left <| pow_le_pow_right (le_max_right i j)⟩⟩

theorem adicBasis_isAddGroupBasis :
    IsAddGroupBasis (fun _ ↦ True) (I.adicBasis M) :=
  .mk_of_subgroups_of_comm <| I.adicBasis_isBasis M

/-- The topology on an `R`-module `M` associated to an ideal `M`. Submodules $I^n M$,
written `I^n • ⊤` form a basis of neighborhoods of zero. -/
def adicTopology : TopologicalSpace M :=
  I.adicBasis_isAddGroupBasis M |>.topology

end Ideal

/-- Given a topology on a module `M` and an ideal `J` of the base ring,
`IsAdic J` means the topology is the `J`-adic one. -/
def IsAdic (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    [tM : TopologicalSpace M] : Prop :=
  tM = I.adicTopology M

section IsAdic

theorem Ideal.isAdic_adicTopology (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    IsAdic I M (tM := I.adicTopology M) :=
  rfl

instance (priority := 100) Ideal.instTopologicalAddGroup_adic
    (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    @TopologicalAddGroup M (I.adicTopology M) _ :=
  (I.adicBasis_isAddGroupBasis M).topologicalAddGroup

theorem IsAdic.topologicalAddGroup {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
    {_ : TopologicalSpace M} (h : IsAdic I M) :
    TopologicalAddGroup M :=
  h ▸ I.instTopologicalAddGroup_adic M

/-- For the `I`-adic topology, the neighborhoods of zero has basis given by the powers of `I`. -/
theorem IsAdic.hasBasis_nhds_zero {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
    {_ : TopologicalSpace M} (h : IsAdic I M) :
    (𝓝 0).HasBasis (fun _ ↦ True) (I.adicBasis M) :=
  h ▸ (I.adicBasis_isAddGroupBasis M).nhds_zero_hasBasis

theorem IsAdic.hasBasis_nhds {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
    {_ : TopologicalSpace M} (h : IsAdic I M) (m : M) :
    (𝓝 m).HasBasis (fun _ ↦ True) (fun n ↦ m +ᵥ I.adicBasis M n) :=
  h ▸ (I.adicBasis_isAddGroupBasis M).nhds_hasBasis m

theorem isAdic_iff_hasBasis_nhds_zero {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
    {_ : TopologicalSpace M} [TopologicalAddGroup M] : IsAdic I M ↔
    (𝓝 0).HasBasis (fun _ ↦ True) (I.adicBasis M) :=
  ⟨IsAdic.hasBasis_nhds_zero, fun H ↦ TopologicalAddGroup.ext inferInstance
    (I.isAdic_adicTopology M).topologicalAddGroup
    (H.eq_of_same_basis <| I.isAdic_adicTopology M |>.hasBasis_nhds_zero)⟩

/-- A topological ring is `J`-adic if and only if it admits the powers of `J` as a basis of
open neighborhoods of zero. -/
theorem isAdic_iff {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
    {_ : TopologicalSpace M} [TopologicalAddGroup M] :
    IsAdic I M ↔
      (∀ n : ℕ, IsOpen ((I ^ n • ⊤ : Submodule R M) : Set M)) ∧
        ∀ s ∈ 𝓝 (0 : M), ∃ n : ℕ, ((I ^ n • ⊤ : Submodule R M) : Set M) ⊆ s := by
  rw [isAdic_iff_hasBasis_nhds_zero]
  refine ⟨fun H ↦ ⟨fun n ↦ (I ^ n • ⊤ : Submodule R M).toAddSubgroup.isOpen_of_mem_nhds
    (H.mem_of_mem trivial), fun _ hS ↦ H.mem_iff.mp hS |>.imp fun n h ↦ h.2⟩,
    fun H ↦ ⟨fun s ↦ ⟨fun hs ↦ H.2 s hs |>.imp fun n h ↦ ⟨trivial, h⟩, fun h ↦ h.elim
      fun n h ↦ mem_of_superset ((H.1 n).mem_nhds (zero_mem _)) h.2⟩⟩⟩

theorem IsAdic.pow {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
    {_ : TopologicalSpace M} (h : IsAdic I M) {n : ℕ} (hn : 0 < n) : IsAdic (I ^ n) M := by
  haveI := h.topologicalAddGroup
  simp_rw [isAdic_iff_hasBasis_nhds_zero, Ideal.adicBasis_def, ← pow_mul] at h ⊢
  exact h.to_hasBasis
    (fun k _ ↦ ⟨k, trivial, smul_mono_left <| Ideal.pow_le_pow_right <| n.le_mul_of_pos_left k hn⟩)
    (fun k _ ↦ ⟨n * k, trivial, subset_rfl⟩)

theorem isAdic_bot_iff {M : Type*} [AddCommGroup M] [Module R M] {_ : TopologicalSpace M} :
    IsAdic (⊥ : Ideal R) M ↔ DiscreteTopology M := by
  constructor <;> intro H
  · haveI := H.topologicalAddGroup
    exact discreteTopology_iff_isOpen_singleton_zero.mpr <|
      isOpen_iff_mem_nhds.mpr fun _ h ↦ h.symm ▸ by
      simpa [Ideal.adicBasis] using H.hasBasis_nhds_zero.mem_of_mem (i := 1) trivial
  -- TODO: this should be an instance
  · haveI : TopologicalAddGroup M := ⟨⟩
    exact isAdic_iff_hasBasis_nhds_zero.mpr (nhds_discrete M ▸ (hasBasis_pure _).to_hasBasis
      (fun _ _ ↦ ⟨1, trivial, by simp⟩) (by simp))

instance (priority := 100) Ideal.instNonarchimedeanAddGroup_adic
    (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    @NonarchimedeanAddGroup M _ (I.adicTopology M) :=
  (I.adicBasis_isAddGroupBasis M).nonarchimedean_of_subgroups

theorem IsAdic.nonarchimedeanAddGroup {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
    {_ : TopologicalSpace M} (h : IsAdic I M) :
    NonarchimedeanAddGroup M :=
  h ▸ I.instNonarchimedeanAddGroup_adic M

/-- The elements of the basis of neighborhoods of zero for the `I`-adic topology
on an `R`-module `M`, seen as open additive subgroups of `M`. -/
def IsAdic.openAddSubgroup {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
    {_ : TopologicalSpace M} (h : IsAdic I M) (n : ℕ) : OpenAddSubgroup M :=
  haveI := h.topologicalAddGroup
  ⟨(I ^ n • ⊤ : Submodule R M).toAddSubgroup,
    AddSubgroup.isOpen_of_mem_nhds _ (h.hasBasis_nhds_zero.mem_of_mem trivial)⟩

end IsAdic

end Common

section Ring

variable (I : Ideal R)

theorem Ideal.adicBasis_eq (n : ℕ) : I.adicBasis R n = (I ^ n : Submodule R R) := by
  simp only [Ideal.adicBasis, smul_eq_mul, mul_top]

theorem Ideal.adicBasis_isRingBasis :
    IsRingBasis (fun _ ↦ True) (I.adicBasis R) :=
  .mk_of_ideals_of_comm (I.adicBasis_isBasis R)
    (fun {n} _ ↦ ⟨n, trivial, mul_subset_iff.mpr fun x _ _ hb ↦ Submodule.smul_mem _ x hb⟩)

instance (priority := 100) Ideal.instTopologicalRing_adic :
    @TopologicalRing R (I.adicTopology R) _ :=
  I.adicBasis_isRingBasis.topologicalRing

theorem IsAdic.topologicalRing {I : Ideal R} {_ : TopologicalSpace R} (h : IsAdic I R) :
    TopologicalRing R :=
  h ▸ I.instTopologicalRing_adic

instance (priority := 100) Ideal.instNonarchimedeanRing_adic :
    @NonarchimedeanRing R _ (I.adicTopology R) :=
  I.adicBasis_isRingBasis.nonarchimedean_of_subgroups

theorem IsAdic.nonarchimedeanRing {I : Ideal R} {_ : TopologicalSpace R} (h : IsAdic I R) :
    NonarchimedeanRing R :=
  h ▸ I.instNonarchimedeanRing_adic

end Ring

section Module

theorem Ideal.adicBasis_isModuleBasis [TopologicalSpace R] (I : Ideal R) (M : Type*)
    (hR : IsAdic I R) [AddCommGroup M] [Module R M] :
    IsModuleBasis R (fun _ ↦ True) (I.adicBasis M) :=
  .mk_of_submodules_of_hasBasis hR.hasBasis_nhds_zero (I.adicBasis_isBasis M)
    (fun m i _ ↦ ⟨i, trivial, fun r hr ↦ Submodule.smul_mem_smul (by simpa using hr) trivial⟩)

instance (priority := 100) Ideal.instContinuousSMul_adic (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] :
    @ContinuousSMul R M _ (I.adicTopology R) (I.adicTopology M) :=
  letI := I.adicTopology R
  (I.adicBasis_isModuleBasis M (I.isAdic_adicTopology R)).continuousSMul

variable {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace R] [TopologicalSpace M] (hR : IsAdic I R) (hM : IsAdic I M)

include hR hM in
theorem IsAdic.continuousSMul : ContinuousSMul R M :=
  hR ▸ hM ▸ I.instContinuousSMul_adic M

end Module

/-- The ring `R` is equipped with a preferred ideal. -/
class WithIdeal (R : Type*) [CommRing R] where
  i : Ideal R

namespace WithIdeal

variable (R)
variable [WithIdeal R]

instance (priority := 100) : TopologicalSpace R :=
  (i : Ideal R).adicTopology R

theorem isAdic : IsAdic (i : Ideal R) R := rfl

instance (priority := 100) : UniformSpace R :=
  TopologicalAddGroup.toUniformSpace R

instance (priority := 100) : UniformAddGroup R :=
  comm_topologicalAddGroup_is_uniform

/-- The adic topology on an `R` module coming from the ideal `WithIdeal.I`.
This cannot be an instance because `R` cannot be inferred from `M`. -/
def topologicalSpaceModule (M : Type*) [AddCommGroup M] [Module R M] : TopologicalSpace M :=
  (i : Ideal R).adicTopology M

/-
The next examples are kept to make sure potential future refactors won't break the instance
chaining.
-/
example : NonarchimedeanRing R := inferInstance

example : TopologicalRing (UniformSpace.Completion R) := inferInstance

example (M : Type*) [AddCommGroup M] [Module R M] :
    @TopologicalAddGroup M (WithIdeal.topologicalSpaceModule R M) _ := inferInstance

example (M : Type*) [AddCommGroup M] [Module R M] :
    @ContinuousSMul R M _ _ (WithIdeal.topologicalSpaceModule R M) := inferInstance

example (M : Type*) [AddCommGroup M] [Module R M] :
    @NonarchimedeanAddGroup M _ (WithIdeal.topologicalSpaceModule R M) :=
  inferInstance

end WithIdeal

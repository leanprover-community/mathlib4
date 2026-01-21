/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.RingTheory.IdealFilter.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.FilterBasis

/-!
# Topologies associated to ideal filters

This file constructs topological structures on a ring from an `IdealFilter`.

## Main definitions

* `IdealFilter.addGroupFilterBasis`: the `AddGroupFilterBasis` with sets the ideals of `F`.
* `IdealFilter.addGroupTopology`: the corresponding topology on `A`.
* `IdealFilter.ringFilterBasis`: under `F.IsUniform`, the `RingFilterBasis` with sets the ideals of
`F`.
* `IdealFilter.ringTopology`: under `F.IsUniform`, the corresponding ring topology on `A`.

## Main statements

* `isUniform_iff_exists_ringFilterBasis`: An `IdealFilter` on a ring `A` is uniform if and only if
its ideals form a `RingFilterBasis` for `A`.
* `IdealFilter.addGroupTopology_mem_nhds_iff`: a neighbourhood characterization for
`addGroupTopology`.
* `IdealFilter.ringTopology_mem_nhds_iff`: a neighbourhood characterization for
`ringTopology`.
* `IdealFilter.isLinearTopology_ringTopology`: the topology `ringTopology` is linear.

## References

* [nLab: Uniform filter](<https://ncatlab.org/nlab/show/uniform+filter>)
* [nLab: Gabriel filter](<https://ncatlab.org/nlab/show/Gabriel+filter>)
* [nLab: Gabriel composition](<https://ncatlab.org/nlab/show/Gabriel+composition+of+filters>)

## Tags

ring theory, ideal, filter, linear topology
-/

@[expose] public section

open scoped Pointwise Topology

namespace IdealFilter

variable {A : Type*} [Ring A]

variable (F : IdealFilter A)

/-- The additive-group filter basis whose sets are the ideals belonging to the ideal filter `F`. -/
def addGroupFilterBasis : AddGroupFilterBasis A where
  sets := {(I : Set A) | I ∈ F}
  nonempty := by
    obtain ⟨I, hI⟩ := F.nonempty
    exact ⟨I, ⟨I, hI, rfl⟩⟩
  inter_sets := by
    rintro s t ⟨I, hI, rfl⟩ ⟨J, hJ, rfl⟩
    exact ⟨I ⊓ J, ⟨I ⊓ J, Order.PFilter.inf_mem hI hJ, rfl⟩, fun _ h ↦ h⟩
  zero' := by
    rintro s ⟨I, hI, rfl⟩
    exact zero_mem I
  add' := by
    rintro s ⟨I, hI, rfl⟩
    exact ⟨I, ⟨I, hI, rfl⟩, Set.add_subset_iff.mpr (fun _ hx _ hy ↦ add_mem hx hy)⟩
  neg' := by
    rintro s ⟨I, hI, rfl⟩
    exact ⟨I, ⟨I, hI, rfl⟩, by simp⟩
  conj' := by
    rintro x₀ s ⟨I, hI, rfl⟩
    exact ⟨I, ⟨I, hI, rfl⟩, by simp⟩

/-- Under `F.IsUniform`, the ring filter basis obtained from `addGroupFilterBasis`. -/
def ringFilterBasis (hUniform : F.IsUniform) : RingFilterBasis A where
  sets := F.addGroupFilterBasis.sets
  nonempty := F.addGroupFilterBasis.nonempty
  inter_sets := F.addGroupFilterBasis.inter_sets
  zero' := F.addGroupFilterBasis.zero'
  add' := F.addGroupFilterBasis.add'
  neg' := F.addGroupFilterBasis.neg'
  conj' := F.addGroupFilterBasis.conj'
  mul' := by
    rintro U ⟨I, hI, rfl⟩
    exact ⟨I, ⟨I, hI, rfl⟩, Set.mul_subset_iff.mpr fun _ h₁ _ h₂ ↦ mul_mem h₁ h₂⟩
  mul_left' := by
    rintro x₀ U ⟨I, hI, rfl⟩
    exact ⟨I, ⟨I, hI, rfl⟩, fun a ha ↦ Ideal.mul_mem_left I x₀ ha⟩
  mul_right' := by
    rintro x₀ U ⟨I, hI, rfl⟩
    exact ⟨I.colon {x₀}, ⟨I.colon {x₀}, IsUniform.colon_mem hUniform hI x₀, rfl⟩,
      fun a ha ↦ Set.mem_preimage.mpr (Submodule.mem_colon_singleton.mp ha)⟩

/-- An `IdealFilter` on a ring `A` is uniform if and only if its ideals form a `RingFilterBasis`
for `A`. -/
theorem isUniform_iff_exists_ringFilterBasis :
    F.IsUniform ↔ ∃ B : RingFilterBasis A, B.sets = {s : Set A | ∃ I ∈ F, s = (I : Set A)} := by
  constructor
  · intro hF
    refine ⟨F.ringFilterBasis hF, ?_⟩
    ext s
    constructor <;>
    · intro hs
      rcases hs with ⟨I, hI, rfl⟩
      exact ⟨I, hI, rfl⟩
  · rintro ⟨B, hB⟩
    exact {
      colon_mem := by
        intro I hI a
        have hIB : (I : Set A) ∈ B.sets := by simpa [hB]
        rcases RingFilterBasis.mul_right B a hIB with ⟨V, hbasis : V ∈ B.sets, hsub⟩
        rcases (by simpa [hB] using hbasis) with ⟨J, hJ, rfl⟩
        exact Order.PFilter.mem_of_le (fun x hx ↦ Submodule.mem_colon_singleton.mpr (hsub hx)) hJ
    }

/-- The topology on `A` induced by `addGroupFilterBasis`. -/
def addGroupTopology : TopologicalSpace A := (addGroupFilterBasis F).topology

/-- The topology `F.addGroupTopology` endows `A` with the structure of a topological additive
group. -/
theorem isTopologicalAddGroup :
    letI : TopologicalSpace A := F.addGroupTopology
    IsTopologicalAddGroup A :=
  F.addGroupFilterBasis.isTopologicalAddGroup

/-- Under `F.IsUniform`, the topology on `A` induced by `ringFilterBasis`. -/
def ringTopology (hUniform : F.IsUniform) : TopologicalSpace A :=
  (ringFilterBasis F hUniform).topology

/-- Under `F.IsUniform`, the topology `F.ringTopology` endows `A` with the structure of a
topological ring. -/
theorem isTopologicalRing (hUniform : F.IsUniform) :
    letI : TopologicalSpace A := F.ringTopology hUniform
    IsTopologicalRing A :=
  (F.ringFilterBasis hUniform).isTopologicalRing

/-- In `F.addGroupTopology`, a set is a neighbourhood of `a` iff it contains a
left-additive coset of some ideal `I ∈ F`. -/
lemma addGroupTopology_mem_nhds_iff (a : A) (s : Set A) :
    letI : TopologicalSpace A := F.addGroupTopology
    s ∈ 𝓝 a ↔ ∃ I ∈ F, a +ᵥ (I : Set A) ⊆ s := by
  constructor
  · intro hs
    rcases ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.1 hs with ⟨t, ht, hts⟩
    rcases ht with ⟨I, hI, rfl⟩
    exact ⟨I, hI, hts⟩
  · rintro ⟨I, hI, hIs⟩
    refine ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.2 ?_
    exact ⟨I, ⟨I, hI, rfl⟩, hIs⟩

/-- In `F.addGroupTopology`, `s` is a neighbourhood of `0` iff it contains an ideal
belonging to `F`. -/
lemma addGroupTopology_mem_nhds_zero_iff (s : Set A) :
    letI : TopologicalSpace A := F.addGroupTopology
    s ∈ 𝓝 0 ↔ ∃ I ∈ F, (I : Set A) ⊆ s := by
  simpa [zero_vadd] using F.addGroupTopology_mem_nhds_iff (a := (0 : A)) (s := s)

/-- In `F.ringTopology`, `s` is a neighbourhood of `a` iff it contains a
left-additive coset of some ideal `I ∈ F`. -/
lemma ringTopology_mem_nhds_iff (hUniform : F.IsUniform) (a : A) (s : Set A) :
    letI : TopologicalSpace A := F.ringTopology hUniform
    s ∈ 𝓝 a ↔ ∃ I ∈ F, a +ᵥ (I : Set A) ⊆ s := by
  constructor
  · intro hs
    rcases ((F.ringFilterBasis hUniform).nhds_hasBasis a).mem_iff.mp hs with ⟨t, ht, hts⟩
    rcases ht with ⟨I, hI, rfl⟩
    exact ⟨I, hI, hts⟩
  · rintro ⟨I, hI, hIs⟩
    exact ((F.ringFilterBasis hUniform).nhds_hasBasis a).mem_iff.mpr ⟨I, ⟨I, hI, rfl⟩, hIs⟩

/-- In `F.ringTopology`, `s` is a neighbourhood of `0` iff it contains an ideal belonging
to `F`. -/
lemma ringTopology_mem_nhds_zero_iff (hUniform : F.IsUniform) (s : Set A) :
    letI : TopologicalSpace A := F.ringTopology hUniform
    s ∈ 𝓝 0 ↔ ∃ I ∈ F, (I : Set A) ⊆ s := by
  simpa [zero_vadd] using F.ringTopology_mem_nhds_iff (hUniform := hUniform) (a := (0 : A)) (s := s)

/-- Under `F.IsUniform`, the topology `ringTopology` is linear in the sense that `𝓝 0` has a
basis of ideals. -/
theorem isLinearTopology_ringTopology (hUniform : F.IsUniform) :
    letI : TopologicalSpace A := F.ringTopology hUniform
    IsLinearTopology A A := by
  letI : TopologicalSpace A := F.ringTopology hUniform
  exact IsLinearTopology.mk_of_hasBasis' (R := A) (M := A)
    (ι := Ideal A) (S := Ideal A)
    (p := fun I : Ideal A ↦ I ∈ F) (s := fun I : Ideal A ↦ I)
    ⟨fun t ↦ ringTopology_mem_nhds_zero_iff F hUniform t⟩
    (fun I a m hm ↦ Submodule.smul_mem I a hm)

end IdealFilter

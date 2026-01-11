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

* [nLab: Uniform filter](https://ncatlab.org/nlab/show/uniform+filter)
* [nLab: Gabriel filter](https://ncatlab.org/nlab/show/Gabriel+filter)
* [nLab: Gabriel composition](https://ncatlab.org/nlab/show/Gabriel+composition+of+filters)

## Tags

ring theory, ideal, filter, linear topology
-/

@[expose] public section

open scoped Pointwise Topology

universe u

namespace IdealFilter

variable {A : Type u} [Ring A]

variable (F : IdealFilter A)

/-- The additive-group filter basis whose sets are the ideals belonging to the ideal filter `F`. -/
def addGroupFilterBasis : AddGroupFilterBasis A where
  sets := {(I : Set A) | I ∈ F}
  nonempty := by
    obtain ⟨I, h_I⟩ := F.nonempty
    exact ⟨I, ⟨I, h_I, rfl⟩⟩
  inter_sets := by
    rintro s t ⟨I, h_I, rfl⟩ ⟨J, h_J, rfl⟩
    exact ⟨I ⊓ J, ⟨I ⊓ J, Order.PFilter.inf_mem h_I h_J, rfl⟩, fun x h ↦ h⟩
  zero' := by
    rintro s ⟨I, h_I, rfl⟩
    exact zero_mem I
  add' := by
    rintro s ⟨I, h_I, rfl⟩
    refine ⟨I, ⟨I, h_I, rfl⟩, Set.add_subset_iff.mpr ?_⟩
    exact fun x a y a_1 ↦ add_mem a a_1
  neg' := by
    rintro s ⟨I, h_I, rfl⟩
    exact ⟨I, ⟨I, h_I, rfl⟩, by simp⟩
  conj' := by
    rintro x₀ s ⟨I, h_I, rfl⟩
    exact ⟨I, ⟨I, h_I, rfl⟩, by simp⟩

/-- Under `F.IsUniform`, the ring filter basis obtained from `addGroupFilterBasis`.
The right-multiplication axiom uses the comap-closure from uniformity. -/
def ringFilterBasis (uni_F : F.IsUniform) : RingFilterBasis A where
  sets := F.addGroupFilterBasis.sets
  nonempty := F.addGroupFilterBasis.nonempty
  inter_sets := F.addGroupFilterBasis.inter_sets
  zero' := F.addGroupFilterBasis.zero'
  add' := F.addGroupFilterBasis.add'
  neg' := F.addGroupFilterBasis.neg'
  conj' := F.addGroupFilterBasis.conj'
  mul' := by
    rintro U ⟨I, h_I, rfl⟩
    exact ⟨I, ⟨I, h_I, rfl⟩, Set.mul_subset_iff.mpr fun _ h₁ _ h₂ ↦ mul_mem h₁ h₂⟩
  mul_left' := by
    rintro x₀ U ⟨I, h_I, rfl⟩
    refine ⟨I, ⟨I, h_I, rfl⟩, ?_⟩
    intro a h_a
    exact Ideal.mul_mem_left I x₀ h_a
  mul_right' := by
    rintro x₀ U ⟨I, h_I, rfl⟩
    refine ⟨I.colon {x₀}, ?_, ?_⟩
    · exact ⟨I.colon {x₀}, IsUniform.colon_mem uni_F h_I x₀, rfl⟩
    · intro a ha
      exact Set.mem_preimage.mpr (Submodule.mem_colon_singleton_set.mp ha)

/-- An `IdealFilter` on a ring `A` is uniform if and only if its ideals form a `RingFilterBasis`
for `A`. -/
theorem isUniform_iff_exists_ringFilterBasis :
    F.IsUniform ↔ ∃ B : RingFilterBasis A, B.sets = {s : Set A | ∃ I ∈ F, s = (I : Set A)} := by
  constructor
  · intro h_F
    refine ⟨F.ringFilterBasis h_F, ?_⟩
    ext s
    constructor <;>
    · intro h_s
      rcases h_s with ⟨I, h_I, rfl⟩
      exact ⟨I, h_I, rfl⟩
  · rintro ⟨B, h_B⟩
    exact {
      colon_closed := by
        intro I h_I a
        have h_IB : (I : Set A) ∈ B.sets := by
          rw [h_B]
          exact ⟨I, h_I, rfl⟩
        rcases RingFilterBasis.mul_right B a h_IB with ⟨V, h_VB : V ∈ B.sets, h_sub⟩
        rw[h_B] at h_VB
        rcases h_VB with ⟨J, h_J, rfl⟩
        refine Order.PFilter.mem_of_le ?_ h_J
        intro x hx
        refine Submodule.mem_colon.mpr ?_
        intro s hs
        simpa [Set.mem_singleton_iff.mp hs] using (Submodule.mem_toAddSubgroup I).mp (h_sub hx)
    }

/-- The topology on `A` induced by `addGroupFilterBasis`. -/
def addGroupTopology : TopologicalSpace A := (addGroupFilterBasis F).topology

/-- The topology `addGroupTopology` makes `A` a topological additive group. -/
theorem isTopologicalAddGroup :
    letI : TopologicalSpace A := F.addGroupTopology
    IsTopologicalAddGroup A :=
  F.addGroupFilterBasis.isTopologicalAddGroup

/-- Under `F.IsUniform`, the topology on `A` induced by `ringFilterBasis`. -/
def ringTopology (uni_F : F.IsUniform) : TopologicalSpace A :=
  (ringFilterBasis F uni_F).topology

/-- Under `F.IsUniform`, the topology `ringTopology` makes `A` a topological ring. -/
theorem isTopologicalRing (uni_F : F.IsUniform) :
    letI : TopologicalSpace A := F.ringTopology uni_F
    IsTopologicalRing A :=
  (F.ringFilterBasis uni_F).isTopologicalRing

/-- Neighbourhoods in `addGroupTopology`: a set is a neighbourhood of `a` iff it contains a
left-additive coset `a +ᵥ I` for some ideal `I ∈ F`. -/
lemma addGroupTopology_mem_nhds_iff (a : A) (s : Set A) :
    letI : TopologicalSpace A := F.addGroupTopology
    s ∈ 𝓝 a ↔ ∃ I ∈ F, a +ᵥ (I : Set A) ⊆ s := by
  constructor
  · intro h_s
    rcases ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.1 h_s with ⟨t, h_t, h_ts⟩
    rcases h_t with ⟨I, h_I, rfl⟩
    exact ⟨I, h_I, h_ts⟩
  · rintro ⟨I, h_I, h_Is⟩
    refine ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.2 ?_
    exact ⟨(I : Set A), ⟨I, h_I, rfl⟩, h_Is⟩

/-- In `F.addGroupTopology`, `s : Set A` is a neighbourhood of `0` iff it contains an ideal
belonging to `F`. -/
lemma addGroupTopology_mem_nhds_zero_iff (s : Set A) :
    letI : TopologicalSpace A := F.addGroupTopology
    s ∈ 𝓝 0 ↔ ∃ I ∈ F, (I : Set A) ⊆ s := by
  simpa [zero_vadd] using F.addGroupTopology_mem_nhds_iff (a := (0 : A)) (s := s)

/-- Neighbourhoods in `ringTopology`: a set is a neighbourhood of `a` iff it contains a
left-additive coset `a +ᵥ I` for some ideal `I ∈ F`. -/
lemma ringTopology_mem_nhds_iff (uni_F : F.IsUniform) (a : A) (s : Set A) :
    letI : TopologicalSpace A := F.ringTopology uni_F
    s ∈ 𝓝 a ↔ ∃ I ∈ F, a +ᵥ (I : Set A) ⊆ s := by
  constructor
  · intro h_s
    rcases ((F.ringFilterBasis uni_F).nhds_hasBasis a).mem_iff.1 h_s with ⟨t, h_t, h_ts⟩
    rcases h_t with ⟨I, h_I, rfl⟩
    exact ⟨I, h_I, h_ts⟩
  · rintro ⟨I, h_I, h_Is⟩
    refine ((F.ringFilterBasis uni_F).nhds_hasBasis a).mem_iff.2 ?_
    exact ⟨(I : Set A), ⟨I, h_I, rfl⟩, h_Is⟩

/-- In `F.ringTopology`, `s : Set A` is a neighbourhood of `0` iff it contains an ideal belonging
to `F`. -/
lemma ringTopology_mem_nhds_zero_iff (uni_F : F.IsUniform) (s : Set A) :
    letI : TopologicalSpace A := F.ringTopology uni_F
    s ∈ 𝓝 0 ↔ ∃ I ∈ F, (I : Set A) ⊆ s := by
  simpa [zero_vadd] using F.ringTopology_mem_nhds_iff (uni_F := uni_F) (a := (0 : A)) (s := s)

/-- Under `F.IsUniform`, the topology `ringTopology` is linear in the sense that `𝓝 0` has a
basis of ideals. -/
theorem isLinearTopology_ringTopology (uni_F : F.IsUniform) :
    letI : TopologicalSpace A := F.ringTopology uni_F
    IsLinearTopology A A := by
  letI : TopologicalSpace A := F.ringTopology uni_F
  have h_Basis :
      (𝓝 (0 : A)).HasBasis (fun I : Ideal A ↦ I ∈ F) (fun I : Ideal A ↦ (I : Set A)) := by
    refine ⟨?_⟩
    intro t
    exact ringTopology_mem_nhds_zero_iff F uni_F t
  refine IsLinearTopology.mk_of_hasBasis' (R := A) (M := A)
      (ι := Ideal A) (S := Ideal A)
      (p := fun I : Ideal A ↦ I ∈ F) (s := fun I : Ideal A ↦ I)
      ?_ ?_
  · exact h_Basis
  · intro I a m h_m
    exact Submodule.smul_mem I a h_m

end IdealFilter

/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Topology.Algebra.LinearTopology

/-! # Bounded subsets

Let `M` be a monoid with a zero, endowed with a topology.

* `IsBounded S` says that `S : Set M` is *bounded* if for every neighbourhood `U` of `0` there is
    some neighbourhood `V` satisfying `V * S ⊆ U`.

* `IsBounded.union`: the union of two bounded sets are bounded.

* `IsBounded.mul`: the product of two bounded sets are bounded.

Let `R` be a ring, endowed with a topology, such that multiplication is continuous.

* `isBounded_singleton`: every singleton is bounded.

* `isBounded_finite`: every finite set is bounded.

-/

@[expose] public section

open Filter Topology Pointwise Polynomial

namespace TopologicalRing

variable {M : Type*} [MonoidWithZero M] [TopologicalSpace M]

/-- A subset is bounded if for every nhd `U` of `0`, some nhd `V` satisfies `V * S ⊆ U`. -/
def IsBounded (S : Set M) : Prop := ∀ U ∈ 𝓝 (0 : M), ∃ V ∈ 𝓝 (0 : M), V * S ⊆ U

/-- Subsets of bounded sets are bounded. -/
theorem IsBounded.subset {S T : Set M} (hS : IsBounded S) (hTS : T ⊆ S) : IsBounded T :=
  fun U hU ↦ let ⟨V, hV, hSV⟩ := hS U hU
  ⟨V, hV, (Set.mul_subset_mul_left hTS).trans hSV⟩

/-- The empty set is bounded. -/
theorem isBounded_empty : IsBounded (∅ : Set M) :=
  fun U _ ↦ ⟨Set.univ, univ_mem, by simp⟩

/-- The singleton `{0}` is bounded. -/
theorem isBounded_singleton_zero : IsBounded ({0} : Set M) :=
  fun U hU ↦ ⟨Set.univ, univ_mem, fun x hx ↦ by simp_all [mem_of_mem_nhds hU]⟩

/-- The pair `{0, 1}` is bounded. -/
theorem isBounded_pair_zero_one : IsBounded ({0, 1} : Set M) :=
  fun U hU ↦ ⟨U, hU, fun _ hx ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    rcases Set.mem_insert_iff.mp hb with rfl | ha
    · rw [mul_zero]; exact mem_of_mem_nhds hU
    · rwa [Set.mem_singleton_iff.mp ha, mul_one]⟩

/-- Union of two bounded sets is bounded. -/
theorem IsBounded.union {S T : Set M} (hS : IsBounded S) (hT : IsBounded T) :
    IsBounded (S ∪ T) := by
  intro U hU
  obtain ⟨V₁, hV₁, hSV⟩ := hS U hU; obtain ⟨V₂, hV₂, hTV⟩ := hT U hU
  refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
  rw [Set.mul_union]
  refine Set.union_subset ?_ ?_
  · exact (Set.mul_subset_mul_right Set.inter_subset_left).trans hSV
  · exact (Set.mul_subset_mul_right Set.inter_subset_right).trans hTV

/-- Product of two bounded sets is bounded. -/
theorem IsBounded.mul {S T : Set M} (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S * T) := by
  intro U hU
  obtain ⟨W, hW, hTW⟩ := hT U hU
  obtain ⟨V, hV, hSV⟩ := hS W hW
  exact ⟨V, hV, by simpa [← mul_assoc] using (Set.mul_subset_mul_right hSV).trans hTW⟩

section Semiring

variable {R : Type*} [Semiring R] [TopologicalSpace R] [ContinuousMul R]

/-- Every singleton is bounded. -/
theorem isBounded_singleton (a : R) : IsBounded ({a} : Set R) :=
  fun U hU ↦ ⟨(· * a) ⁻¹' U, (continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds
    (by simp [hU]), by simp⟩

/-- Every finite subset is bounded. -/
theorem isBounded_finite {S : Set R} (hS : S.Finite) : IsBounded S := by
  refine Set.Finite.induction_on S hS ?_ ?_
  · exact isBounded_empty
  · intro a s _ _ ih
    exact Set.insert_eq a s ▸ (isBounded_singleton a).union ih

end Semiring

end TopologicalRing

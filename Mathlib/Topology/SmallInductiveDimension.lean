/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu, Andrew Yang
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Clopen

/-!
# Small inductive dimension

The small inductive dimension of a space is inductively defined as follows. Empty spaces have
small inductive dimension less than 0, and a topological space has dimension less than `n + 1` if
it has a topological basis whose elements have frontiers of dimension strictly less `n`.

In this file we formalize this notion, and characterize the cases `n = 0` and `n = 1`.

## Main definitions

* `HasSmallInductiveDimensionLT X n` : Provides a class stating that `X` has small inductive
  dimension less than `n`.
* `HasSmallInductiveDimensionLE X n` : Provides an abbrev for
  `HasSmallInductiveDimensionLT X (n + 1)`.
* `smallInductiveDimension X` : The small inductive dimension of `X`, with values in `WithBot ℕ∞`.

## References

* https://en.wikipedia.org/wiki/Inductive_dimension
-/

@[expose] public section

open Set TopologicalSpace

/--
For a topological space, the property of having small inductive dimension less than `n : ℕ`  is
inductively defined as follows. Empty spaces have small inductive dimension less than 0, and a
topological space has dimension less than `n + 1` if it has a topological basis whose elements have
frontiers of dimension strictly less `n`.
-/
class inductive HasSmallInductiveDimensionLT.{u} :
  ∀ (X : Type u) [TopologicalSpace X], ℕ → Prop where
  | zero {X : Type u} [TopologicalSpace X] [IsEmpty X] : HasSmallInductiveDimensionLT X 0
  | succ {X : Type u} [TopologicalSpace X] (n : ℕ) (s : Set (Set X)) (hs : IsTopologicalBasis s)
      (h : ∀ U ∈ s, HasSmallInductiveDimensionLT ↑(frontier U) n) :
      HasSmallInductiveDimensionLT X (n + 1)

variable (X : Type) [TopologicalSpace X]

/-- A topological space has dimension `≤ n` if it has dimension `< n + 1`. -/
abbrev HasSmallInductiveDimensionLE (n : ℕ) :=
  HasSmallInductiveDimensionLT X (n + 1)

/-- The small inductive dimension of a topological space. -/
noncomputable def smallInductiveDimension : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasSmallInductiveDimensionLT X i}

lemma HasSmallInductiveDimensionLT_zero_iff :
    HasSmallInductiveDimensionLT X 0 ↔ IsEmpty X :=
  ⟨fun h ↦ by cases h; assumption, fun _ ↦ .zero⟩

lemma HasSmallInductiveDimensionLT_one_iff :
    HasSmallInductiveDimensionLT X 1 ↔ IsTopologicalBasis { s : Set X | IsClopen s } := by
  constructor
  · intro (.succ _ s hs h)
    refine hs.of_isOpen_of_subset (fun _ hU ↦ hU.isOpen) (fun U hU ↦ ⟨?_, hs.isOpen hU⟩)
    rw [← closure_subset_iff_isClosed]
    cases h U hU
    rwa [isEmpty_coe_sort, (hs.isOpen hU).frontier_eq, sdiff_eq_empty] at ‹_›
  · exact fun h ↦ .succ 0 _ h fun _ hU ↦ hU.frontier_eq ▸ .zero

/-- The dimension bound is monotone: if `X` has small inductive dimension `< n`, then
it also has small inductive dimension `< n + 1`. -/
theorem HasSmallInductiveDimensionLT.step {X : Type*} [TopologicalSpace X] {n : ℕ}
    (h : HasSmallInductiveDimensionLT X n) : HasSmallInductiveDimensionLT X (n + 1) := by
  induction h with
  | zero =>
    exact .succ 0 ∅ (isTopologicalBasis_of_isOpen_of_nhds
      (fun _ h ↦ h.elim) (fun a ↦ IsEmpty.elim ‹IsEmpty _› a))
      (fun _ h ↦ h.elim)
  | succ n s hs _ ih => exact .succ (n + 1) s hs ih

/-- The dimension bound is monotone: if `n ≤ m` and `X` has small inductive dimension `< n`,
then `X` also has small inductive dimension `< m`. -/
theorem HasSmallInductiveDimensionLT.mono {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (hnm : n ≤ m) (h : HasSmallInductiveDimensionLT X n) : HasSmallInductiveDimensionLT X m := by
  have : ∀ k, HasSmallInductiveDimensionLT X (n + k) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih => exact ih.step
  convert this (m - n) using 1; omega

/-- A discrete topological space has small inductive dimension `< 1` (i.e., dimension `≤ 0`). -/
theorem hasSmallInductiveDimensionLT_one_of_discreteTopology {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] : HasSmallInductiveDimensionLT X 1 :=
  .succ 0 {s : Set X | IsClopen s}
    (isTopologicalBasis_of_isOpen_of_nhds (fun _ h ↦ h.isOpen)
      (fun a _ ha _ ↦ ⟨{a}, isClopen_discrete _, rfl, singleton_subset_iff.mpr ha⟩))
    (fun _ hU ↦ hU.frontier_eq ▸ .zero)

end

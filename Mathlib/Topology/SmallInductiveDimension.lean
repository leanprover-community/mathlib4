/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu, Andrew Yang
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected

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

open Set TopologicalSpace Topology

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
      (h : ∀ U ∈ s, HasSmallInductiveDimensionLT (frontier U) n) :
      HasSmallInductiveDimensionLT X (n + 1)

variable {X : Type*} [TopologicalSpace X]

variable (X) in
/-- A topological space has dimension `≤ n` if it has dimension `< n + 1`. -/
abbrev HasSmallInductiveDimensionLE (n : ℕ) :=
  HasSmallInductiveDimensionLT X (n + 1)

@[simp]
theorem hasSmallInductiveDimensionLT_zero_iff : HasSmallInductiveDimensionLT X 0 ↔ IsEmpty X :=
  ⟨fun h ↦ by cases h; assumption, fun _ ↦ .zero⟩

@[deprecated (since := "2026-06-21")]
alias HasSmallInductiveDimensionLT_zero_iff := hasSmallInductiveDimensionLT_zero_iff

theorem HasSmallInductiveDimensionLT.mono {m n : ℕ} (hmn : m ≤ n)
    (H : HasSmallInductiveDimensionLT X m) : HasSmallInductiveDimensionLT X n := by
  induction n generalizing m X with
  | zero => simp_all
  | succ m IH =>
    cases H with
    | zero => exact .succ _ ∅ (by simpa) (by simp)
    | succ n s hs h =>
      refine .succ _ s hs fun U hU ↦ IH ?_ (h U hU)
      rwa [add_le_add_iff_right] at hmn

theorem HasSmallInductiveDimensionLE.mono {m n : ℕ} (hmn : m ≤ n)
    (H : HasSmallInductiveDimensionLE X m) : HasSmallInductiveDimensionLE X n := by
  apply HasSmallInductiveDimensionLT.mono _ H
  rwa [add_le_add_iff_right]

theorem HasSmallInductiveDimensionLT.hasSmallInductiveDimensionLE {n : ℕ}
    (H : HasSmallInductiveDimensionLT X n) : HasSmallInductiveDimensionLE X n :=
  HasSmallInductiveDimensionLT.mono n.le_succ H

instance (n : ℕ) [IsEmpty X] : HasSmallInductiveDimensionLT X n :=
  .mono zero_le <| hasSmallInductiveDimensionLT_zero_iff.2 ‹_›

/-! ### Zero-dimensional spaces -/

variable (X) in
/-- A zero-dimensional topological space is defined as one with small inductive dimension ≤ 0. In
particular, our definition of `ZeroDimensionalSpace` allows the empty space even though, strictly
speaking, it is (-1)-dimensional.

An equivalent characterization is that a zero-dimensional space is one with a basis of clopen
sets. -/
abbrev ZeroDimensionalSpace :=
  HasSmallInductiveDimensionLT X 1

theorem zeroDimensionalSpace_def : ZeroDimensionalSpace X ↔ HasSmallInductiveDimensionLT X 1 :=
  .rfl

theorem zeroDimensionalSpace_def' : ZeroDimensionalSpace X ↔ HasSmallInductiveDimensionLE X 0 :=
  .rfl

lemma zeroDimensionalSpace_iff_isTopologicalBasis :
    ZeroDimensionalSpace X ↔ IsTopologicalBasis { s : Set X | IsClopen s } := by
  constructor
  · intro (.succ _ s hs h)
    refine hs.of_isOpen_of_subset (fun _ hU ↦ hU.isOpen) (fun U hU ↦ ⟨?_, hs.isOpen hU⟩)
    rw [← closure_subset_iff_isClosed]
    cases h U hU
    rwa [isEmpty_coe_sort, (hs.isOpen hU).frontier_eq, sdiff_eq_empty] at ‹_›
  · exact fun h ↦ .succ 0 _ h fun _ hU ↦ hU.frontier_eq ▸ .zero

@[deprecated (since := "2026-06-21")]
alias hasSmallInductiveDimensionLT_one_iff := zeroDimensionalSpace_iff_isTopologicalBasis

theorem isTopologicalBasis_isClopen [ZeroDimensionalSpace X] :
    IsTopologicalBasis { s : Set X | IsClopen s } :=
  zeroDimensionalSpace_iff_isTopologicalBasis.1 ‹_›

theorem zeroDimensionalSpace_iff_isTopologicalBasis_iff_nhds_basis :
    ZeroDimensionalSpace X ↔ ∀ x : X, (𝓝 x).HasBasis (fun s ↦ IsClopen s ∧ x ∈ s) id where
  mp _ _ := isTopologicalBasis_isClopen.nhds_hasBasis
  mpr H := by
    rw [zeroDimensionalSpace_iff_isTopologicalBasis]
    exact .of_hasBasis_nhds H

theorem exists_isClopen_mem_of_isOpen [ZeroDimensionalSpace X] {x : X} {U : Set X}
    (hU : IsOpen U) (hx : x ∈ U) : ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U :=
  isTopologicalBasis_isClopen.mem_nhds_iff.1 (hU.mem_nhds hx)

instance [DiscreteTopology X] : ZeroDimensionalSpace X := by
  rw [zeroDimensionalSpace_iff_isTopologicalBasis]
  simpa using isTopologicalBasis_opens (α := X)

instance [T0Space X] [ZeroDimensionalSpace X] : TotallySeparatedSpace X := by
  simp_rw [totallySeparatedSpace_iff_exists_isClopen, mem_compl_iff]
  intro x y hxy
  contrapose! hxy
  apply Inseparable.eq
  rw [isTopologicalBasis_isClopen.inseparable_iff]
  exact fun V hV ↦ ⟨hxy V hV, (hxy Vᶜ hV.compl).mtr⟩

/-! ### Small inductive dimension -/

variable (X) in
/-- The small inductive dimension of a topological space. -/
noncomputable def smallInductiveDimension : WithBot ℕ∞ :=
  sInf {n | ∀ i : ℕ, n < i → HasSmallInductiveDimensionLT X i}

private theorem hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt {n : ℕ}
    (h : smallInductiveDimension X < n) : HasSmallInductiveDimensionLT X n := by
  apply csInf_mem (s := {n : WithBot ℕ∞ | ∀ i : ℕ, n < i → HasSmallInductiveDimensionLT X i})
  · contrapose! h
    simp [smallInductiveDimension, h]
  · exact h

private theorem hasSmallInductiveDimensionLE_of_smallInductiveDimension_le {n : ℕ}
    (h : smallInductiveDimension X ≤ n) : HasSmallInductiveDimensionLE X n := by
  apply hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt (h.trans_lt _)
  exact_mod_cast n.lt_add_one

theorem smallInductiveDimension_le_iff {n : ℕ} :
    smallInductiveDimension X ≤ n ↔ HasSmallInductiveDimensionLE X n where
  mp := hasSmallInductiveDimensionLE_of_smallInductiveDimension_le
  mpr h := by
    refine csInf_le' fun m hm ↦ .mono ?_ h
    simpa using hm

theorem smallInductiveDimension_lt_iff {n : ℕ} :
    smallInductiveDimension X < n ↔ HasSmallInductiveDimensionLT X n where
  mp := hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt
  mpr h := by
    cases n with
    | zero =>
      rw [smallInductiveDimension, csInf_eq_bot_of_bot_mem]
      · simp
      · exact fun i _ ↦ h.mono zero_le
    | succ n =>
      apply (smallInductiveDimension_le_iff.2 h).trans_lt
      exact_mod_cast lt_add_one n

theorem smallInductiveDimension_eq (n : ℕ)
    (hle : HasSmallInductiveDimensionLE X n) (hlt : ¬ HasSmallInductiveDimensionLT X n) :
    smallInductiveDimension X = n := by
  apply (smallInductiveDimension_le_iff.2 hle).antisymm
  rwa [← not_lt, smallInductiveDimension_lt_iff]

@[simp]
theorem smallInductiveDimension_eq_bot : smallInductiveDimension X = ⊥ ↔ IsEmpty X := by
  rw [← hasSmallInductiveDimensionLT_zero_iff, ← smallInductiveDimension_lt_iff]
  exact WithBot.lt_coe_bot.symm

variable (X) in
@[simp]
theorem smallInductiveDimension_of_isEmpty [IsEmpty X] : smallInductiveDimension X = ⊥ :=
  smallInductiveDimension_eq_bot.2 ‹_›

theorem smallInductiveDimension_eq_zero :
    smallInductiveDimension X = 0 ↔ ZeroDimensionalSpace X ∧ Nonempty X := by
  rw [← not_isEmpty_iff, ← hasSmallInductiveDimensionLT_zero_iff]
  refine ⟨fun h ↦ ⟨smallInductiveDimension_le_iff.1 h.le, ?_⟩, fun ⟨_, h⟩ ↦ ?_⟩
  · rw [← smallInductiveDimension_lt_iff]
    simp [h]
  · apply smallInductiveDimension_eq _ _ h
    infer_instance

variable (X) in
@[simp]
theorem smallInductiveDimension_of_zeroDimensionalSpace [ZeroDimensionalSpace X] [Nonempty X] :
    smallInductiveDimension X = 0 :=
  smallInductiveDimension_eq_zero.2 ⟨‹_›, ‹_›⟩

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

open Set Topology TopologicalSpace

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

lemma HasSmallInductiveDimensionLT_one_iff :
    HasSmallInductiveDimensionLT X 1 ↔ IsTopologicalBasis { s : Set X | IsClopen s } := by
  constructor
  · intro (.succ _ s hs h)
    refine hs.of_isOpen_of_subset (fun _ hU ↦ hU.isOpen) (fun U hU ↦ ⟨?_, hs.isOpen hU⟩)
    rw [← closure_subset_iff_isClosed]
    cases h U hU
    rwa [isEmpty_coe_sort, (hs.isOpen hU).frontier_eq, sdiff_eq_empty] at ‹_›
  · exact fun h ↦ .succ 0 _ h fun _ hU ↦ hU.frontier_eq ▸ .zero

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

/-! ### Small inductive dimension -/

variable (X) in
/-- The small inductive dimension of a topological space. -/
noncomputable def smallInductiveDimension : WithBot ℕ∞ :=
  sInf {n | ∀ i : ℕ, n < i → HasSmallInductiveDimensionLT X i}

@[simp]
theorem smallInductiveDimension_eq_bot : smallInductiveDimension X = ⊥ ↔ IsEmpty X where
  mp h := by
    rw [smallInductiveDimension, sInf_eq_bot] at h
    obtain ⟨n, hn, hn'⟩ := h _ (WithBot.bot_lt_coe 0)
    have := hn 0 hn'
    rwa [← hasSmallInductiveDimensionLT_zero_iff]
  mpr _ := by
    refine csInf_eq_bot_of_bot_mem fun _ _ ↦ ?_
    infer_instance

variable (X) in
@[simp]
theorem smallInductiveDimension_of_isEmpty [IsEmpty X] : smallInductiveDimension X = ⊥ :=
  smallInductiveDimension_eq_bot.2 ‹_›

theorem smallInductiveDimension_le {n : ℕ} (h : HasSmallInductiveDimensionLE X n) :
    smallInductiveDimension X ≤ n := by
  refine csInf_le' fun m hm ↦ .mono ?_ h
  simpa using hm

theorem smallInductiveDimension_lt {n : ℕ} (h : HasSmallInductiveDimensionLT X n) :
    smallInductiveDimension X < n := by
  cases n with
  | zero => simp_all
  | succ n =>
    apply (smallInductiveDimension_le h).trans_lt
    exact_mod_cast lt_add_one n

theorem smallInductiveDimension_eq (n : ℕ)
    (hle : HasSmallInductiveDimensionLE X n) (hlt : ¬ HasSmallInductiveDimensionLT X n) :
    smallInductiveDimension X = n := by
  apply (smallInductiveDimension_le hle).antisymm
  rw [smallInductiveDimension, le_csInf_iff'']
  · intro m hm
    simpa using mt (hm n) hlt
  · refine ⟨n, fun m hm ↦ .mono ?_ hle⟩
    simpa using hm

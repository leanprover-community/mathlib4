/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne, David Ledvinka
-/
module

public import Mathlib.Dynamics.HittingTime
public import Mathlib.Probability.Process.Stopping

/-!
# Hitting times of stochastic processes

The hitting times of an adapted discrete process are stopping times. The pathwise definitions
and their deterministic properties are in `Mathlib/Dynamics/HittingTime.lean`.
For a process `u : ι → Ω → β`, its hitting time is `fun ω ↦ Function.hittingAfter (u · ω) s n`.

## Main results

* `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`: a bounded discrete hitting time of an
  adapted process is a stopping time.
* `MeasureTheory.Adapted.isStoppingTime_hittingAfter`: a discrete hitting time of an adapted
  process is a stopping time.
-/

public section

open Function

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

/-- A discrete hitting time is a stopping time. -/
theorem Adapted.isStoppingTime_hittingBtwn [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    [Countable ι] {_ : MeasurableSpace β} {f : Filtration ι m} {u : ι → Ω → β} {s : Set β}
    {n n' : ι} (hu : Adapted f u) (hs : MeasurableSet s) :
    IsStoppingTime f (fun ω ↦ (hittingBtwn (u · ω) s n n' : ι)) := by
  intro i
  rcases le_or_gt n' i with hi | hi
  · have h_le : ∀ ω, hittingBtwn (u · ω) s n n' ≤ i :=
      fun x => (hittingBtwn_le (u · x) s n n').trans hi
    simp [h_le]
  · have h_set_eq_Union : {ω | hittingBtwn (u · ω) s n n' ≤ i} = ⋃ j ∈ Set.Icc n i, u j ⁻¹' s := by
      ext; simp [hittingBtwn_le_iff_of_lt hi]
    simpa [h_set_eq_Union] using MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun hj => f.mono hj.2 _ ((hu j) hs)

theorem Adapted.isStoppingTime_hittingAfter [ConditionallyCompleteLinearOrder ι]
    [WellFoundedLT ι] [Countable ι] {_ : MeasurableSpace β} {f : Filtration ι m} {u : ι → Ω → β}
    {s : Set β} {n : ι} (hu : Adapted f u) (hs : MeasurableSet s) :
    IsStoppingTime f (fun ω ↦ hittingAfter (u · ω) s n) := by
  intro i
  have h_set_eq_Union : {ω | hittingAfter (u · ω) s n ≤ i} = ⋃ j ∈ Set.Icc n i, u j ⁻¹' s := by
    ext; simp [hittingAfter_le_iff]
  simpa [h_set_eq_Union] using MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun hj => f.mono hj.2 _ ((hu j) hs)

theorem stoppedValue_hittingBtwn_mem [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    {u : ι → Ω → β} {s : Set β} {n m : ι} {ω : Ω} (h : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    stoppedValue u (fun ω ↦ (hittingBtwn (u · ω) s n m : ι)) ω ∈ s :=
  hittingBtwn_mem_set h

/-- The hitting time of a discrete process with the starting time indexed by a stopping time
is a stopping time. -/
theorem Adapted.isStoppingTime_hittingBtwn_isStoppingTime [ConditionallyCompleteLinearOrder ι]
    [WellFoundedLT ι] [Countable ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace β] {f : Filtration ι m} {u : ι → Ω → β}
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime f τ)
    {N : ι} (hτbdd : ∀ x, τ x ≤ N) {s : Set β} (hs : MeasurableSet s) (hf : Adapted f u) :
    IsStoppingTime f fun x ↦ (hittingBtwn (u · x) s (τ x).untopA N : ι) := by
  intro n
  have h₁ : {x | hittingBtwn (u · x) s (τ x).untopA N ≤ n} =
    (⋃ i ≤ n, {x | τ x = i} ∩ {x | hittingBtwn (u · x) s i N ≤ n}) ∪
      ⋃ i > n, {x | τ x = i} ∩ {x | hittingBtwn (u · x) s i N ≤ n} := by
    ext x
    simp only [Set.mem_ofPred_eq, gt_iff_lt, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      exists_and_left, exists_prop]
    specialize hτbdd x
    have h_top : τ x ≠ ⊤ := fun h => by simp [h] at hτbdd
    lift τ x to ι using h_top with t
    simp [← or_and_right, le_or_gt]
  have h₂ : ⋃ i > n, {x | τ x = i} ∩ {x | hittingBtwn (u · x) s i N ≤ n} = ∅ := by
    ext x
    simp only [gt_iff_lt, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, exists_prop,
      Set.mem_empty_iff_false, iff_false, not_exists, not_and, not_le]
    refine fun m hm hτ ↦ hm.trans_le <| start_le_hittingBtwn ?_
    specialize hτbdd x
    have h_top : τ x ≠ ⊤ := fun h => by simp [h] at hτbdd
    lift τ x to ι using h_top with t
    rw [hτ] at hτbdd
    exact mod_cast hτbdd
  simp only [WithTop.coe_le_coe, h₁, h₂, Set.union_empty]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun hi =>
    (f.mono hi _ (hτ.measurableSet_eq i)).inter ?_
  simpa using hf.isStoppingTime_hittingBtwn hs n

end MeasureTheory

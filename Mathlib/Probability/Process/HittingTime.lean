/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Dynamics.HittingTime
public import Mathlib.Probability.Process.Stopping

/-!
# Hitting times of stochastic processes

This file contains results about the hitting times of stochastic processes. The definitions of
hitting times and their deterministic properties are in `Mathlib/Dynamics/HittingTime.lean`.
For a process `u : ι → Ω → β`, its hitting after time is
`fun ω ↦ Function.hittingAfter (u · ω) s n`.

## Main results

* `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`: a bounded discrete hitting time of an
  adapted process is a stopping time.
* `MeasureTheory.Adapted.isStoppingTime_hittingAfter`: a discrete hitting time of an adapted
  process is a stopping time.
-/

@[expose] public section

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

/-! ### Deprecated process-based hitting times

These declarations preserve the original process API during the transition to `Function.hittingBtwn`
and `Function.hittingAfter`.
-/

section Deprecated

section Basic

variable [Preorder ι] [InfSet ι] {u : ι → Ω → β}

-- Keep the original bodies so explicit unfolding in existing proofs still works.
open scoped Classical in
/-- Deprecated process-based version of `Function.hittingBtwn`. -/
@[deprecated Function.hittingBtwn
  "Use `fun ω ↦ Function.hittingBtwn (u · ω) s n m` instead." +typeChanged
  (since := "2026-11-08")]
noncomputable def hittingBtwn (u : ι → Ω → β)
    (s : Set β) (n m : ι) : Ω → ι :=
  fun x => if ∃ j ∈ Set.Icc n m, u j x ∈ s
    then sInf (Set.Icc n m ∩ {i : ι | u i x ∈ s}) else m

open scoped Classical in
/-- Deprecated process-based version of `Function.hittingAfter`. -/
@[deprecated Function.hittingAfter
  "Use `fun ω ↦ Function.hittingAfter (u · ω) s n` instead." +typeChanged
  (since := "2026-11-08")]
noncomputable def hittingAfter (u : ι → Ω → β) (s : Set β) (n : ι) :
    Ω → WithTop ι :=
  fun x ↦ if ∃ j, n ≤ j ∧ u j x ∈ s then (sInf {i : ι | n ≤ i ∧ u i x ∈ s} : ι) else ⊤

open scoped Classical in
@[deprecated Function.hittingBtwn_def +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_def (u : ι → Ω → β) (s : Set β) (n m : ι) :
    hittingBtwn u s n m =
    fun x => if ∃ j ∈ Set.Icc n m, u j x ∈ s then sInf (Set.Icc n m ∩ {i : ι | u i x ∈ s}) else m :=
  funext fun ω ↦ Function.hittingBtwn_def (u · ω) s n m

open scoped Classical in
@[deprecated Function.hittingAfter_def +typeChanged (since := "2026-11-08")]
lemma hittingAfter_def (u : ι → Ω → β) (s : Set β) (n : ι) :
    hittingAfter u s n =
    fun x => if ∃ j, n ≤ j ∧ u j x ∈ s
      then ((sInf {i : ι | n ≤ i ∧ u i x ∈ s} : ι) : WithTop ι) else ⊤ :=
  funext fun ω ↦ Function.hittingAfter_def (u · ω) s n

@[simp, deprecated Function.hittingBtwn_empty +typeChanged (since := "2026-11-08")]
lemma hittingBtwn_empty (n m : ι) : hittingBtwn u ∅ n m = fun _ ↦ m :=
  funext fun ω ↦ Function.hittingBtwn_empty (u · ω) n m

@[simp, deprecated Function.hittingAfter_empty +typeChanged (since := "2026-11-08")]
lemma hittingAfter_empty (n : ι) : hittingAfter u ∅ n = fun _ ↦ ⊤ :=
  funext fun ω ↦ Function.hittingAfter_empty (u · ω) n

@[simp, deprecated Function.hittingBtwn_univ +typeChanged (since := "2026-11-08")]
lemma hittingBtwn_univ {ι : Type*} [ConditionallyCompleteLinearOrder ι] {u : ι → Ω → β} (n m : ι) :
    hittingBtwn u .univ n m = fun _ ↦ min n m :=
  funext fun ω ↦ Function.hittingBtwn_univ (u · ω) n m

@[simp, deprecated Function.hittingAfter_univ +typeChanged (since := "2026-11-08")]
lemma hittingAfter_univ {ι : Type*} [ConditionallyCompleteLattice ι] {u : ι → Ω → β} (n : ι) :
    hittingAfter u .univ n = fun _ ↦ (n : WithTop ι) :=
  funext fun ω ↦ Function.hittingAfter_univ (u · ω) n

end Basic

section Inequalities

variable [ConditionallyCompleteLinearOrder ι] {u : ι → Ω → β} {s : Set β}
  {n i : ι} {ω : Ω}

@[deprecated Function.hittingBtwn_of_lt +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_of_lt {m : ι} (h : m < n) : hittingBtwn u s n m ω = m :=
  Function.hittingBtwn_of_lt h

@[deprecated Function.hittingBtwn_le +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_le {m : ι} (ω : Ω) : hittingBtwn u s n m ω ≤ m :=
  Function.hittingBtwn_le (u · ω) s n m

@[deprecated Function.notMem_of_lt_hittingBtwn +typeChanged (since := "2026-11-08")]
theorem notMem_of_lt_hittingBtwn {m k : ι} (hk₁ : k < hittingBtwn u s n m ω) (hk₂ : n ≤ k) :
    u k ω ∉ s :=
  Function.notMem_of_lt_hittingBtwn (f := fun i ↦ u i ω) hk₂ hk₁

@[deprecated Function.notMem_of_lt_hittingAfter +typeChanged (since := "2026-11-08")]
theorem notMem_of_lt_hittingAfter {k : ι} (hk₁ : k < hittingAfter u s n ω) (hk₂ : n ≤ k) :
    u k ω ∉ s :=
  Function.notMem_of_lt_hittingAfter (f := fun i ↦ u i ω) hk₂ hk₁

@[deprecated Function.hittingBtwn_eq_end_iff +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_eq_end_iff {m : ι} : hittingBtwn u s n m ω = m ↔
    (∃ j ∈ Set.Icc n m, u j ω ∈ s) → sInf (Set.Icc n m ∩ {i : ι | u i ω ∈ s}) = m :=
  Function.hittingBtwn_eq_end_iff

@[deprecated Function.hittingAfter_eq_top_iff +typeChanged (since := "2026-11-08")]
lemma hittingAfter_eq_top_iff : hittingAfter u s n ω = ⊤ ↔ ∀ j, n ≤ j → u j ω ∉ s :=
  Function.hittingAfter_eq_top_iff

@[deprecated Function.hittingBtwn_of_le +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_of_le {m : ι} (hmn : m ≤ n) : hittingBtwn u s n m ω = m :=
  Function.hittingBtwn_of_le hmn

@[deprecated Function.start_le_hittingBtwn +typeChanged (since := "2026-11-08")]
theorem le_hittingBtwn {m : ι} (hnm : n ≤ m) (ω : Ω) : n ≤ hittingBtwn u s n m ω :=
  Function.start_le_hittingBtwn hnm

@[deprecated Function.start_le_hittingAfter +typeChanged (since := "2026-11-08")]
lemma le_hittingAfter (ω : Ω) : n ≤ hittingAfter u s n ω :=
  Function.start_le_hittingAfter (u · ω) s n

@[deprecated Function.start_le_hittingBtwn_of_exists +typeChanged (since := "2026-11-08")]
theorem le_hittingBtwn_of_exists {m : ι} (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    n ≤ hittingBtwn u s n m ω :=
  Function.start_le_hittingBtwn_of_exists h_exists

@[deprecated Function.hittingBtwn_mem_Icc +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_mem_Icc {m : ι} (hnm : n ≤ m) (ω : Ω) : hittingBtwn u s n m ω ∈ Set.Icc n m :=
  Function.hittingBtwn_mem_Icc hnm

@[deprecated Function.hittingBtwn_mem_set +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_mem_set [WellFoundedLT ι] {m : ι} (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    u (hittingBtwn u s n m ω) ω ∈ s :=
  Function.hittingBtwn_mem_set h_exists

@[deprecated Function.hittingAfter_mem_set +typeChanged (since := "2026-11-08")]
lemma hittingAfter_mem_set [WellFoundedLT ι] (h_exists : ∃ j, n ≤ j ∧ u j ω ∈ s) :
    u (hittingAfter u s n ω).untopA ω ∈ s :=
  Function.hittingAfter_mem_set h_exists

@[deprecated Function.hittingBtwn_mem_set_of_hittingBtwn_lt +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_mem_set_of_hittingBtwn_lt [WellFoundedLT ι] {m : ι}
    (hl : hittingBtwn u s n m ω < m) :
    u (hittingBtwn u s n m ω) ω ∈ s :=
  Function.hittingBtwn_mem_set_of_hittingBtwn_lt hl

@[deprecated Function.hittingAfter_mem_set_of_ne_top +typeChanged (since := "2026-11-08")]
lemma hittingAfter_mem_set_of_ne_top [WellFoundedLT ι] (hl : hittingAfter u s n ω ≠ ⊤) :
    u (hittingAfter u s n ω).untopA ω ∈ s :=
  Function.hittingAfter_mem_set_of_ne_top hl

@[deprecated Function.hittingBtwn_le_of_mem +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_le_of_mem {m : ι} (hin : n ≤ i) (him : i ≤ m) (his : u i ω ∈ s) :
    hittingBtwn u s n m ω ≤ i :=
  Function.hittingBtwn_le_of_mem hin him his

@[deprecated Function.hittingAfter_le_of_mem +typeChanged (since := "2026-11-08")]
lemma hittingAfter_le_of_mem (hin : n ≤ i) (his : u i ω ∈ s) :
    hittingAfter u s n ω ≤ i :=
  Function.hittingAfter_le_of_mem hin his

@[deprecated Function.hittingBtwn_le_iff_of_exists +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_le_iff_of_exists [WellFoundedLT ι] {m : ι}
    (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    hittingBtwn u s n m ω ≤ i ↔ ∃ j ∈ Set.Icc n i, u j ω ∈ s :=
  Function.hittingBtwn_le_iff_of_exists h_exists

@[deprecated Function.hittingAfter_le_iff +typeChanged (since := "2026-11-08")]
lemma hittingAfter_le_iff [WellFoundedLT ι] :
    hittingAfter u s n ω ≤ i ↔ ∃ j ∈ Set.Icc n i, u j ω ∈ s :=
  Function.hittingAfter_le_iff

@[deprecated Function.hittingBtwn_le_iff_of_lt +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_le_iff_of_lt [WellFoundedLT ι] {m : ι} (i : ι) (hi : i < m) :
    hittingBtwn u s n m ω ≤ i ↔ ∃ j ∈ Set.Icc n i, u j ω ∈ s :=
  Function.hittingBtwn_le_iff_of_lt hi

@[deprecated Function.hittingBtwn_lt_iff +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_lt_iff {m : ι} (i : ι) (hi : i ≤ m) :
    hittingBtwn u s n m ω < i ↔ ∃ j ∈ Set.Ico n i, u j ω ∈ s :=
  Function.hittingBtwn_lt_iff hi

@[deprecated Function.hittingAfter_lt_iff +typeChanged (since := "2026-11-08")]
lemma hittingAfter_lt_iff :
    hittingAfter u s n ω < i ↔ ∃ j ∈ Set.Ico n i, u j ω ∈ s :=
  Function.hittingAfter_lt_iff

@[deprecated Function.hittingBtwn_eq_hittingBtwn_of_exists +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_eq_hittingBtwn_of_exists {m₁ m₂ : ι} (h : m₁ ≤ m₂)
    (h' : ∃ j ∈ Set.Icc n m₁, u j ω ∈ s) : hittingBtwn u s n m₁ ω = hittingBtwn u s n m₂ ω :=
  Function.hittingBtwn_eq_hittingBtwn_of_exists h h'

@[deprecated Function.hittingBtwn_set_antitone +typeChanged (since := "2026-11-08")]
lemma hittingBtwn_anti (u : ι → Ω → β) (n m : ι) : Antitone (hittingBtwn u · n m) :=
  fun _ _ h ω ↦ Function.hittingBtwn_set_antitone (u · ω) n m h

@[deprecated Function.hittingAfter_set_antitone +typeChanged (since := "2026-11-08")]
lemma hittingAfter_anti (u : ι → Ω → β) (n : ι) : Antitone (hittingAfter u · n) :=
  fun _ _ h ω ↦ Function.hittingAfter_set_antitone (u · ω) n h

@[deprecated Function.hittingBtwn_set_antitone +typeChanged (since := "2026-11-08")]
lemma hittingBtwn_apply_anti (u : ι → Ω → β) (n m : ι) (ω : Ω) :
    Antitone (hittingBtwn u · n m ω) :=
  Function.hittingBtwn_set_antitone (u · ω) n m

@[deprecated Function.hittingAfter_set_antitone +typeChanged (since := "2026-11-08")]
lemma hittingAfter_apply_anti (u : ι → Ω → β) (n : ι) (ω : Ω) :
    Antitone (hittingAfter u · n ω) :=
  Function.hittingAfter_set_antitone (u · ω) n

@[deprecated Function.hittingBtwn_end_monotone +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_mono_right (u : ι → Ω → β) (s : Set β) (n : ι) :
    Monotone (hittingBtwn u s n · ω) :=
  Function.hittingBtwn_end_monotone (u · ω) s n

@[deprecated Function.hittingBtwn_start_monotone +typeChanged (since := "2026-11-08")]
lemma hittingBtwn_mono_left (u : ι → Ω → β) (s : Set β) (m : ι) :
    Monotone (hittingBtwn u s · m) :=
  fun _ _ h ω ↦ Function.hittingBtwn_start_monotone (u · ω) s m h

@[deprecated Function.hittingAfter_start_monotone +typeChanged (since := "2026-11-08")]
lemma hittingAfter_mono (u : ι → Ω → β) (s : Set β) : Monotone (hittingAfter u s) :=
  fun _ _ h ω ↦ Function.hittingAfter_start_monotone (u · ω) s h

@[deprecated Function.hittingBtwn_end_monotone +typeChanged (since := "2026-11-08")]
lemma hittingBtwn_apply_mono_right (u : ι → Ω → β) (s : Set β) (n : ι) (ω : Ω) :
    Monotone (hittingBtwn u s n · ω) :=
  Function.hittingBtwn_end_monotone (u · ω) s n

@[deprecated Function.hittingBtwn_start_monotone +typeChanged (since := "2026-11-08")]
lemma hittingBtwn_apply_mono_left (u : ι → Ω → β) (s : Set β) (m : ι) (ω : Ω) :
    Monotone (hittingBtwn u s · m ω) :=
  Function.hittingBtwn_start_monotone (u · ω) s m

@[deprecated Function.hittingAfter_start_monotone +typeChanged (since := "2026-11-08")]
lemma hittingAfter_apply_mono (u : ι → Ω → β) (s : Set β) (ω : Ω) :
    Monotone (hittingAfter u s · ω) :=
  Function.hittingAfter_start_monotone (u · ω) s

end Inequalities

section CompleteLattice

variable [CompleteLattice ι] {u : ι → Ω → β} {s : Set β}

@[deprecated Function.hittingBtwn_bot_top +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_eq_sInf (ω : Ω) : hittingBtwn u s ⊥ ⊤ ω = sInf {i : ι | u i ω ∈ s} :=
  Function.hittingBtwn_bot_top

@[deprecated Function.hittingAfter_bot +typeChanged (since := "2026-11-08")]
lemma hittingAfter_eq_sInf [∀ ω, Decidable (∃ j, u j ω ∈ s)] (ω : Ω) :
    hittingAfter u s ⊥ ω
      = if ∃ j, u j ω ∈ s then ((sInf {i : ι | u i ω ∈ s} : ι) : WithTop ι)
        else (⊤ : WithTop ι) := by
  simp [hittingAfter_def]

end CompleteLattice

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
  {u : ι → Ω → β} {s : Set β}

@[deprecated Function.hittingBtwn_bot_le_iff +typeChanged (since := "2026-11-08")]
theorem hittingBtwn_bot_le_iff {i n : ι} {ω : Ω} (hx : ∃ j, j ≤ n ∧ u j ω ∈ s) :
    hittingBtwn u s ⊥ n ω ≤ i ↔ ∃ j ≤ i, u j ω ∈ s :=
  Function.hittingBtwn_bot_le_iff hx

@[deprecated Function.hittingAfter_bot_le_iff +typeChanged (since := "2026-11-08")]
theorem hittingAfter_bot_le_iff {i : ι} {ω : Ω} :
    hittingAfter u s ⊥ ω ≤ i ↔ ∃ j ≤ i, u j ω ∈ s :=
  Function.hittingAfter_bot_le_iff

end ConditionallyCompleteLinearOrderBot

end Deprecated

end MeasureTheory

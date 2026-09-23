/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Almost everywhere disjoint sets

We say that sets `s` and `t` are `μ`-a.e. disjoint (see `MeasureTheory.AEDisjoint`) if their
intersection has measure zero. This assumption can be used instead of `Disjoint` in most theorems in
measure theory.
-/

@[expose] public section


open Set Function

namespace MeasureTheory

variable {ι α : Type*} {m : MeasurableSpace α} (μ : Measure α)

/-- Two sets are said to be `μ`-a.e. disjoint if their intersection has measure zero. -/
def AEDisjoint (s t : Set α) :=
  μ (s ∩ t) = 0

variable {μ} {s t u v : Set α}

/-- If `s : ι → Set α` is a countable family of pairwise a.e. disjoint sets, then there exists a
family of measurable null sets `t i` such that `s i \ t i` are pairwise disjoint. -/
theorem exists_null_pairwise_disjoint_diff [Countable ι] {s : ι → Set α}
    (hd : Pairwise (AEDisjoint μ on s)) : ∃ t : ι → Set α, (∀ i, MeasurableSet (t i)) ∧
    (∀ i, μ (t i) = 0) ∧ Pairwise (Disjoint on fun i => s i \ t i) := by
  refine ⟨fun i => toMeasurable μ (s i ∩ ⋃ j ∈ ({i}ᶜ : Set ι), s j), fun i =>
    measurableSet_toMeasurable _ _, fun i => ?_, ?_⟩
  · simp only [measure_toMeasurable, inter_iUnion]
    exact (measure_biUnion_null_iff <| to_countable _).2 fun j hj => hd (Ne.symm hj)
  · simp only [Pairwise, disjoint_left, onFun, mem_diff, not_and, and_imp, Classical.not_not]
    intro i j hne x hi hU hj
    replace hU : x ∉ s i ∩ iUnion fun j ↦ iUnion fun _ ↦ s j :=
      fun h ↦ hU (subset_toMeasurable _ _ h)
    simp only [mem_inter_iff, mem_iUnion, not_and, not_exists] at hU
    exact (hU hi j hne.symm hj).elim

namespace AEDisjoint

protected theorem eq (h : AEDisjoint μ s t) : μ (s ∩ t) = 0 :=
  h

@[symm]
protected theorem symm (h : AEDisjoint μ s t) : AEDisjoint μ t s := by rwa [AEDisjoint, inter_comm]

protected theorem symmetric : Symmetric (AEDisjoint μ) := fun _ _ => AEDisjoint.symm

protected theorem comm : AEDisjoint μ s t ↔ AEDisjoint μ t s :=
  ⟨AEDisjoint.symm, AEDisjoint.symm⟩

protected theorem _root_.Disjoint.aedisjoint (h : Disjoint s t) : AEDisjoint μ s t := by
  rw [AEDisjoint, disjoint_iff_inter_eq_empty.1 h, measure_empty]

protected theorem _root_.Pairwise.aedisjoint {f : ι → Set α} (hf : Pairwise (Disjoint on f)) :
    Pairwise (AEDisjoint μ on f) :=
  hf.mono fun _i _j h => h.aedisjoint

protected theorem _root_.Set.PairwiseDisjoint.aedisjoint {f : ι → Set α} {s : Set ι}
    (hf : s.PairwiseDisjoint f) : s.Pairwise (AEDisjoint μ on f) :=
  hf.mono' fun _i _j h => h.aedisjoint

theorem mono_ae (h : AEDisjoint μ s t) (hu : u ≤ᵐ[μ] s) (hv : v ≤ᵐ[μ] t) : AEDisjoint μ u v :=
  measure_mono_null_ae (hu.inter hv) h

protected theorem mono (h : AEDisjoint μ s t) (hu : u ⊆ s) (hv : v ⊆ t) : AEDisjoint μ u v :=
  mono_ae h (HasSubset.Subset.eventuallyLE hu) (HasSubset.Subset.eventuallyLE hv)

protected theorem congr (h : AEDisjoint μ s t) (hu : u =ᵐ[μ] s) (hv : v =ᵐ[μ] t) :
    AEDisjoint μ u v :=
  mono_ae h (Filter.EventuallyEq.le hu) (Filter.EventuallyEq.le hv)

@[simp]
theorem iUnion_left_iff {ι : Sort*} [Countable ι] {s : ι → Set α} :
    AEDisjoint μ (⋃ i, s i) t ↔ ∀ i, AEDisjoint μ (s i) t := by
  simp only [AEDisjoint, iUnion_inter, measure_iUnion_null_iff]

@[simp]
theorem iUnion_right_iff {ι : Sort*} [Countable ι] {t : ι → Set α} :
    AEDisjoint μ s (⋃ i, t i) ↔ ∀ i, AEDisjoint μ s (t i) := by
  simp only [AEDisjoint, inter_iUnion, measure_iUnion_null_iff]

@[simp]
theorem union_left_iff : AEDisjoint μ (s ∪ t) u ↔ AEDisjoint μ s u ∧ AEDisjoint μ t u := by
  simp [union_eq_iUnion, and_comm]

@[simp]
theorem union_right_iff : AEDisjoint μ s (t ∪ u) ↔ AEDisjoint μ s t ∧ AEDisjoint μ s u := by
  simp [union_eq_iUnion, and_comm]

theorem union_left (hs : AEDisjoint μ s u) (ht : AEDisjoint μ t u) : AEDisjoint μ (s ∪ t) u :=
  union_left_iff.mpr ⟨hs, ht⟩

theorem union_right (ht : AEDisjoint μ s t) (hu : AEDisjoint μ s u) : AEDisjoint μ s (t ∪ u) :=
  union_right_iff.2 ⟨ht, hu⟩

theorem diff_ae_eq_left (h : AEDisjoint μ s t) : (s \ t : Set α) =ᵐ[μ] s :=
  @diff_self_inter _ s t ▸ diff_null_ae_eq_self h

theorem diff_ae_eq_right (h : AEDisjoint μ s t) : (t \ s : Set α) =ᵐ[μ] t :=
  diff_ae_eq_left <| AEDisjoint.symm h

theorem measure_diff_left (h : AEDisjoint μ s t) : μ (s \ t) = μ s :=
  measure_congr <| AEDisjoint.diff_ae_eq_left h

theorem measure_diff_right (h : AEDisjoint μ s t) : μ (t \ s) = μ t :=
  measure_congr <| AEDisjoint.diff_ae_eq_right h

/-- If `s` and `t` are `μ`-a.e. disjoint, then `s \ u` and `t` are disjoint for some measurable null
set `u`. -/
theorem exists_disjoint_diff (h : AEDisjoint μ s t) :
    ∃ u, MeasurableSet u ∧ μ u = 0 ∧ Disjoint (s \ u) t :=
  ⟨toMeasurable μ (s ∩ t), measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans h,
    disjoint_sdiff_self_left.mono_left (b := s \ t) fun x hx => by
      simpa using ⟨hx.1, fun hxt => hx.2 <| subset_toMeasurable _ _ ⟨hx.1, hxt⟩⟩⟩

theorem of_null_right (h : μ t = 0) : AEDisjoint μ s t :=
  measure_mono_null inter_subset_right h

theorem of_null_left (h : μ s = 0) : AEDisjoint μ s t :=
  AEDisjoint.symm (of_null_right h)

end AEDisjoint

theorem aedisjoint_compl_left : AEDisjoint μ sᶜ s :=
  (@disjoint_compl_left _ _ s).aedisjoint

theorem aedisjoint_compl_right : AEDisjoint μ s sᶜ :=
  (@disjoint_compl_right _ _ s).aedisjoint

end MeasureTheory

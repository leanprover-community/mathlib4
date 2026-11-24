/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import Mathlib.Probability.Process.Stopping

/-!
# Stopped information from cofinal deterministic caps

A cofinal increasing sequence of caps recovers the stopped sigma-algebra,
including its trace where the original stopping time is infinite.
-/

@[expose] public section

open Filter Order TopologicalSpace WithTop
open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory.IsStoppingTime

variable {Ω ι : Type*} {m : MeasurableSpace Ω}
  [LinearOrder ι] {f : Filtration ι m} {τ : Ω → WithTop ι}

/-- The σ-algebras obtained by capping a stopping time at a cofinal sequence of deterministic
times generate the original stopped σ-algebra, including on the event that the time is infinite. -/
theorem iSup_measurableSpace_min_const_eq (hτ : IsStoppingTime f τ) {c : ℕ → ι}
    (hc : Monotone c) (hcofinal : ∀ t, ∃ n, t ≤ c n) :
    (⨆ n, (hτ.min_const (c n)).measurableSpace) = hτ.measurableSpace := by
  classical
  let M := ⨆ n, (hτ.min_const (c n)).measurableSpace
  let Z : Set Ω := {ω | τ ω = ⊤}
  have hcover (ω : Ω) (hω : τ ω ≠ ⊤) : ∃ n, τ ω ≤ c n := by
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hω
    obtain ⟨n, hn⟩ := hcofinal t
    refine ⟨n, ?_⟩
    rw [← ht]
    exact WithTop.coe_le_coe.mpr hn
  have htail {n : ℕ} {A : Set Ω} (hA : MeasurableSet[f (c n)] A) :
      MeasurableSet[M] (A \ {ω | τ ω ≤ c n}) := by
    have ha := hA.diff (hτ (c n))
    refine le_iSup (fun k ↦ (hτ.min_const (c k)).measurableSpace) n _ ?_
    refine (hτ.measurableSet_min_const_iff _).2 ⟨?_, ha⟩
    refine (hτ.measurableSet _).2 ⟨le_iSup f (c n) _ ha, fun t ↦ ?_⟩
    by_cases ht : t ≤ c n
    · have he : (A \ {ω | τ ω ≤ c n}) ∩ {ω | τ ω ≤ t} = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
        exact ⟨fun h ↦ h.1.2 (h.2.trans (WithTop.coe_le_coe.mpr ht)), False.elim⟩
      rw [he]
      exact @MeasurableSet.empty Ω (f t)
    · exact (f.mono (le_of_not_ge ht) _ ha).inter (hτ t)
  have hgen (t : ι) (A : Set Ω) (hA : MeasurableSet[f t] A) : MeasurableSet[M] (A ∩ Z) := by
    obtain ⟨j, hj⟩ := hcofinal t
    have he : A ∩ Z = ⋂ k : ℕ, A \ {ω | τ ω ≤ c (max j k)} := by
      ext ω
      simp only [Z, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_sdiff]
      constructor
      · rintro ⟨ha, ht⟩ k
        exact ⟨ha, by simp [ht]⟩
      · intro h
        refine ⟨(h 0).1, ?_⟩
        by_contra hne
        obtain ⟨k, hk⟩ := hcover ω hne
        exact (h k).2 (hk.trans (WithTop.coe_le_coe.mpr (hc (le_max_right j k))))
    rw [he]
    exact MeasurableSet.iInter fun k ↦ htail (f.mono (hj.trans (hc (le_max_left j k))) _ hA)
  have htrace {A : Set Ω} (hA : MeasurableSet[⨆ t, f t] A) : MeasurableSet[M] (A ∩ Z) := by
    have hZ : MeasurableSet[M] Z := by
      simpa only [Set.univ_inter] using hgen (c 0) Set.univ MeasurableSet.univ
    rw [MeasurableSpace.measurableSet_iSup] at hA
    induction hA with
    | basic s hs =>
      obtain ⟨t, ht⟩ := hs
      exact hgen t s ht
    | empty => simp
    | compl s _ ih =>
      have he : sᶜ ∩ Z = Z \ (s ∩ Z) := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
        exact ⟨fun ⟨hn, hz⟩ ↦ ⟨hz, fun h ↦ hn h.1⟩,
          fun ⟨hz, hn⟩ ↦ ⟨fun hs ↦ hn ⟨hs, hz⟩, hz⟩⟩
      rw [he]
      exact hZ.diff ih
    | iUnion s _ ih =>
      rw [Set.iUnion_inter]
      exact MeasurableSet.iUnion ih
  refine le_antisymm (iSup_le fun n ↦ (hτ.min_const (c n)).measurableSpace_mono hτ
    (fun _ ↦ min_le_left _ _)) ?_
  intro A hA
  have hfin (n : ℕ) : MeasurableSet[M] (A ∩ {ω | τ ω ≤ c n}) :=
    le_iSup (fun k ↦ (hτ.min_const (c k)).measurableSpace) n _
      ((hτ.measurableSet_inter_le_const_iff A (c n)).1 (hA.inter (hτ.measurableSet_le' (c n))))
  have he : A = (⋃ n, A ∩ {ω | τ ω ≤ c n}) ∪ (A ∩ Z) := by
    ext ω
    simp only [Z, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro ha
      by_cases ht : τ ω = ⊤
      · exact Or.inr ⟨ha, ht⟩
      · obtain ⟨n, hn⟩ := hcover ω ht
        exact Or.inl ⟨n, ha, hn⟩
    · rintro (⟨_, ha, _⟩ | ⟨ha, _⟩)
      · exact ha
      · exact ha
  change MeasurableSet[M] A
  rw [he]
  exact (MeasurableSet.iUnion hfin).union (htrace ((hτ.measurableSet A).1 hA).1)

end MeasureTheory.IsStoppingTime

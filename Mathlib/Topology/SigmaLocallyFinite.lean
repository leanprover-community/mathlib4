/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Order.Disjointed
public import Mathlib.Topology.LocallyFinite

/-! # `σ`-locally finite families of sets
In this file we define σ-locally finite families of sets, i.e. families of sets that consist of
countably many locally finite families.

## References

* [Engelking, *General Topology*][engelking1989]
-/

public section

universe u

open Set Function

variable {ι X : Type*} [TopologicalSpace X] {s t : ι → Set X}

/-- A family of sets is *σ-locally finite* if it can be split into countably many locally finite
families. -/
@[expose]
def SigmaLocallyFinite (s : ι → Set X) :=
  ∃ κ : ℕ → Set ι, ⋃ n, κ n = univ ∧ ∀ n, LocallyFinite (fun k : κ n ↦ s k)

lemma sigmaLocallyFinite_iff_exists_fun : SigmaLocallyFinite s ↔
    ∃ κ : ℕ → Set ι, ⋃ n, κ n = univ ∧ ∀ n, LocallyFinite (fun k : κ n ↦ s k) :=
  Iff.rfl

lemma sigmaLocallyFinite_iff_exists_equiv {ι : Type u} {s : ι → Set X} : SigmaLocallyFinite s ↔
    ∃ κ : ℕ → Type u, ∃ e : ι ≃ Σ n, κ n, ∀ n, LocallyFinite (fun k ↦ s (e.symm ⟨n, k⟩)) := by
  refine ⟨fun h ↦ ?_, fun ⟨κ, e, he⟩ ↦ ?_⟩
  · have ⟨f, hf, hf', hf''⟩ : ∃ κ : ℕ → Set ι,
        ⋃ n, κ n = univ ∧ univ.PairwiseDisjoint κ ∧ ∀ n, LocallyFinite (fun k : κ n ↦ s k) := by
      obtain ⟨f, hf⟩ := h
      refine ⟨disjointed f, ?_, ?_, fun n ↦ ?_⟩
      · rw [iUnion_disjointed, hf.1]
      · exact pairwise_univ.2 <| disjoint_disjointed f
      · exact (hf.2 n).comp_injective <| inclusion_injective <| disjointed_subset f n
    refine ⟨fun n ↦ f n, (Equiv.ofBijective (fun i ↦ i.snd) ⟨?_, fun i ↦ ?_⟩).symm, fun n ↦ ?_⟩
    · intro i i' h
      have := pairwiseDisjoint_iff.1 hf' (mem_univ i.fst) (mem_univ i'.fst) ⟨i.snd, by grind⟩
      ext <;> assumption
    · have ⟨n, hi⟩ := iUnion_eq_univ_iff.1 hf i
      use ⟨n, ⟨i, hi⟩⟩
    · simp [hf'', Equiv.ofBijective]
  · refine ⟨fun n ↦ e ⁻¹' range (Sigma.mk n), ?_, fun n ↦ ?_⟩
    · simp [← preimage_iUnion, iUnion_of_singleton]
    · refine .of_comp_surjective (g := fun k ↦ ⟨e.symm ⟨n, k⟩, by simp⟩) ?_ ?_
      · exact (surjective_codRestrict _).2 <| by grind
      · convert he n; simp

lemma LocallyFinite.sigmaLocallyFinite (hu : LocallyFinite s) : SigmaLocallyFinite s :=
  ⟨fun _ ↦ univ, by simp [iUnion_const], fun n ↦ hu.comp_injective Subtype.val_injective⟩

lemma sigmaLocallyFinite_of_countable [Countable ι] : SigmaLocallyFinite s := by
  obtain _ | _ := isEmpty_or_nonempty ι
  · exact ⟨fun _ ↦ ∅, by simp [univ_eq_empty_iff.2], fun n ↦ locallyFinite_of_finite _⟩
  · have ⟨f, hf⟩ := (countable_iff_exists_surjective (α := ι)).1 ‹_›
    exact ⟨fun n ↦ {f n}, by simp [hf.range_eq], fun n ↦ locallyFinite_of_finite _⟩

lemma SigmaLocallyFinite.point_countable (hs : SigmaLocallyFinite s) (x : X) :
    {i : ι | x ∈ s i}.Countable := by
  obtain ⟨f, hf⟩ := hs
  rw [← Set.inter_univ {i : ι | x ∈ s i}, ← hf.1, inter_iUnion, countable_iUnion_iff]
  refine fun n ↦ Finite.countable <| (((hf.2 n).point_finite x).image (↑)).subset fun _ ↦ ?_
  simp

protected lemma SigmaLocallyFinite.subset (ht : SigmaLocallyFinite t) (h : ∀ i, s i ⊆ t i) :
    SigmaLocallyFinite s := by
  obtain ⟨f, hf⟩ := ht
  exact ⟨f, hf.1, fun n ↦ (hf.2 n).subset fun _ ↦ h _⟩

lemma SigmaLocallyFinite.comp_injOn (hs : SigmaLocallyFinite s) {κ : Type*} {f : κ → ι}
    (hf : InjOn f {i | (s (f i)).Nonempty}) : SigmaLocallyFinite (s ∘ f) := by
  obtain ⟨g, hg⟩ := hs
  refine ⟨fun n ↦ f ⁻¹' g n, by simp [← preimage_iUnion, hg.1], fun n ↦ ?_⟩
  exact (hg.2 n).comp_injOn (g := (mapsTo_preimage f _).restrict _ _ _) <| hf.restrict _

lemma SigmaLocallyFinite.comp_injective (hs : SigmaLocallyFinite s) {κ : Type*} {f : κ → ι}
    (hf : Injective f) : SigmaLocallyFinite (s ∘ f) :=
  hs.comp_injOn hf.injOn

lemma SigmaLocallyFinite.of_comp_surjective {κ : Type*} {f : κ → ι}
    (hf : Surjective f) (hs : SigmaLocallyFinite (s ∘ f)) : SigmaLocallyFinite s := by
  simpa only [comp_def, surjInv_eq hf] using hs.comp_injective (injective_surjInv hf)

protected lemma SigmaLocallyFinite.closure (hs : SigmaLocallyFinite s) :
    SigmaLocallyFinite (fun i ↦ closure (s i)) := by
  obtain ⟨f, hf⟩ := hs
  exact ⟨f, hf.1, fun n ↦ (hf.2 n).closure⟩

lemma SigmaLocallyFinite.preimage_continuous (hs : SigmaLocallyFinite s)
    {Y : Type*} [TopologicalSpace Y] {f : Y → X} (hf : Continuous f) :
    SigmaLocallyFinite (fun i ↦ f ⁻¹' s i) := by
  obtain ⟨g, hg⟩ := hs
  exact ⟨g, hg.1, fun n ↦ (hg.2 n).preimage_continuous hf⟩

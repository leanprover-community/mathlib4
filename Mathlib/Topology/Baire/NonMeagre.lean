/-
Copyright (c) 2025 Shaun Allison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaun Allison
-/
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.Lemmas

/-!
# Non-Meagre Sets

This file defines `IsNonMeagre` as `¬ IsMeagre A` and proves basic properties of these sets.
Historically these are often called "of the second category" while meagre sets are "of the first
category". These are of generally of interest in the context of a Baire Space.
-/

open Function Topology TopologicalSpace Set

variable {α : Type*} [TopologicalSpace α]
variable {s t : Set α}

abbrev IsNonMeagre (A : Set α) : Prop := ¬ IsMeagre A

theorem IsNonMeagre.nonempty [Nonempty α] (hs : IsNonMeagre s) : s.Nonempty := by
  contrapose! hs
  exact hs ▸ IsMeagre.empty

lemma IsNonMeagre.mono (hs : IsNonMeagre s) (hst : s ⊆ t) : IsNonMeagre t :=
  mt (IsMeagre.mono · hst) hs

lemma IsNonMeagre.congr_residual (hst : s =ᵇ t) : IsNonMeagre s ↔ IsNonMeagre t := by
  have : IsMeagre s ↔ IsMeagre t := by exact isMeagre_congr_residual hst
  exact not_congr this

lemma BaireMeasurableSet.IsNonMeagre_residualEq_isOpen_Nonempty (hBM : BaireMeasurableSet s)
    (hNM : IsNonMeagre s) : ∃ u : Set α, (IsOpen u) ∧ u.Nonempty ∧ s =ᵇ u := by
  rcases hBM.residualEq_isOpen with ⟨u, h_open, h_su⟩
  refine ⟨u, h_open, ?_, h_su⟩
  rw [IsNonMeagre.congr_residual h_su] at hNM
  exact nonempty_of_not_isMeagre hNM

theorem IsOpen.IsNonMeagre_of_Nonempty [BaireSpace α] (h_open : IsOpen s) (h_ne : s.Nonempty)
     : IsNonMeagre s := by
  by_contra h_meagre
  apply dense_of_mem_residual at h_meagre
  have : (s ∩ sᶜ).Nonempty := Dense.inter_open_nonempty h_meagre s h_open h_ne
  simp only [inter_compl_self, Set.not_nonempty_empty] at this

theorem IsNonMeagre.univ [Nonempty α] [BaireSpace α] : IsNonMeagre (univ : Set α) := by
  simp [IsNonMeagre, IsMeagre]
  by_contra h
  have : False := Set.not_nonempty_empty (dense_of_mem_residual h).nonempty
  contradiction

theorem IsNonMeagre.of_nonempty_interior [BaireSpace α] (hs : (interior s).Nonempty)
    : IsNonMeagre s :=
  IsNonMeagre.mono (isOpen_interior.IsNonMeagre_of_Nonempty hs) interior_subset

theorem IsNonMeagre.of_mem_nhds [BaireSpace α] {a : α} (hs : s ∈ 𝓝 a)
    : IsNonMeagre s := by
  obtain ⟨U, hUs, hU_open, h_aU⟩ := mem_nhds_iff.mp hs
  exact IsNonMeagre.mono (hU_open.IsNonMeagre_of_Nonempty ⟨a, h_aU⟩) hUs

/-- If a countable union of sets covers the space, then one of the sets is non meagre. -/
theorem IsNonMeagre.of_iUnion_univ {ι : Sort*} [Nonempty α] [BaireSpace α] [Countable ι]
  {f : ι → Set α} (hU : ⋃ i, f i = Set.univ) : ∃ i, IsNonMeagre (f i) := by
  by_contra! h
  have : IsMeagre (Set.univ : Set α) := by
    rw [←hU]
    exact isMeagre_iUnion h
  have : False := IsNonMeagre.univ this
  contradiction

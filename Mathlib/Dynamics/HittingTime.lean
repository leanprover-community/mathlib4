/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne, David Ledvinka
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.WithTop

/-!
# Hitting times of paths

Given a path `f : ι → E`, we define the "hitting after" and "hitting between" times of a set
and their basic API. These are typically used in the context of probability theory in one of
two ways:

* If `P : Measure (ι → E)` is a distribution on paths, then
  `P.map (fun f ↦ hittingAfter f A t₀)` is the distribution of its hitting time.
* If `X : Ω → ι → E` is a random path then `fun ω ↦ hittingAfter (X ω) A t₀`
  gives its random hitting time.

## Main definitions

* `Function.hittingAfter f A t₀`: the infimum of visits to `A` at or after `t₀`,
  or `⊤` if there are none.
* `Function.hittingBtwn f A t₀ t₁`: the infimum of visits to `A` in `[t₀, t₁]`,
  or `t₁` if there are none.

-/

@[expose] public section

open Set

namespace Function

variable {ι E F : Type*}

section Basic

variable [Preorder ι] [InfSet ι] {f : ι → E} {A : Set E} {t₀ t₁ : ι}

open scoped Classical in
/-- The infimum of times `t ∈ [t₀, t₁]` such that `f t ∈ A`, or `t₁` if there are none. -/
noncomputable def hittingBtwn (f : ι → E) (A : Set E) (t₀ t₁ : ι) : ι :=
  if ∃ t ∈ Icc t₀ t₁, f t ∈ A then sInf (Icc t₀ t₁ ∩ f ⁻¹' A) else t₁

open scoped Classical in
/-- The infimum of times `t ≥ t₀` such that `f t ∈ A`, or `⊤` if there are none. -/
noncomputable def hittingAfter (f : ι → E) (A : Set E) (t₀ : ι) : WithTop ι :=
  if ∃ t, t₀ ≤ t ∧ f t ∈ A then ↑(sInf {t | t₀ ≤ t ∧ f t ∈ A}) else ⊤

open scoped Classical in
lemma hittingBtwn_def (f : ι → E) (A : Set E) (t₀ t₁ : ι) :
    hittingBtwn f A t₀ t₁ = if ∃ t ∈ Icc t₀ t₁, f t ∈ A then
      sInf (Icc t₀ t₁ ∩ f ⁻¹' A) else t₁ := rfl

open scoped Classical in
lemma hittingAfter_def (f : ι → E) (A : Set E) (t₀ : ι) :
    hittingAfter f A t₀ = if ∃ t, t₀ ≤ t ∧ f t ∈ A then
      ↑(sInf {t | t₀ ≤ t ∧ f t ∈ A}) else ⊤ := rfl

@[simp]
lemma hittingBtwn_empty (f : ι → E) (t₀ t₁ : ι) : hittingBtwn f ∅ t₀ t₁ = t₁ := by
  simp [hittingBtwn_def]

@[simp]
lemma hittingAfter_empty (f : ι → E) (t₀ : ι) : hittingAfter f ∅ t₀ = ⊤ := by
  simp [hittingAfter_def]

lemma hittingBtwn_eq_sInf_of_exists (h : ∃ t ∈ Icc t₀ t₁, f t ∈ A) :
    hittingBtwn f A t₀ t₁ = sInf (Icc t₀ t₁ ∩ f ⁻¹' A) := by
  rw [hittingBtwn_def, ite_eq_left h]

lemma hittingAfter_eq_sInf_of_exists (h : ∃ t, t₀ ≤ t ∧ f t ∈ A) :
    hittingAfter f A t₀ = (sInf {t | t₀ ≤ t ∧ f t ∈ A} : ι) := by
  rw [hittingAfter_def, ite_eq_left h]

lemma hittingBtwn_eq_sInf_of_mem {t : ι} (ht₀ : t₀ ≤ t) (ht₁ : t ≤ t₁) (hA : f t ∈ A) :
    hittingBtwn f A t₀ t₁ = sInf (Icc t₀ t₁ ∩ f ⁻¹' A) :=
  hittingBtwn_eq_sInf_of_exists ⟨t, ⟨ht₀, ht₁⟩, hA⟩

lemma hittingAfter_eq_sInf_of_mem {t : ι} (ht : t₀ ≤ t) (hA : f t ∈ A) :
    hittingAfter f A t₀ = (sInf {t | t₀ ≤ t ∧ f t ∈ A} : ι) :=
  hittingAfter_eq_sInf_of_exists ⟨t, ht, hA⟩

lemma hittingBtwn_comp (f : ι → E) (g : E → F) (A : Set F) (t₀ t₁ : ι) :
    hittingBtwn (g ∘ f) A t₀ t₁ = hittingBtwn f (g ⁻¹' A) t₀ t₁ := rfl

lemma hittingAfter_comp (f : ι → E) (g : E → F) (A : Set F) (t₀ : ι) :
    hittingAfter (g ∘ f) A t₀ = hittingAfter f (g ⁻¹' A) t₀ := rfl

end Basic

section Inequalities

variable {f : ι → E} {A : Set E} {t₀ t₁ t : ι}

/-- This lemma is strictly weaker than `hittingBtwn_of_le`. -/
lemma hittingBtwn_of_lt [ConditionallyCompleteLattice ι]
    (h : t₁ < t₀) : hittingBtwn f A t₀ t₁ = t₁ := by
  simp [hittingBtwn_def, Icc_eq_empty_of_lt h]

lemma hittingBtwn_le [ConditionallyCompleteLattice ι]
    (f : ι → E) (A : Set E) (t₀ t₁ : ι) : hittingBtwn f A t₀ t₁ ≤ t₁ := by
  rw [hittingBtwn_def]
  split_ifs with h
  · obtain ⟨s, hs, hA⟩ := h
    exact (csInf_le bddBelow_Icc.inter_of_left ⟨hs, hA⟩).trans hs.2
  · exact le_rfl

lemma notMem_of_lt_hittingBtwn [ConditionallyCompleteLattice ι]
    (ht₀ : t₀ ≤ t) (ht : t < hittingBtwn f A t₀ t₁) : f t ∉ A := by
  intro hA
  have ht₁ := ht.le.trans (hittingBtwn_le f A t₀ t₁)
  rw [hittingBtwn_eq_sInf_of_mem ht₀ ht₁ hA] at ht
  exact ht.not_ge (csInf_le bddBelow_Icc.inter_of_left ⟨⟨ht₀, ht₁⟩, hA⟩)

lemma notMem_of_lt_hittingAfter [ConditionallyCompleteLattice ι]
    (ht₀ : t₀ ≤ t) (ht : t < hittingAfter f A t₀) : f t ∉ A := by
  intro hA
  apply ht.not_ge
  rw [hittingAfter_eq_sInf_of_mem ht₀ hA, WithTop.coe_le_coe]
  exact csInf_le ⟨t₀, fun _ hs ↦ hs.1⟩ ⟨ht₀, hA⟩

lemma hittingBtwn_eq_end_iff [Preorder ι] [InfSet ι] :
    hittingBtwn f A t₀ t₁ = t₁ ↔
      (∃ t ∈ Icc t₀ t₁, f t ∈ A) → sInf (Icc t₀ t₁ ∩ f ⁻¹' A) = t₁ := by
  classical
  rw [hittingBtwn_def, ite_eq_right_iff]

lemma hittingAfter_eq_top_iff [Preorder ι] [InfSet ι] :
    hittingAfter f A t₀ = ⊤ ↔ ∀ t, t₀ ≤ t → f t ∉ A := by
  simp [hittingAfter_def]

lemma le_hittingBtwn [ConditionallyCompleteLattice ι]
    (ht₁ : t ≤ t₁) (h : ∀ s ∈ Icc t₀ t₁, f s ∈ A → t ≤ s) : t ≤ hittingBtwn f A t₀ t₁ := by
  rw [hittingBtwn_def]
  split_ifs with h'
  · exact le_csInf h' fun s hs ↦ h s hs.1 hs.2
  · exact ht₁

lemma le_hittingAfter [ConditionallyCompleteLattice ι]
    {t : WithTop ι} (h : ∀ s, t₀ ≤ s → f s ∈ A → t ≤ s) :
    t ≤ hittingAfter f A t₀ := by
  rw [hittingAfter_def]
  split_ifs with h'
  · exact WithTop.le_coe_csInf h' fun s hs ↦ h s hs.1 hs.2
  · exact le_top

lemma hittingBtwn_of_le [ConditionallyCompleteLattice ι]
    (h : t₁ ≤ t₀) : hittingBtwn f A t₀ t₁ = t₁ :=
  le_antisymm (hittingBtwn_le f A t₀ t₁) (le_hittingBtwn le_rfl fun _ hs _ ↦ h.trans hs.1)

lemma start_le_hittingBtwn [ConditionallyCompleteLattice ι]
    (h : t₀ ≤ t₁) : t₀ ≤ hittingBtwn f A t₀ t₁ :=
  le_hittingBtwn h fun _ hs _ ↦ hs.1

lemma start_le_hittingAfter [ConditionallyCompleteLattice ι]
    (f : ι → E) (A : Set E) (t₀ : ι) : t₀ ≤ hittingAfter f A t₀ :=
  le_hittingAfter fun _ ht _ ↦ WithTop.coe_le_coe.mpr ht

lemma start_le_hittingBtwn_of_exists [ConditionallyCompleteLattice ι]
    (h : ∃ t ∈ Icc t₀ t₁, f t ∈ A) : t₀ ≤ hittingBtwn f A t₀ t₁ := by
  obtain ⟨_, ht, _⟩ := h
  exact start_le_hittingBtwn (ht.1.trans ht.2)

lemma hittingBtwn_mem_Icc [ConditionallyCompleteLattice ι]
    (h : t₀ ≤ t₁) : hittingBtwn f A t₀ t₁ ∈ Icc t₀ t₁ :=
  ⟨start_le_hittingBtwn h, hittingBtwn_le f A t₀ t₁⟩

lemma hittingBtwn_mem_set [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    (h : ∃ t ∈ Icc t₀ t₁, f t ∈ A) : f (hittingBtwn f A t₀ t₁) ∈ A := by
  have hs := csInf_mem (s := Icc t₀ t₁ ∩ f ⁻¹' A) h
  rw [hittingBtwn_eq_sInf_of_mem hs.1.1 hs.1.2 hs.2]
  exact hs.2

lemma hittingAfter_mem_set [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    (h : ∃ t, t₀ ≤ t ∧ f t ∈ A) : f (hittingAfter f A t₀).untopA ∈ A := by
  have hs := csInf_mem (s := {t | t₀ ≤ t ∧ f t ∈ A}) h
  rw [hittingAfter_eq_sInf_of_mem hs.1 hs.2]
  exact hs.2

lemma hittingBtwn_mem_set_of_hittingBtwn_lt [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    (h : hittingBtwn f A t₀ t₁ < t₁) : f (hittingBtwn f A t₀ t₁) ∈ A := by
  by_cases hvisit : ∃ s ∈ Icc t₀ t₁, f s ∈ A
  · exact hittingBtwn_mem_set hvisit
  · rw [hittingBtwn_def, ite_eq_right hvisit] at h
    simp at h

lemma hittingAfter_mem_set_of_ne_top [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    (h : hittingAfter f A t₀ ≠ ⊤) : f (hittingAfter f A t₀).untopA ∈ A := by
  simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at h
  obtain ⟨t, ht, hA⟩ := h
  exact hittingAfter_mem_set ⟨t, ht, hA⟩

lemma hittingBtwn_le_of_mem [ConditionallyCompleteLattice ι]
    (ht₀ : t₀ ≤ t) (ht₁ : t ≤ t₁) (hA : f t ∈ A) : hittingBtwn f A t₀ t₁ ≤ t := by
  rw [hittingBtwn_eq_sInf_of_mem ht₀ ht₁ hA]
  exact csInf_le bddBelow_Icc.inter_of_left ⟨⟨ht₀, ht₁⟩, hA⟩

lemma hittingAfter_le_of_mem [ConditionallyCompleteLattice ι]
    (ht : t₀ ≤ t) (hA : f t ∈ A) : hittingAfter f A t₀ ≤ t := by
  rw [hittingAfter_eq_sInf_of_mem ht hA, WithTop.coe_le_coe]
  exact csInf_le ⟨t₀, fun _ hs ↦ hs.1⟩ ⟨ht, hA⟩

lemma le_hittingBtwn_iff [ConditionallyCompleteLattice ι] :
    t ≤ hittingBtwn f A t₀ t₁ ↔ t ≤ t₁ ∧ ∀ s ∈ Icc t₀ t₁, f s ∈ A → t ≤ s := by
  refine ⟨?_, fun h ↦ le_hittingBtwn h.1 h.2⟩
  intro h
  refine ⟨h.trans (hittingBtwn_le f A t₀ t₁), ?_⟩
  intro s hs hA
  exact h.trans (hittingBtwn_le_of_mem hs.1 hs.2 hA)

lemma le_hittingAfter_iff [ConditionallyCompleteLattice ι] {t : WithTop ι} :
    t ≤ hittingAfter f A t₀ ↔ ∀ s, t₀ ≤ s → f s ∈ A → t ≤ s :=
  ⟨fun h _ hs hA ↦ h.trans (hittingAfter_le_of_mem hs hA), le_hittingAfter⟩

lemma hittingBtwn_eq_start [ConditionallyCompleteLattice ι]
    (h : t₀ ≤ t₁) (hA : f t₀ ∈ A) : hittingBtwn f A t₀ t₁ = t₀ :=
  le_antisymm (hittingBtwn_le_of_mem le_rfl h hA) (start_le_hittingBtwn h)

lemma hittingAfter_eq_start [ConditionallyCompleteLattice ι]
    (h : f t₀ ∈ A) : hittingAfter f A t₀ = t₀ :=
  le_antisymm (hittingAfter_le_of_mem le_rfl h) (start_le_hittingAfter f A t₀)

@[simp]
lemma hittingBtwn_univ [ConditionallyCompleteLinearOrder ι]
    (f : ι → E) (t₀ t₁ : ι) : hittingBtwn f univ t₀ t₁ = min t₀ t₁ := by
  rcases le_total t₀ t₁ with h | h
  · rw [hittingBtwn_eq_start h (mem_univ _), min_eq_left h]
  · rw [hittingBtwn_of_le h, min_eq_right h]

@[simp]
lemma hittingAfter_univ [ConditionallyCompleteLattice ι]
    (f : ι → E) (t₀ : ι) : hittingAfter f univ t₀ = t₀ :=
  hittingAfter_eq_start (mem_univ _)

lemma hittingBtwn_le_iff_of_exists [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    (hvisit : ∃ t ∈ Icc t₀ t₁, f t ∈ A) : hittingBtwn f A t₀ t₁ ≤ t ↔ ∃ s ∈ Icc t₀ t, f s ∈ A := by
  constructor
  · intro h
    exact ⟨_, ⟨start_le_hittingBtwn_of_exists hvisit, h⟩, hittingBtwn_mem_set hvisit⟩
  · rintro ⟨s, hs, hA⟩
    rcases le_total s t₁ with hst | hst
    · exact (hittingBtwn_le_of_mem hs.1 hst hA).trans hs.2
    · exact (hittingBtwn_le f A t₀ t₁).trans (hst.trans hs.2)

lemma hittingAfter_le_iff [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι] :
    hittingAfter f A t₀ ≤ t ↔ ∃ s ∈ Icc t₀ t, f s ∈ A := by
  constructor
  · intro h
    by_cases hvisit : ∃ s, t₀ ≤ s ∧ f s ∈ A
    · have hs := csInf_mem (s := {s | t₀ ≤ s ∧ f s ∈ A}) hvisit
      rw [hittingAfter_eq_sInf_of_mem hs.1 hs.2, WithTop.coe_le_coe] at h
      exact ⟨_, ⟨hs.1, h⟩, hs.2⟩
    · simp [hittingAfter_def, hvisit] at h
  · rintro ⟨s, ⟨hs₀, hst⟩, hsA⟩
    exact (hittingAfter_le_of_mem hs₀ hsA).trans (WithTop.coe_le_coe.mpr hst)

lemma hittingBtwn_le_iff_of_lt [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    (ht : t < t₁) : hittingBtwn f A t₀ t₁ ≤ t ↔ ∃ s ∈ Icc t₀ t, f s ∈ A := by
  by_cases hvisit : ∃ s ∈ Icc t₀ t₁, f s ∈ A
  · exact hittingBtwn_le_iff_of_exists hvisit
  · simp only [hittingBtwn_def, ite_eq_right hvisit, not_le.mpr ht, false_iff]
    rintro ⟨s, hs, hA⟩
    exact hvisit ⟨s, ⟨hs.1, hs.2.trans ht.le⟩, hA⟩

lemma hittingBtwn_lt_iff [ConditionallyCompleteLinearOrder ι] (ht : t ≤ t₁) :
    hittingBtwn f A t₀ t₁ < t ↔ ∃ s ∈ Ico t₀ t, f s ∈ A := by
  rw [lt_iff_not_ge, le_hittingBtwn_iff, and_iff_right ht]
  grind

lemma hittingAfter_lt_iff [ConditionallyCompleteLinearOrder ι] :
    hittingAfter f A t₀ < t ↔ ∃ s ∈ Ico t₀ t, f s ∈ A := by
  rw [lt_iff_not_ge, le_hittingAfter_iff]
  simp only [not_forall, not_le, exists_prop, WithTop.coe_lt_coe, mem_Ico]
  grind

lemma hittingBtwn_eq_hittingBtwn_of_exists [ConditionallyCompleteLinearOrder ι] {t₂ : ι}
    (h : t₁ ≤ t₂) (hvisit : ∃ t ∈ Icc t₀ t₁, f t ∈ A) :
    hittingBtwn f A t₀ t₁ = hittingBtwn f A t₀ t₂ := by
  apply le_antisymm
  · refine le_hittingBtwn ((hittingBtwn_le f A t₀ t₁).trans h) fun s hs hA ↦ ?_
    rcases le_total s t₁ with hst | hst
    · exact hittingBtwn_le_of_mem hs.1 hst hA
    · exact (hittingBtwn_le f A t₀ t₁).trans hst
  · obtain ⟨s, hs, hA⟩ := hvisit
    apply le_hittingBtwn ((hittingBtwn_le_of_mem hs.1 (hs.2.trans h) hA).trans hs.2)
    exact fun _ ht hA ↦ hittingBtwn_le_of_mem ht.1 (ht.2.trans h) hA

lemma hittingBtwn_set_antitone [ConditionallyCompleteLattice ι] (f : ι → E) (t₀ t₁ : ι) :
    Antitone (fun A ↦ hittingBtwn f A t₀ t₁) := by
  intro A B hAB
  apply le_hittingBtwn (hittingBtwn_le f B t₀ t₁)
  exact fun _ ht hA ↦ hittingBtwn_le_of_mem ht.1 ht.2 (hAB hA)

lemma hittingAfter_set_antitone [ConditionallyCompleteLattice ι] (f : ι → E) (t₀ : ι) :
    Antitone (fun A ↦ hittingAfter f A t₀) := by
  intro A B hAB
  exact le_hittingAfter fun _ ht hA ↦ hittingAfter_le_of_mem ht (hAB hA)

lemma hittingBtwn_end_monotone [ConditionallyCompleteLinearOrder ι]
    (f : ι → E) (A : Set E) (t₀ : ι) : Monotone (fun t₁ ↦ hittingBtwn f A t₀ t₁) := by
  intro t₁ t₂ h
  refine le_hittingBtwn ((hittingBtwn_le f A t₀ t₁).trans h) fun s hs hA ↦ ?_
  rcases le_total s t₁ with hst | hst
  · exact hittingBtwn_le_of_mem hs.1 hst hA
  · exact (hittingBtwn_le f A t₀ t₁).trans hst

lemma hittingBtwn_start_monotone [ConditionallyCompleteLattice ι] (f : ι → E) (A : Set E) (t₁ : ι) :
    Monotone (fun t₀ ↦ hittingBtwn f A t₀ t₁) := by
  intro t₀ t₀' h
  apply le_hittingBtwn (hittingBtwn_le f A t₀ t₁)
  exact fun _ ht hA ↦ hittingBtwn_le_of_mem (h.trans ht.1) ht.2 hA

lemma hittingAfter_start_monotone [ConditionallyCompleteLattice ι] (f : ι → E) (A : Set E) :
    Monotone (fun t₀ ↦ hittingAfter f A t₀) := by
  intro t₀ t₀' h
  exact le_hittingAfter fun _ ht hA ↦ hittingAfter_le_of_mem (h.trans ht) hA

end Inequalities

lemma hittingBtwn_bot_top [CompleteLattice ι] {f : ι → E} {A : Set E} :
    hittingBtwn f A ⊥ ⊤ = sInf (f ⁻¹' A) := by
  simp only [hittingBtwn_def, Icc_bot, Iic_top, univ_inter, mem_univ, true_and]
  split_ifs with h
  · rfl
  · have hA : f ⁻¹' A = ∅ := by ext t; simp_all
    simp [hA]

open scoped Classical in
lemma hittingAfter_bot [Preorder ι] [OrderBot ι] [InfSet ι] {f : ι → E} {A : Set E} :
    hittingAfter f A ⊥ = if ∃ t, f t ∈ A then ↑(sInf (f ⁻¹' A)) else ⊤ := by
  simp [hittingAfter_def]
  congr

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
    {f : ι → E} {A : Set E} {t₁ t : ι}

lemma hittingBtwn_bot_le_iff (h : ∃ s ≤ t₁, f s ∈ A) :
    hittingBtwn f A ⊥ t₁ ≤ t ↔ ∃ s ≤ t, f s ∈ A := by
  simp [hittingBtwn_le_iff_of_exists, h]

lemma hittingAfter_bot_le_iff : hittingAfter f A ⊥ ≤ t ↔ ∃ s ≤ t, f s ∈ A := by
  simp [hittingAfter_le_iff]

end ConditionallyCompleteLinearOrderBot

end Function

/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Order.SuccPred.Limit

/-!

# Relation between `IsSuccPrelimit` and `iSup` in (conditionally) complete linear orders.

-/

open Order Set

variable {ι α : Type*}

section ConditionallyCompleteLinearOrder
variable [ConditionallyCompleteLinearOrder α] [Nonempty ι] {f : ι → α} {s : Set α} {x : α}

lemma csSup_mem_of_not_isSuccPrelimit
    (hne : s.Nonempty) (hbdd : BddAbove s) (hlim : ¬ IsSuccPrelimit (sSup s)) : sSup s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := exists_lt_of_lt_csSup hne hy.lt
  exact eq_of_le_of_not_lt (le_csSup hbdd his) (hy.2 hi) ▸ his

@[deprecated csSup_mem_of_not_isSuccPrelimit (since := "2024-09-05")]
alias csSup_mem_of_not_isSuccLimit := csSup_mem_of_not_isSuccPrelimit

lemma csInf_mem_of_not_isPredPrelimit
    (hne : s.Nonempty) (hbdd : BddBelow s) (hlim : ¬ IsPredPrelimit (sInf s)) : sInf s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := exists_lt_of_csInf_lt hne hy.lt
  exact eq_of_le_of_not_lt (csInf_le hbdd his) (hy.2 · hi) ▸ his

@[deprecated csInf_mem_of_not_isPredPrelimit (since := "2024-09-05")]
alias csInf_mem_of_not_isPredLimit := csInf_mem_of_not_isPredPrelimit

lemma exists_eq_ciSup_of_not_isSuccPrelimit
    (hf : BddAbove (range f)) (hf' : ¬ IsSuccPrelimit (⨆ i, f i)) : ∃ i, f i = ⨆ i, f i :=
  csSup_mem_of_not_isSuccPrelimit (range_nonempty f) hf hf'

@[deprecated exists_eq_ciSup_of_not_isSuccPrelimit (since := "2024-09-05")]
alias exists_eq_ciSup_of_not_isSuccLimit := exists_eq_ciSup_of_not_isSuccPrelimit

lemma exists_eq_ciInf_of_not_isPredPrelimit
    (hf : BddBelow (range f)) (hf' : ¬ IsPredPrelimit (⨅ i, f i)) : ∃ i, f i = ⨅ i, f i :=
  csInf_mem_of_not_isPredPrelimit (range_nonempty f) hf hf'

@[deprecated exists_eq_ciInf_of_not_isPredPrelimit (since := "2024-09-05")]
alias exists_eq_ciInf_of_not_isPredLimit := exists_eq_ciInf_of_not_isPredPrelimit

lemma IsLUB.mem_of_nonempty_of_not_isSuccPrelimit
    (hs : IsLUB s x) (hne : s.Nonempty) (hx : ¬ IsSuccPrelimit x) : x ∈ s :=
  hs.csSup_eq hne ▸ csSup_mem_of_not_isSuccPrelimit hne hs.bddAbove (hs.csSup_eq hne ▸ hx)

@[deprecated IsLUB.mem_of_nonempty_of_not_isSuccPrelimit (since := "2024-09-05")]
alias IsLUB.mem_of_nonempty_of_not_isSuccLimit := IsLUB.mem_of_nonempty_of_not_isSuccPrelimit

lemma IsGLB.mem_of_nonempty_of_not_isPredPrelimit
    (hs : IsGLB s x) (hne : s.Nonempty) (hx : ¬ IsPredPrelimit x) : x ∈ s :=
  hs.csInf_eq hne ▸ csInf_mem_of_not_isPredPrelimit hne hs.bddBelow (hs.csInf_eq hne ▸ hx)

@[deprecated IsGLB.mem_of_nonempty_of_not_isPredPrelimit (since := "2024-09-05")]
alias IsGLB.mem_of_nonempty_of_not_isPredLimit := IsGLB.mem_of_nonempty_of_not_isPredPrelimit

lemma IsLUB.exists_of_nonempty_of_not_isSuccPrelimit
    (hf : IsLUB (range f) x) (hx : ¬ IsSuccPrelimit x) : ∃ i, f i = x :=
  hf.mem_of_nonempty_of_not_isSuccPrelimit (range_nonempty f) hx

@[deprecated IsLUB.exists_of_nonempty_of_not_isSuccPrelimit (since := "2024-09-05")]
alias IsLUB.exists_of_nonempty_of_not_isSuccLimit := IsLUB.exists_of_nonempty_of_not_isSuccPrelimit

lemma IsGLB.exists_of_nonempty_of_not_isPredPrelimit
    (hf : IsGLB (range f) x) (hx : ¬ IsPredPrelimit x) : ∃ i, f i = x :=
  hf.mem_of_nonempty_of_not_isPredPrelimit (range_nonempty f) hx

@[deprecated IsGLB.exists_of_nonempty_of_not_isPredPrelimit (since := "2024-09-05")]
alias IsGLB.exists_of_nonempty_of_not_isPredLimit := IsGLB.exists_of_nonempty_of_not_isPredPrelimit

open Classical in
/-- Every conditionally complete linear order with well-founded `<` is a successor order, by setting
the successor of an element to be the infimum of all larger elements. -/
noncomputable def ConditionallyCompleteLinearOrder.toSuccOrder [WellFoundedLT α] :
    SuccOrder α where
  succ a := if IsMax a then a else sInf {b | a < b}
  le_succ a := by
    by_cases h : IsMax a
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [not_isMax_iff] at h
      exact le_csInf h (fun b => le_of_lt)
  max_of_succ_le hs := by
    by_contra h
    simp [h] at hs
    rw [not_isMax_iff] at h
    exact hs.not_lt (csInf_mem h)
  succ_le_of_lt {a b} ha := by
    simp [ha.not_isMax]
    exact csInf_le ⟨a, fun _ hc => hc.le⟩ ha

end ConditionallyCompleteLinearOrder

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α] {f : ι → α} {s : Set α} {x : α}

/-- See `csSup_mem_of_not_isSuccPrelimit` for the `ConditionallyCompleteLinearOrder` version. -/
lemma csSup_mem_of_not_isSuccPrelimit'
    (hbdd : BddAbove s) (hlim : ¬ IsSuccPrelimit (sSup s)) : sSup s ∈ s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [isSuccPrelimit_bot] at hlim
  · exact csSup_mem_of_not_isSuccPrelimit hs hbdd hlim

@[deprecated csSup_mem_of_not_isSuccPrelimit' (since := "2024-09-05")]
alias csSup_mem_of_not_isSuccLimit' := csSup_mem_of_not_isSuccPrelimit'

/-- See `exists_eq_ciSup_of_not_isSuccPrelimit` for the
`ConditionallyCompleteLinearOrder` version. -/
lemma exists_eq_ciSup_of_not_isSuccPrelimit'
    (hf : BddAbove (range f)) (hf' : ¬ IsSuccPrelimit (⨆ i, f i)) : ∃ i, f i = ⨆ i, f i :=
  csSup_mem_of_not_isSuccPrelimit' hf hf'

@[deprecated exists_eq_ciSup_of_not_isSuccPrelimit' (since := "2024-09-05")]
alias exists_eq_ciSup_of_not_isSuccLimit' := exists_eq_ciSup_of_not_isSuccPrelimit'

lemma IsLUB.mem_of_not_isSuccPrelimit (hs : IsLUB s x) (hx : ¬ IsSuccPrelimit x) : x ∈ s := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp [show x = ⊥ by simpa using hs, isSuccPrelimit_bot] at hx
  · exact hs.mem_of_nonempty_of_not_isSuccPrelimit hs' hx

@[deprecated IsLUB.mem_of_not_isSuccPrelimit (since := "2024-09-05")]
alias IsLUB.mem_of_not_isSuccLimit := IsLUB.mem_of_not_isSuccPrelimit

lemma IsLUB.exists_of_not_isSuccPrelimit (hf : IsLUB (range f) x) (hx : ¬ IsSuccPrelimit x) :
    ∃ i, f i = x :=
  hf.mem_of_not_isSuccPrelimit hx

@[deprecated IsLUB.exists_of_not_isSuccPrelimit (since := "2024-09-05")]
alias IsLUB.exists_of_not_isSuccLimit := IsLUB.exists_of_not_isSuccPrelimit

theorem Order.IsSuccPrelimit.sSup_Iio (h : IsSuccPrelimit x) : sSup (Iio x) = x := by
  obtain rfl | hx := eq_bot_or_bot_lt x
  · simp
  · refine (csSup_le ⟨⊥, hx⟩ fun a ha ↦ ha.le).antisymm <| le_of_forall_lt fun a ha ↦ ?_
    rw [lt_csSup_iff' bddAbove_Iio]
    obtain ⟨b, hb', hb⟩ := (not_covBy_iff ha).1 (h a)
    use b, hb

theorem Order.IsSuccPrelimit.iSup_Iio (h : IsSuccPrelimit x) : ⨆ a : Iio x, a.1 = x := by
  rw [← sSup_eq_iSup', h.sSup_Iio]

theorem Order.IsSuccLimit.sSup_Iio (h : IsSuccLimit x) : sSup (Iio x) = x :=
  h.isSuccPrelimit.sSup_Iio

theorem Order.IsSuccLimit.iSup_Iio (h : IsSuccLimit x) : ⨆ a : Iio x, a.1 = x :=
  h.isSuccPrelimit.iSup_Iio

theorem sSup_Iio_eq_self_iff_isSuccPrelimit : sSup (Iio x) = x ↔ IsSuccPrelimit x := by
  refine ⟨fun h ↦ ?_, IsSuccPrelimit.sSup_Iio⟩
  by_contra hx
  rw [← h] at hx
  simpa [h] using csSup_mem_of_not_isSuccPrelimit' bddAbove_Iio hx

theorem iSup_Iio_eq_self_iff_isSuccPrelimit : ⨆ a : Iio x, a.1 = x ↔ IsSuccPrelimit x := by
  rw [← sSup_eq_iSup', sSup_Iio_eq_self_iff_isSuccPrelimit]

end ConditionallyCompleteLinearOrderBot

section CompleteLinearOrder
variable [CompleteLinearOrder α] {s : Set α} {f : ι → α} {x : α}

lemma sSup_mem_of_not_isSuccPrelimit (hlim : ¬ IsSuccPrelimit (sSup s)) : sSup s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := lt_sSup_iff.mp hy.lt
  exact eq_of_le_of_not_lt (le_sSup his) (hy.2 hi) ▸ his

@[deprecated sSup_mem_of_not_isSuccPrelimit (since := "2024-09-05")]
alias sSup_mem_of_not_isSuccLimit := sSup_mem_of_not_isSuccPrelimit

lemma sInf_mem_of_not_isPredPrelimit (hlim : ¬ IsPredPrelimit (sInf s)) : sInf s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := sInf_lt_iff.mp hy.lt
  exact eq_of_le_of_not_lt (sInf_le his) (hy.2 · hi) ▸ his

@[deprecated sInf_mem_of_not_isPredPrelimit (since := "2024-09-05")]
alias sInf_mem_of_not_isPredLimit := sInf_mem_of_not_isPredPrelimit

lemma exists_eq_iSup_of_not_isSuccPrelimit (hf : ¬ IsSuccPrelimit (⨆ i, f i)) :
    ∃ i, f i = ⨆ i, f i :=
  sSup_mem_of_not_isSuccPrelimit hf

@[deprecated exists_eq_iSup_of_not_isSuccPrelimit (since := "2024-09-05")]
alias exists_eq_iSup_of_not_isSuccLimit := exists_eq_iSup_of_not_isSuccPrelimit

lemma exists_eq_iInf_of_not_isPredPrelimit (hf : ¬ IsPredPrelimit (⨅ i, f i)) :
    ∃ i, f i = ⨅ i, f i :=
  sInf_mem_of_not_isPredPrelimit hf

@[deprecated exists_eq_iInf_of_not_isPredPrelimit (since := "2024-09-05")]
alias exists_eq_iInf_of_not_isPredLimit := exists_eq_iInf_of_not_isPredPrelimit

lemma IsGLB.mem_of_not_isPredPrelimit (hs : IsGLB s x) (hx : ¬ IsPredPrelimit x) : x ∈ s :=
  hs.sInf_eq ▸ sInf_mem_of_not_isPredPrelimit (hs.sInf_eq ▸ hx)

@[deprecated IsGLB.mem_of_not_isPredPrelimit (since := "2024-09-05")]
alias IsGLB.mem_of_not_isPredLimit := IsGLB.mem_of_not_isPredPrelimit

lemma IsGLB.exists_of_not_isPredPrelimit (hf : IsGLB (range f) x) (hx : ¬ IsPredPrelimit x) :
    ∃ i, f i = x :=
  hf.mem_of_not_isPredPrelimit hx

@[deprecated IsGLB.exists_of_not_isPredPrelimit (since := "2024-09-05")]
alias IsGLB.exists_of_not_isPredLimit := IsGLB.exists_of_not_isPredPrelimit

end CompleteLinearOrder

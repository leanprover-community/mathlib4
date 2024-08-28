/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Order.SuccPred.Limit
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!

# Relation between `IsSuccLimit` and `iSup` in (conditionally) complete linear orders.

-/

open Order

variable {ι α : Type*}

section ConditionallyCompleteLinearOrder
variable [ConditionallyCompleteLinearOrder α] [Nonempty ι] {f : ι → α} {s : Set α} {x : α}

lemma csSup_mem_of_not_isSuccLimit
    (hne : s.Nonempty) (hbdd : BddAbove s) (hlim : ¬ IsSuccLimit (sSup s)) :
    sSup s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := exists_lt_of_lt_csSup hne hy.lt
  exact eq_of_le_of_not_lt (le_csSup hbdd his) (hy.2 hi) ▸ his

lemma csInf_mem_of_not_isPredLimit
    (hne : s.Nonempty) (hbdd : BddBelow s) (hlim : ¬ IsPredLimit (sInf s)) :
    sInf s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := exists_lt_of_csInf_lt hne hy.lt
  exact eq_of_le_of_not_lt (csInf_le hbdd his) (hy.2 · hi) ▸ his

lemma exists_eq_ciSup_of_not_isSuccLimit
    (hf : BddAbove (Set.range f)) (hf' : ¬ IsSuccLimit (⨆ i, f i)) :
    ∃ i, f i = ⨆ i, f i :=
  csSup_mem_of_not_isSuccLimit (Set.range_nonempty f) hf hf'

lemma exists_eq_ciInf_of_not_isPredLimit
    (hf : BddBelow (Set.range f)) (hf' : ¬ IsPredLimit (⨅ i, f i)) :
    ∃ i, f i = ⨅ i, f i :=
  csInf_mem_of_not_isPredLimit (Set.range_nonempty f) hf hf'

lemma IsLUB.mem_of_nonempty_of_not_isSuccLimit
    (hs : IsLUB s x) (hne : s.Nonempty) (hx : ¬ IsSuccLimit x) : x ∈ s :=
  hs.csSup_eq hne ▸ csSup_mem_of_not_isSuccLimit hne hs.bddAbove (hs.csSup_eq hne ▸ hx)

lemma IsGLB.mem_of_nonempty_of_not_isPredLimit
    (hs : IsGLB s x) (hne : s.Nonempty) (hx : ¬ IsPredLimit x) : x ∈ s :=
  hs.csInf_eq hne ▸ csInf_mem_of_not_isPredLimit hne hs.bddBelow (hs.csInf_eq hne ▸ hx)

lemma IsLUB.exists_of_nonempty_of_not_isSuccLimit
    (hf : IsLUB (Set.range f) x) (hx : ¬ IsSuccLimit x) :
    ∃ i, f i = x := hf.mem_of_nonempty_of_not_isSuccLimit (Set.range_nonempty f) hx

lemma IsGLB.exists_of_nonempty_of_not_isPredLimit
    (hf : IsGLB (Set.range f) x) (hx : ¬ IsPredLimit x) :
    ∃ i, f i = x := hf.mem_of_nonempty_of_not_isPredLimit (Set.range_nonempty f) hx

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

/-- See `csSup_mem_of_not_isSuccLimit` for the `ConditionallyCompleteLinearOrder` version. -/
lemma csSup_mem_of_not_isSuccLimit'
    (hbdd : BddAbove s) (hlim : ¬ IsSuccLimit (sSup s)) :
    sSup s ∈ s := by
  obtain (rfl|hs) := s.eq_empty_or_nonempty
  · simp [isSuccLimit_bot] at hlim
  · exact csSup_mem_of_not_isSuccLimit hs hbdd hlim

/-- See `exists_eq_ciSup_of_not_isSuccLimit` for the
`ConditionallyCompleteLinearOrder` version. -/
lemma exists_eq_ciSup_of_not_isSuccLimit'
    (hf : BddAbove (Set.range f)) (hf' : ¬ IsSuccLimit (⨆ i, f i)) :
    ∃ i, f i = ⨆ i, f i :=
  csSup_mem_of_not_isSuccLimit' hf hf'

lemma IsLUB.mem_of_not_isSuccLimit (hs : IsLUB s x) (hx : ¬ IsSuccLimit x) :
    x ∈ s := by
  obtain (rfl|hs') := s.eq_empty_or_nonempty
  · simp [show x = ⊥ by simpa using hs, isSuccLimit_bot] at hx
  · exact hs.mem_of_nonempty_of_not_isSuccLimit hs' hx

lemma IsLUB.exists_of_not_isSuccLimit (hf : IsLUB (Set.range f) x) (hx : ¬ IsSuccLimit x) :
    ∃ i, f i = x := hf.mem_of_not_isSuccLimit hx

end ConditionallyCompleteLinearOrderBot

section CompleteLinearOrder
variable [CompleteLinearOrder α] {s : Set α} {f : ι → α} {x : α}

lemma sSup_mem_of_not_isSuccLimit (hlim : ¬ IsSuccLimit (sSup s)) :
    sSup s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := lt_sSup_iff.mp hy.lt
  exact eq_of_le_of_not_lt (le_sSup his) (hy.2 hi) ▸ his

lemma sInf_mem_of_not_isPredLimit (hlim : ¬ IsPredLimit (sInf s)) :
    sInf s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := sInf_lt_iff.mp hy.lt
  exact eq_of_le_of_not_lt (sInf_le his) (hy.2 · hi) ▸ his

lemma exists_eq_iSup_of_not_isSuccLimit (hf : ¬ IsSuccLimit (⨆ i, f i)) :
    ∃ i, f i = ⨆ i, f i :=
  sSup_mem_of_not_isSuccLimit hf

lemma exists_eq_iInf_of_not_isPredLimit (hf : ¬ IsPredLimit (⨅ i, f i)) :
    ∃ i, f i = ⨅ i, f i :=
  sInf_mem_of_not_isPredLimit hf

lemma IsGLB.mem_of_not_isPredLimit (hs : IsGLB s x) (hx : ¬ IsPredLimit x) :
    x ∈ s :=
  hs.sInf_eq ▸ sInf_mem_of_not_isPredLimit (hs.sInf_eq ▸ hx)

lemma IsGLB.exists_of_not_isPredLimit (hf : IsGLB (Set.range f) x) (hx : ¬ IsPredLimit x) :
    ∃ i, f i = x := hf.mem_of_not_isPredLimit hx

end CompleteLinearOrder

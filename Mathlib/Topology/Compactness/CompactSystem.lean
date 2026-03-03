/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.Data.Set.Dissipate
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact systems.

This file defines compact systems of sets.

## Main definitions

* `IsCompactSystem`: A set of sets is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.

## Main results

* `IsCompactSystemiff_isCompactSystem_of_or_univ`: A set system is a compact
system iff inserting `univ` gives a compact system.
* `IsClosedCompact.isCompactSystem`: The set of closed and compact sets is a compact system.
* `IsClosedCompact.isCompactSystem_of_T2Space`: In a `T2Space α`, the set of compact sets
  is a compact system in a `T2Space`.
-/

@[expose] public section

open Set Finset Nat

variable {α : Type*} {p : Set α → Prop} {C : ℕ → Set α}

section definition

/-- A set of sets is a compact system if, whenever a countable subfamily has empty intersection,
then finitely many of them already have empty intersection. -/
def IsCompactSystem (p : Set α → Prop) : Prop :=
  ∀ C : ℕ → Set α, (∀ i, p (C i)) → ⋂ i, C i = ∅ → ∃ (n : ℕ), dissipate C n = ∅

end definition

namespace IsCompactSystem

open Classical in
/-- In a compact system, given a countable family with `⋂ i, C i = ∅`, we choose the smallest `n`
with `⋂ (i ≤ n), C i = ∅`. -/
noncomputable
def finite_of_empty (hp : IsCompactSystem p) (hC : ∀ i, p (C i))
    (hC_empty : ⋂ i, C i = ∅) : ℕ :=
  Nat.find (hp C hC hC_empty)

open Classical in
lemma dissipate_eq_empty (hp : IsCompactSystem p) (hC : ∀ i, p (C i))
    (hC_empty : ⋂ i, C i = ∅) :
    dissipate C (hp.finite_of_empty hC hC_empty) = ∅ := by
  apply Nat.find_spec (hp C hC hC_empty)

lemma of_nonempty_iInter
    (h : ∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ n, (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) :
    IsCompactSystem p := by
  intro C hC
  contrapose!
  exact h C hC

lemma nonempty_iInter (hp : IsCompactSystem p) {C : ℕ → Set α} (hC : ∀ i, p (C i))
    (h_nonempty : ∀ n, (dissipate C n).Nonempty) :
    (⋂ i, C i).Nonempty := by
  revert h_nonempty
  contrapose!
  exact hp C hC

theorem iff_nonempty_iInter (p : Set α → Prop) :
    IsCompactSystem p ↔ (∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ (n : ℕ),
      (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) :=
  ⟨nonempty_iInter, of_nonempty_iInter⟩

@[simp]
lemma of_IsEmpty [IsEmpty α] (p : Set α → Prop) : IsCompactSystem p :=
  fun s _ _ ↦ ⟨0, Set.eq_empty_of_isEmpty (dissipate s 0)⟩

/-- Any subset of a compact system is a compact system. -/
theorem mono {C D : (Set α) → Prop} (hD : IsCompactSystem D) (hCD : ∀ s, C s → D s) :
  IsCompactSystem C := fun s hC hs ↦ hD s (fun i ↦ hCD (s i) (hC i)) hs

/-- In this equivalent formulation for a compact system,
note that we use `⋂ k < n, C k` rather than `⋂ k ≤ n, C k`. -/
lemma iff_nonempty_iInter_of_lt (p : Set α → Prop) :
    IsCompactSystem p ↔
      ∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ n, (⋂ k < n, C k).Nonempty) → (⋂ i, C i).Nonempty := by
  simp_rw [iff_nonempty_iInter]
  refine ⟨fun h C hi h'↦ h C hi (fun n ↦ dissipate_eq ▸ (h' (n + 1))), fun h C hi h' ↦ h C hi ?_⟩
  simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
  intro n g
  apply h' n
  simp_rw [← subset_empty_iff, dissipate] at g ⊢
  apply le_trans _ g
  intro x
  rw [mem_iInter₂, mem_iInter₂]
  exact fun h i hi ↦ h i hi.le

/-- A set system is a compact system iff adding `∅` gives a compact system. -/
lemma iff_isCompactSystem_of_or_empty :
    IsCompactSystem p ↔ IsCompactSystem (fun s ↦ (p s ∨ (s = ∅))) := by
  refine ⟨fun h s h' hd ↦ ?_, fun h ↦ mono h (fun s ↦ fun a ↦ (Or.inr a).symm)⟩
  by_cases g : ∃ n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact (dissipate_subset le_rfl).trans g.choose_spec.le
  · push_neg at g
    refine h s (fun i ↦ ?_) hd
    specialize g i
    specialize h' i
    rw [Set.nonempty_iff_ne_empty] at g
    simpa [g] using h'

/-- A set system is a compact system iff adding `univ` gives a compact system. -/
lemma iff_isCompactSystem_of_or_univ :
    IsCompactSystem p ↔ IsCompactSystem (fun s ↦ (p s ∨ s = univ)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ mono h (fun s ↦ fun a ↦ Or.symm (Or.inr a))⟩
  rcases isEmpty_or_nonempty α with hα | _
  · simp
  rw [iff_nonempty_iInter] at h ⊢
  intro s h' hd
  by_cases h₀ : ∀ n, ¬ p (s n)
  · simp only [h₀, false_or] at h'
    simp [h']
  push_neg at h₀
  classical
  let n := Nat.find h₀
  let s' := fun i ↦ if p (s i) then s i else s n
  have h₁ : ∀ i, p (s' i) := by simp [s']; grind
  have h₂ : ⋂ i, s i = ⋂ i, s' i := by ext; simp; grind
  apply h₂ ▸ h s' h₁
  by_contra! h_exists_empty
  obtain ⟨j, hj⟩ := h_exists_empty
  have h₃ (v : ℕ) (hv : n ≤ v) : dissipate s v = dissipate s' v:= by ext; simp; grind
  have h₇ : dissipate s' (max j n) = ∅ := by
    rw [← subset_empty_iff] at hj ⊢
    exact (antitone_dissipate (Nat.le_max_left j n)).trans hj
  specialize h₃ (max j n) (Nat.le_max_right j n)
  specialize hd (max j n)
  simp [h₃, h₇] at hd

theorem iff_directed (hpi : IsPiSystem {x |p x}) :
    IsCompactSystem p ↔
    ∀ (C : ℕ → Set α), (Directed (fun x1 x2 ↦ x1 ⊇ x2) C) → (∀ i, p (C i)) → ⋂ i, C i = ∅ →
      ∃ n, C n = ∅ := by
  rw [iff_isCompactSystem_of_or_empty]
  refine ⟨fun h ↦ fun C hdi hi ↦ ?_, fun h C h1 h2 ↦ ?_⟩
  · rw [exists_dissipate_eq_empty_iff_of_directed C hdi]
    exact h C (by simp [hi])
  · have hpi' : IsPiSystem {s | p s ∨ s = ∅} := by
      convert IsPiSystem.insert_empty hpi using 1
      ext
      simp
      grind
    rw [← biInter_le_eq_iInter] at h2
    obtain h' := h (dissipate C) directed_dissipate
    have h₀ (h₀ : ∀ n, p (dissipate C n) ∨ dissipate C n = ∅) (h₁ : ⋂ n, dissipate C n = ∅) :
        ∃ n, dissipate C n = ∅ := by
      by_cases! f : ∀ n, p (dissipate C n)
      · apply h' f h₁
      · obtain ⟨n, hn⟩ := f
        exact ⟨n, by simpa [hn] using h₀ n⟩
    obtain h'' := IsPiSystem.dissipate_mem hpi' h1
    have h₁ : ∀ n, p (dissipate C n) ∨ dissipate C n = ∅ := by
      intro n
      by_cases g : (dissipate C n).Nonempty
      · exact h'' n g
      · exact .inr (Set.not_nonempty_iff_eq_empty.mp g)
    apply h₀ h₁ h2

theorem iff_directed' (hpi : IsPiSystem p) :
    IsCompactSystem p ↔
    ∀ (C : ℕ → Set α), (Directed (fun x1 x2 ↦ x1 ⊇ x2) C) → (∀ i, p (C i)) → (∀ n, (C n).Nonempty) →
      (⋂ i, C i).Nonempty := by
  rw [IsCompactSystem.iff_directed hpi]
  refine ⟨fun h1 C h3 h4 ↦ ?_, fun h1 C h3 s ↦ ?_⟩ <;> rw [← not_imp_not] <;> push_neg
  · exact h1 C h3 h4
  · exact h1 C h3 s

section IsCompactIsClosed

variable (α : Type*) [TopologicalSpace α]

/-- The set of compact and closed sets is a compact system. -/
theorem of_isCompact_isClosed :
    IsCompactSystem (fun s : Set α ↦ IsCompact s ∧ IsClosed s) := by
  intro C hC_cc hC_inter
  by_contra! h_nonempty
  refine absurd hC_inter ?_
  rw [← ne_eq, ← Set.nonempty_iff_ne_empty, ← Set.iInter_dissipate]
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (Set.dissipate C)
    (fun n ↦ ?_) (fun n ↦ ?_) ?_ (fun n ↦ ?_)
  · exact Set.antitone_dissipate (by lia)
  · exact h_nonempty _
  · simp only [Set.dissipate_zero_nat]
    exact (hC_cc 0).1
  · induction n with
    | zero => simp only [Set.dissipate_zero_nat]; exact (hC_cc 0).2
    | succ n hn =>
      rw [Set.dissipate_succ]
      exact hn.inter (hC_cc (n + 1)).2

/-- In a `T2Space` the set of compact sets is a compact system. -/
theorem of_isCompact [T2Space α] :
    IsCompactSystem (fun s : Set α ↦ IsCompact s) := by
  convert of_isCompact_isClosed α with s
  exact ⟨fun hs ↦ ⟨hs, hs.isClosed⟩, fun hs ↦ hs.1⟩

/-- The set of sets which are either compact and closed, or `univ`, is a compact system. -/
theorem of_isCompact_isClosed_or_univ :
    IsCompactSystem (fun s : Set α ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ)) := by
  rw [← iff_isCompactSystem_of_or_univ]
  apply of_isCompact_isClosed

end IsCompactIsClosed

end IsCompactSystem

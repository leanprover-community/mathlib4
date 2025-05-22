/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Data.Set.Dissipate
import Mathlib.Topology.Separation.Hausdorff

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

theorem iff_nonempty_iInter (p : Set α → Prop) :
    IsCompactSystem p ↔ (∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ (n : ℕ),
      (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) := by
  refine ⟨fun h C hC hn ↦ ?_, fun h C hC ↦ ?_⟩ <;> have h2 := not_imp_not.mpr <| h C hC
  · push_neg at h2
    exact h2 hn
  · push_neg at h2
    exact h2

/-- In this equivalent formulation for a compact system,
note that we use `⋂ k < n, C k` rather than `⋂ k ≤ n, C k`. -/
lemma iff_nonempty_iInter_of_lt (p : Set α → Prop) : IsCompactSystem p ↔
    ∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ n, (⋂ k < n, C k).Nonempty) → (⋂ i, C i).Nonempty := by
  simp_rw [iff_nonempty_iInter]
  refine ⟨fun h C hi h'↦ ?_, fun h C hi h' ↦ ?_⟩
  · apply h C hi
    exact fun n ↦ dissipate_eq ▸ (h' (n + 1))
  · apply h C hi
    intro n
    simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
    intro g
    apply h' n
    simp_rw [← subset_empty_iff, dissipate] at g ⊢
    apply le_trans _ g
    intro x
    rw [mem_iInter₂, mem_iInter₂]
    exact fun h i hi ↦ h i hi.le

/-- Any subset of a compact system is a compact system. -/
theorem mono {C D : (Set α) → Prop} (hD : IsCompactSystem D) (hCD : ∀ s, C s → D s) :
  IsCompactSystem C := fun s hC hs ↦ hD s (fun i ↦ hCD (s i) (hC i)) hs

/-- A set system is a compact system iff adding `∅` gives a compact system. -/
lemma iff_isCompactSystem_of_or_empty : IsCompactSystem p ↔
    IsCompactSystem (fun s ↦ (p s ∨ (s = ∅))) := by
  refine ⟨fun h s h' hd ↦ ?_, fun h ↦ mono h (fun s ↦ fun a ↦ Or.symm (Or.inr a))⟩
  by_cases g : ∃ n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact le_trans (dissipate_subset (by rfl)) g.choose_spec.le
  · push_neg at g
    have hj (i : _) : p (s i) := by
      rcases h' i with a | b
      · exact a
      · exfalso
        revert g i
        simp_rw [← Set.not_nonempty_iff_eq_empty]
        simp_rw [imp_false, not_not]
        exact fun h i ↦ h i
    exact h s hj hd

lemma of_IsEmpty (h : IsEmpty α) (p : Set α → Prop) : IsCompactSystem p :=
  fun s _ _ ↦ ⟨0, Set.eq_empty_of_isEmpty (dissipate s 0)⟩

/-- A set system is a compact system iff adding `univ` gives a compact system. -/
lemma iff_isCompactSystem_of_or_univ : IsCompactSystem p ↔
    IsCompactSystem (fun s ↦ (p s ∨ s = univ)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ mono h (fun s ↦ fun a ↦ Or.symm (Or.inr a))⟩
  wlog ht : Nonempty α
  · rw [not_nonempty_iff] at ht
    apply of_IsEmpty ht
  · rw [iff_nonempty_iInter] at h ⊢
    intro s h' hd
    classical
    by_cases h₀ : ∀ n, ¬p (s n)
    · simp only [h₀, false_or] at h'
      simp_rw [h', iInter_univ, Set.univ_nonempty]
    · push_neg at h₀
      let n := Nat.find h₀
      let s' := fun i ↦ if p (s i) then s i else s n
      have h₁ : ∀ i, p (s' i) := by
        intro i
        by_cases h₁ : p (s i)
        · simp only [h₁, ↓reduceIte, s']
        · simp only [h₁, ↓reduceIte, Nat.find_spec h₀, s', n]
      have h₃ : ∀ i, (p (s i) → s' i = s i) := fun i h ↦ if_pos h
      have h₄ : ∀ i, (¬p (s i) → s' i = s n) := fun i h ↦ if_neg h
      have h₂ : ⋂ i, s i = ⋂ i, s' i := by
        simp only [s'] at *
        ext x
        simp only [mem_iInter]
        refine ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
        · by_cases h' : p (s i) <;> simp only [h', ↓reduceIte, h, n]
        · specialize h' i
          specialize h i
          rcases h' with a | b
          · simp only [a, ↓reduceIte] at h
            exact h
          · simp only [b, Set.mem_univ]
      apply h₂ ▸ h s' h₁
      by_contra! a
      obtain ⟨j, hj⟩ := a
      have h₂ (v : ℕ) (hv : n ≤ v) : dissipate s v = dissipate s' v:= by
        ext x
        refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> simp only [dissipate_def, mem_iInter] at h ⊢ <;>
          intro i hi
        · by_cases h₅ : p (s i)
          · exact (h₃ i h₅) ▸ h i hi
          · exact (h₄ i h₅) ▸ h n hv
        · by_cases h₅ : p (s i)
          · exact (h₃ i h₅) ▸ h i hi
          · have h₆ : s i = univ := by
              specialize h' i
              simp only [h₅, false_or] at h'
              exact h'
            simp only [h₆, Set.mem_univ]
      have h₇ : dissipate s' (max j n) = ∅ := by
        rw [← subset_empty_iff] at hj ⊢
        exact le_trans (antitone_dissipate (Nat.le_max_left j n)) hj
      specialize h₂ (max j n) (Nat.le_max_right j n)
      specialize hd (max j n)
      rw [h₂, Set.nonempty_iff_ne_empty, h₇] at hd
      exact hd rfl

theorem iff_directed (hpi : IsPiSystem p) :
    IsCompactSystem p ↔
    ∀ (C : ℕ → Set α), ∀ (_ : Directed (fun (x1 x2 : Set α) => x1 ⊇ x2) C), (∀ i, p (C i)) →
      ⋂ i, C i = ∅ → ∃ (n : ℕ), C n = ∅ := by
  rw [iff_isCompactSystem_of_or_empty]
  refine ⟨fun h ↦ fun C hdi hi ↦ ?_, fun h C h1 h2 ↦ ?_⟩
  · rw [exists_dissipate_eq_empty_iff_of_directed C hdi]
    apply h C
    exact fun i ↦ Or.inl (hi i)
  · have hpi' : IsPiSystem (fun s ↦ p s ∨ s = ∅) := by
      intro a ha b hb hab
      rcases ha with ha₁ | ha₂
      · rcases hb with hb₁ | hb₂
        · left
          exact hpi a ha₁ b hb₁ hab
        · right
          exact hb₂ ▸ (Set.inter_empty a)
      · simp only [ha₂, Set.empty_inter]
        right
        rfl
    rw [← biInter_le_eq_iInter] at h2
    obtain h' := h (dissipate C) directed_dissipate
    have h₀ : (∀ (n : ℕ), p (dissipate C n) ∨ dissipate C n = ∅) → ⋂ n, dissipate C n = ∅ →
      ∃ n, dissipate C n = ∅ := by
      intro h₀ h₁
      by_cases f : ∀ n, p (dissipate C n)
      · apply h' f h₁
      · push_neg at f
        obtain ⟨n, hn⟩ := f
        use n
        specialize h₀ n
        simp_all only [false_or]
    obtain h'' := IsPiSystem.dissipate_mem hpi' h1
    have h₁ :  ∀ (n : ℕ), p (dissipate C n) ∨ dissipate C n = ∅ := by
      intro n
      by_cases g : (dissipate C n).Nonempty
      · exact h'' n g
      · right
        exact Set.not_nonempty_iff_eq_empty.mp g
    apply h₀ h₁ h2


theorem iff_directed' (hpi : IsPiSystem p) :
    IsCompactSystem p ↔
    ∀ (C : ℕ → Set α), ∀ (_ : Directed (fun (x1 x2 : Set α) => x1 ⊇ x2) C), (∀ i, p (C i)) →
    (∀ (n : ℕ), (C n).Nonempty) → (⋂ i, C i).Nonempty  := by
  rw [IsCompactSystem.iff_directed hpi]
  refine ⟨fun h1 C h3 h4 ↦ ?_, fun h1 C h3 s ↦ ?_⟩ <;> rw [← not_imp_not] <;> push_neg
  · exact h1 C h3 h4
  · exact h1 C h3 s

section IsCompactIsClosed

variable (α : Type*) [TopologicalSpace α]

/-- The set of compact and closed sets is a compact system. -/
theorem of_isCompact_isClosed :
    IsCompactSystem (fun s : Set α ↦ IsCompact s ∧ IsClosed s) := by
  let p := fun (s : Set α) ↦ IsCompact s ∧ IsClosed s
  have h2 : IsPiSystem p := by
    intro s hs t ht _
    refine ⟨IsCompact.inter_left ht.1 hs.2, IsClosed.inter hs.2 ht.2⟩
  rw [IsCompactSystem.iff_directed' h2]
  intro s hs h1 h2
  let s' := fun (i : { j : ℕ | s j ≠ univ}) ↦ s i
  have hs' : Directed (fun x1 x2 ↦ x1 ⊇ x2) s' := by
    intro a b
    obtain ⟨z, hz1, hz2⟩ := hs a.val b.val
    have hz : s z ≠ univ := fun h ↦ a.prop <| eq_univ_of_subset hz1 h
    use ⟨z, hz⟩
  have htcl : ∀ (i : { j : ℕ | s j ≠ univ}), IsClosed (s i) :=
    fun i ↦ (h1 i).2
  have htco : ∀ (i : { j : ℕ | s j ≠ univ}), IsCompact (s i) :=
    fun i ↦ (h1 i).1
  haveI f : Nonempty α := by
    apply Exists.nonempty _
    · exact fun x ↦ x ∈ s 0
    · exact h2 0
  by_cases h : Nonempty ↑{j | s j ≠ Set.univ}
  · have g :  (⋂ i, s' i).Nonempty → (⋂ i, s i).Nonempty := by
      rw [Set.nonempty_iInter, Set.nonempty_iInter]
      rintro ⟨x, hx⟩
      use x
      intro i
      by_cases g : s i ≠ univ
      · exact hx ⟨i, g⟩
      · simp only [ne_eq, not_not] at g
        rw [g]
        simp only [Set.mem_univ]
    apply g <| IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed s' hs'
      (fun j ↦ h2 j) htco htcl
  · simp only [ne_eq, coe_setOf, nonempty_subtype, not_exists, not_not] at h
    simp [h]

/-- The set of sets which are either compact and closed, or `univ`, is a compact system. -/
theorem of_isCompact_isClosed_or_univ :
    IsCompactSystem (fun s : Set α ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ)) := by
  rw [← iff_isCompactSystem_of_or_univ]
  exact of_isCompact_isClosed

/-- In a `T2Space` the set of compact sets is a compact system. -/
theorem of_isCompact [T2Space α] :
    IsCompactSystem (fun s : Set α ↦ IsCompact s) := by
  have h : (fun s : Set α ↦ IsCompact s) = (fun s : Set α ↦ IsCompact s ∧ IsClosed s) := by
    ext s
    refine ⟨fun h' ↦ ⟨h', h'.isClosed⟩, fun h ↦ h.1⟩
  exact h ▸ (of_isCompact_isClosed)

end IsCompactIsClosed

end IsCompactSystem

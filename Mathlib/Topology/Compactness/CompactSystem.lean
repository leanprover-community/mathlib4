/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Data.Set.Dissipate
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.MeasureTheory.PiSystem

/-!
# Compact systems.

This files defines compact systems of sets.

## Main definitions

* `IsCompactSystem`: A set of sets is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.

## Main results

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
  ∀ C : ℕ → Set α, (∀ i, p (C i)) → ⋂ i, C i = ∅ → ∃ (n : ℕ), Dissipate C n = ∅

end definition

namespace IsCompactSystem

/-- In a compact system, given a countable family with empty intersection, we choose a finite
subfamily with empty intersection. -/
noncomputable
def max_of_empty (hp : IsCompactSystem p) (hC : ∀ i, p (C i))
    (hC_empty : ⋂ i, C i = ∅) : ℕ :=
  (hp C hC hC_empty).choose

lemma iInter_eq_empty (hp : IsCompactSystem p) (hC : ∀ i, p (C i))
    (hC_empty : ⋂ i, C i = ∅) :
    Dissipate C (hp.max_of_empty hC hC_empty) = ∅ :=
  (hp C hC hC_empty).choose_spec

theorem iff_of_nempty (p : Set α → Prop) :
    IsCompactSystem p ↔ (∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ (n : ℕ),
      (Dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) := by
  refine ⟨fun h C hC hn ↦ ?_, fun h C hC ↦ ?_⟩ <;> have h2 := not_imp_not.mpr <| h C hC
  · push_neg at h2
    exact h2 hn
  · push_neg at h2
    exact h2

theorem iff_directed (hpi : ∀ (s t : Set α), p s → p t → p (s ∩ t)) :
    (IsCompactSystem p) ↔
    (∀ (C : ℕ → Set α), ∀ (_ : Directed (fun (x1 x2 : Set α) => x1 ⊇ x2) C), (∀ i, p (C i)) →
      ⋂ i, C i = ∅ → ∃ (n : ℕ), C n = ∅) := by
  refine ⟨fun h ↦ fun C hdi hi ↦ ?_, fun h C h1 h2 ↦ ?_⟩
  · rw [dissipate_exists_empty_iff_of_directed C hdi]
    exact h C hi
  · rw [← biInter_le_eq_iInter] at h2
    exact h (Dissipate C) dissipate_directed (dissipate_of_piSystem hpi h1) h2

theorem iff_directed' (hpi : ∀ (s t : Set α), p s → p t → p (s ∩ t)) :
    (IsCompactSystem p) ↔
    ∀ (C : ℕ → Set α), ∀ (_ : Directed (fun (x1 x2 : Set α) => x1 ⊇ x2) C), (∀ i, p (C i)) →
    (∀ (n : ℕ), (C n).Nonempty) → (⋂ i, C i).Nonempty  := by
  rw [IsCompactSystem.iff_directed hpi]
  refine ⟨fun h1 C h3 h4 ↦ ?_, fun h1 C h3 s ↦ ?_⟩ <;> rw [← not_imp_not] <;> push_neg
  · exact h1 C h3 h4
  · exact h1 C h3 s

/-- Any subset of a compact system is a compact system. -/
theorem of_supset {C D : (Set α) → Prop} (hD : IsCompactSystem D) (hCD : ∀ s, C s → D s) :
  IsCompactSystem C := fun s hC hs ↦ hD s (fun i ↦ hCD (s i) (hC i)) hs


section ClosedCompact

variable (α : Type*) [TopologicalSpace α]

/-- The set of sets which are either compact and closed, or `univ`, is a compact system. -/
theorem isClosedCompactOrUnivs :
    IsCompactSystem (fun s : Set α ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ)) := by
  let p := fun (s : Set α) ↦ (IsCompact s ∧ IsClosed s) ∨ (s = univ)
  have h2 : ∀ (s t : Set α), p s → p t → p (s ∩ t) := by
    intro s t hs ht
    by_cases hs' : s = univ
    · rw [hs', univ_inter]
      exact ht
    · by_cases ht' : t = univ
      · rw [ht', inter_comm, univ_inter]
        exact hs
      · exact Or.inl <| ⟨IsCompact.inter_right (Or.resolve_right hs hs').1
        (Or.resolve_right ht ht').2, IsClosed.inter (Or.resolve_right hs hs').2
          (Or.resolve_right ht ht').2⟩
  rw [IsCompactSystem.iff_directed' h2]
  intro s hs h1 h2
  let s' := fun (i : { j : ℕ | s j ≠ univ}) ↦ s i
  have hs' : Directed (fun x1 x2 ↦ x1 ⊇ x2) s' := by
    intro a b
    obtain ⟨z, hz1, hz2⟩ := hs a.val b.val
    have hz : s z ≠ univ := fun h ↦ a.prop <| eq_univ_of_subset hz1 h
    use ⟨z, hz⟩
  have htcl : ∀ (i : { j : ℕ | s j ≠ univ}), IsClosed (s i) :=
    fun i ↦ (Or.resolve_right (h1 i.val) i.prop).2
  have htco : ∀ (i : { j : ℕ | s j ≠ univ}), IsCompact (s i) :=
    fun i ↦ (Or.resolve_right (h1 i.val) i.prop).1
  haveI f : Nonempty α := by
    apply nonempty_of_exists _
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
      · simp only [ne_eq, not_not, s'] at g
        rw [g]
        simp only [Set.mem_univ]
    apply g <| IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed s' hs'
      (fun j ↦ h2 j) htco htcl
  · simp only [ne_eq, coe_setOf, nonempty_subtype, not_exists, not_not, s'] at h
    simp only [nonempty_iInter, s', h]
    simp only [Set.mem_univ, implies_true, exists_const, s']

/-- The set of compact and closed sets is a compact system. -/
theorem isClosedCompacts :
    IsCompactSystem (fun s : Set α ↦ IsCompact s ∧ IsClosed s) :=
  IsCompactSystem.of_supset (isClosedCompactOrUnivs α) (fun _ hs ↦ Or.inl hs)

theorem isCompacts (h : ∀ {s : Set α}, IsCompact s → IsClosed s) :
    IsCompactSystem (fun s : Set α ↦ IsCompact s) := by
  have h : (fun s : Set α ↦ IsCompact s) = (fun s : Set α ↦ IsCompact s ∧ IsClosed s) := by
    ext s
    refine ⟨fun h' ↦ ⟨h', h h'⟩, fun h' ↦ h'.1⟩
  exact h ▸ (isClosedCompacts α)

/-- In a `T2Space` The set of compact sets is a compact system. -/
theorem _of_isCompact_of_T2Space [T2Space α] :
    IsCompactSystem (fun s : Set α ↦ IsCompact s) := (isCompacts α) (fun hs ↦ hs.isClosed)

end ClosedCompact

end IsCompactSystem

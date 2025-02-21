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
  is a compact system.

-/

open Set Finset Nat

section definition

variable {α : Type*} {p : Set α → Prop} {C : ℕ → Set α}

/-- A set of sets is a compact system if, whenever a countable subfamily has empty intersection,
then finitely many of them already have empty intersection. -/
def IsCompactSystem (p : Set α → Prop) : Prop :=
  ∀ C : ℕ → Set α, (∀ i, p (C i)) → ⋂ i, C i = ∅ → ∃ (n : ℕ), Dissipate C n = ∅

/-- In a compact system, given a countable family with empty intersection, we choose a finite
subfamily with empty intersection-/
noncomputable
def IsCompactSystem.max_of_empty (hp : IsCompactSystem p) (hC : ∀ i, p (C i))
    (hC_empty : ⋂ i, C i = ∅) : ℕ :=
  (hp C hC hC_empty).choose

lemma IsCompactSystem.iInter_eq_empty (hp : IsCompactSystem p) (hC : ∀ i, p (C i))
    (hC_empty : ⋂ i, C i = ∅) :
    Dissipate C (hp.max_of_empty hC hC_empty) = ∅ :=
  (hp C hC hC_empty).choose_spec

theorem IsCompactSystem.iff_of_nempty (p : Set α → Prop) :
    IsCompactSystem p ↔ (∀ C : ℕ → Set α, (∀ i, p (C i)) → (∀ (n : ℕ),
      (Dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) := by
  refine ⟨fun h C hC hn ↦ ?_, fun h C hC ↦ ?_⟩ <;> have h2 := not_imp_not.mpr <| h C hC
  · push_neg at h2
    exact h2 hn
  · push_neg at h2
    exact h2

theorem IsCompactSystem.iff_directed (hpi : ∀ (s t : Set α), p s → p t → p (s ∩ t)) :
    (IsCompactSystem p) ↔
    (∀ (C : ℕ → Set α), ∀ (_ : Directed (fun (x1 x2 : Set α) => x1 ⊇ x2) C), (∀ i, p (C i)) →
      ⋂ i, C i = ∅ → ∃ (n : ℕ), C n = ∅) := by
  refine ⟨fun h ↦ fun C hdi hi ↦ ?_, fun h C h1 h2 ↦ ?_⟩
  · rw [dissipate_exists_empty_iff_of_directed C hdi]
    exact h C hi
  · rw [← biInter_le_eq_iInter] at h2
    exact h (Dissipate C) dissipate_directed (dissipate_of_piSystem hpi h1) h2

theorem IsCompactSystem.iff_directed' (hpi : ∀ (s t : Set α), p s → p t → p (s ∩ t)) :
    (IsCompactSystem p) ↔
    ∀ (C : ℕ → Set α), ∀ (_ : Directed (fun (x1 x2 : Set α) => x1 ⊇ x2) C), (∀ i, p (C i)) →
    (∀ (n : ℕ), (C n).Nonempty) → (⋂ i, C i).Nonempty  := by
  rw [IsCompactSystem.iff_directed hpi]
  refine ⟨fun h1 C h3 h4 ↦ ?_, fun h1 C h3 s ↦ ?_⟩ <;> rw [← not_imp_not] <;> push_neg
  · exact h1 C h3 h4
  · exact h1 C h3 s

end definition

section ClosedCompact

/-- The set of compact and closed sets is a compact system. -/
theorem IsClosedCompact.isCompactSystem {α : Type*} [TopologicalSpace α] :
    IsCompactSystem (fun s : Set α ↦ IsCompact s ∧ IsClosed s) := by
  have h : IsPiSystem ({ s : Set α | IsCompact s ∧ IsClosed s}) := by
    intro x hx y hy _
    exact ⟨IsCompact.inter_left hy.1 hx.2, IsClosed.inter hx.2 hy.2 ⟩
  have h1 : ∅ ∈ {s : Set α| IsCompact s ∧ IsClosed s} := by
    exact ⟨isCompact_empty, isClosed_empty⟩
  have h2 : ∀ (s t : Set α), IsCompact s ∧ IsClosed s →
      IsCompact t ∧ IsClosed t → IsCompact (s ∩ t) ∧ IsClosed (s ∩ t) :=
    fun s t h1 h2 ↦ ⟨IsCompact.inter_right h1.1 h2.2, IsClosed.inter h1.2 h2.2⟩
  rw [IsPiSystem.iff_of_empty_mem _ h1] at h
  rw [IsCompactSystem.iff_directed' h2]
  exact fun s hs h1 h2 ↦ IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed s hs h2
    (fun i ↦ (h1 i).1) (fun i ↦ (h1 i).2)

theorem IsCompact.isCompactSystem {α : Type*} [TopologicalSpace α]
    (h : ∀ {s : Set α}, IsCompact s → IsClosed s) :
    IsCompactSystem (fun s : Set α ↦ IsCompact s) := by
  have h : (fun s : Set α ↦ IsCompact s) = (fun s : Set α ↦ IsCompact s ∧ IsClosed s) := by
    ext s
    refine ⟨fun h' ↦ ⟨h', h h'⟩, fun h' ↦ h'.1⟩
  exact h ▸ IsClosedCompact.isCompactSystem

/-- In a `T2Space` The set of compact sets is a compact system. -/
theorem IsCompact.isCompactSystem_of_T2Space {α : Type*} [TopologicalSpace α] [T2Space α] :
    IsCompactSystem (fun s : Set α ↦ IsCompact s) :=
  IsCompact.isCompactSystem fun {_} a ↦ isClosed a

end ClosedCompact
